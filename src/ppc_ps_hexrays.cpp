#include <ida.hpp>
#include <idp.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <bytes.hpp>
#include <funcs.hpp>
#include <hexrays.hpp>
#include <allins.hpp>
#include <typeinf.hpp>
#include <registry.hpp>

// Dummy implementation of uint128 operator<< to satisfy MSVC linker when it instantiates
// unreferenced inline functions like builtin_widget_mask_from_id from kernwin.hpp.
uint128 operator<<(const uint128&, int) { return uint128(); }

namespace
{

constexpr int PS_WIDTH = 8;
constexpr const char *PS_TYPE_NAME = "ppc_ps_t";
constexpr const char *ALWAYS_FIX_ACTION_NAME = "ppc_ps_hexrays:always_fix";
constexpr const char *FIX_FUNCTION_ACTION_NAME = "ppc_ps_hexrays:fix_function";
constexpr const char *REG_SUBKEY = "ppc_ps_hexrays";
constexpr const char *REG_ALWAYS_FIX = "always_fix_paired_singles";

struct function_gate_t
{
  virtual bool should_fix_ea(ea_t ea) const = 0;
};

struct dtype_guard_t
{
  insn_t &insn;
  op_dtype_t old_dtypes[UA_MAXOP];

  explicit dtype_guard_t(insn_t &i) : insn(i)
  {
    for ( int n = 0; n < UA_MAXOP; ++n )
      old_dtypes[n] = insn.ops[n].dtype;
  }

  ~dtype_guard_t()
  {
    for ( int n = 0; n < UA_MAXOP; ++n )
      insn.ops[n].dtype = old_dtypes[n];
  }
};

static bool is_void_op(const op_t &op)
{
  return op.type == o_void;
}

static bool is_imm_value(const op_t &op, uval_t value)
{
  return op.type == o_imm && op.value == value;
}

static bool is_same_reg(const op_t &op, int reg)
{
  return op.type == o_reg && op.reg == reg;
}

static bool is_unquantized_pair_access(const insn_t &insn)
{
  // psq_l/st fD,d(rA),W,I. W=0 and I=0 means two unquantized 32-bit floats,
  // which is exactly an 8-byte stack/global memory transfer for dataflow.
  return is_imm_value(insn.Op3, 0) && is_imm_value(insn.Op4, 0);
}

static bool is_stack_operand(const insn_t &insn, int opnum)
{
  if ( opnum < 0 || opnum >= UA_MAXOP )
    return false;
  return is_stkvar(get_flags(insn.ea), opnum);
}

static bool is_paired_single_itype(uint16 itype);
static const char *ps_helper_name(uint16 itype, int *first_arg, int *max_arg_qty);
static bool is_control_flow_boundary(const insn_t &insn, uint32 feature);

static bool has_canon_mnem(const insn_t &insn, const char *mnem)
{
  const char *canon = insn.get_canon_mnem(PH);
  if ( canon == nullptr || mnem == nullptr )
    return false;

  size_t len = qstrlen(mnem);
  return qstrncmp(canon, mnem, len) == 0
      && (canon[len] == '\0' || canon[len] == '.');
}

static bool is_fsel_mnemonic(const insn_t &insn)
{
  return has_canon_mnem(insn, "fsel");
}

static bool is_ps_sum0_mnemonic(const insn_t &insn)
{
  return has_canon_mnem(insn, "ps_sum0");
}

static bool is_ps_sum1_mnemonic(const insn_t &insn)
{
  return has_canon_mnem(insn, "ps_sum1");
}

static mreg_t load_operand_as_ps(codegen_t &cdg, int opnum)
{
  if ( opnum < 0 || opnum >= UA_MAXOP || is_void_op(cdg.insn.ops[opnum]) )
    return mr_none;

  cdg.insn.ops[opnum].dtype = dt_qword;
  return cdg.load_operand(opnum);
}

static bool store_operand_as_ps(codegen_t &cdg, int opnum, mreg_t value)
{
  if ( value == mr_none || opnum < 0 || opnum >= UA_MAXOP || is_void_op(cdg.insn.ops[opnum]) )
    return false;

  cdg.insn.ops[opnum].dtype = dt_qword;
  mop_t src(value, PS_WIDTH);
  minsn_t *outins = nullptr;
  return cdg.store_operand(opnum, src, 0, &outins);
}

static bool make_ps_type(tinfo_t *out)
{
  if ( out->get_named_type(nullptr, PS_TYPE_NAME, BTF_TYPEDEF)
    && out->get_size() == PS_WIDTH )
  {
    return true;
  }

  if ( parse_decls(nullptr,
                   "typedef struct ppc_ps_t { float ps0; float ps1; } ppc_ps_t;",
                   nullptr,
                   HTI_DCL | HTI_NWR) == 0
    && out->get_named_type(nullptr, PS_TYPE_NAME, BTF_TYPEDEF)
    && out->get_size() == PS_WIDTH )
  {
    return true;
  }

  tinfo_t parsed;
  if ( parse_decl(&parsed, nullptr, nullptr,
                  "struct ppc_ps_t { float ps0; float ps1; };",
                  PT_TYP | PT_SIL)
    && parsed.get_size() == PS_WIDTH )
  {
    if ( parsed.set_named_type(nullptr, PS_TYPE_NAME, NTF_TYPE | NTF_REPLACE | NTF_COPY) == TERR_OK
      && out->get_named_type(nullptr, PS_TYPE_NAME, BTF_STRUCT)
      && out->get_size() == PS_WIDTH )
    {
      return true;
    }

    *out = parsed;
    return true;
  }

  *out = tinfo_t(BTF_UINT64);
  return true;
}

static bool is_wiiu_save_prolog_candidate(uint16 itype)
{
  switch ( itype )
  {
    case PPC_stwu:
    case PPC_stmw:
    case PPC_mflr:
    case PPC_mr:
    case PPC_stw:
    case PPC_stfd:
    case PPC_stfs:
    case PPC_ps_merge10:
      return true;
    default:
      return false;
  }
}

static bool collect_wiiu_save_prolog(qvector<insn_t> *out, ea_t ea)
{
  func_t *fn = get_func(ea);
  if ( fn == nullptr )
    return false;

  ea_t cur = fn->start_ea;
  for ( int nins = 0; nins < 32 && cur < fn->end_ea; ++nins )
  {
    insn_t insn;
    if ( decode_insn(&insn, cur) <= 0 )
      break;
    if ( !is_wiiu_save_prolog_candidate(insn.itype) )
      break;

    out->push_back(insn);
    cur = insn.ea + insn.size;
  }

  return !out->empty();
}

static bool is_displ_stack_store(const insn_t &insn, uint16 itype, int reg)
{
  return insn.itype == itype
      && is_same_reg(insn.Op1, reg)
      && insn.Op2.type == o_displ;
}

static bool same_stack_slot_delta(const op_t &from, const op_t &to, sval_t delta)
{
  return from.type == o_displ
      && to.type == o_displ
      && from.phrase == to.phrase
      && sval_t(to.addr) - sval_t(from.addr) == delta;
}

static bool is_self_merge10(const insn_t &insn)
{
  return insn.itype == PPC_ps_merge10
      && insn.Op1.type == o_reg
      && is_same_reg(insn.Op2, insn.Op1.reg)
      && is_same_reg(insn.Op3, insn.Op1.reg);
}

static bool find_ps_lane_save_pattern(
        const qvector<insn_t> &insns,
        size_t merge_idx,
        ea_t *stfd_ea,
        ea_t *merge_ea,
        ea_t *stfs_ea)
{
  if ( merge_idx >= insns.size() || !is_self_merge10(insns[merge_idx]) )
    return false;

  const int reg = insns[merge_idx].Op1.reg;
  const insn_t *stfd = nullptr;
  for ( int i = int(merge_idx) - 1; i >= 0; --i )
  {
    if ( is_displ_stack_store(insns[i], PPC_stfd, reg) )
    {
      stfd = &insns[i];
      break;
    }
  }
  if ( stfd == nullptr )
    return false;

  const insn_t *stfs = nullptr;
  for ( size_t i = merge_idx + 1; i < insns.size(); ++i )
  {
    if ( is_displ_stack_store(insns[i], PPC_stfs, reg)
      && same_stack_slot_delta(stfd->Op2, insns[i].Op2, 8) )
    {
      stfs = &insns[i];
      break;
    }
  }
  if ( stfs == nullptr )
    return false;

  if ( stfd_ea != nullptr )
    *stfd_ea = stfd->ea;
  if ( merge_ea != nullptr )
    *merge_ea = insns[merge_idx].ea;
  if ( stfs_ea != nullptr )
    *stfs_ea = stfs->ea;
  return true;
}

static bool is_wiiu_ps_lane_save_prolog_insn(const insn_t &insn)
{
  qvector<insn_t> insns;
  if ( !collect_wiiu_save_prolog(&insns, insn.ea) )
    return false;

  for ( size_t i = 0; i < insns.size(); ++i )
  {
    ea_t stfd_ea = BADADDR;
    ea_t merge_ea = BADADDR;
    ea_t stfs_ea = BADADDR;
    if ( find_ps_lane_save_pattern(insns, i, &stfd_ea, &merge_ea, &stfs_ea)
      && (insn.ea == stfd_ea || insn.ea == merge_ea || insn.ea == stfs_ea) )
    {
      return true;
    }
  }

  return false;
}

static bool is_wiiu_lr_save_prolog_insn(const insn_t &insn)
{
  qvector<insn_t> insns;
  if ( !collect_wiiu_save_prolog(&insns, insn.ea) )
    return false;

  for ( size_t i = 0; i < insns.size(); ++i )
  {
    if ( insns[i].itype != PPC_mflr || insns[i].Op1.type != o_reg )
      continue;

    const int reg = insns[i].Op1.reg;
    for ( size_t j = i + 1; j < insns.size(); ++j )
    {
      if ( is_displ_stack_store(insns[j], PPC_stw, reg) )
        return insn.ea == insns[i].ea || insn.ea == insns[j].ea;
    }
  }

  return false;
}

static bool is_wiiu_save_prolog_insn(const insn_t &insn)
{
  return is_wiiu_ps_lane_save_prolog_insn(insn)
      || is_wiiu_lr_save_prolog_insn(insn);
}

static void mark_wiiu_save_prolog_insns(ignore_micro_t *ignore, ea_t func_ea)
{
  qvector<insn_t> insns;
  if ( !collect_wiiu_save_prolog(&insns, func_ea) )
    return;

  for ( size_t i = 0; i < insns.size(); ++i )
  {
    ea_t stfd_ea = BADADDR;
    ea_t merge_ea = BADADDR;
    ea_t stfs_ea = BADADDR;
    if ( find_ps_lane_save_pattern(insns, i, &stfd_ea, &merge_ea, &stfs_ea) )
    {
      ignore->mark_prolog_insn(stfd_ea);
      ignore->mark_prolog_insn(merge_ea);
      ignore->mark_prolog_insn(stfs_ea);
    }
  }

  for ( size_t i = 0; i < insns.size(); ++i )
  {
    if ( insns[i].itype != PPC_mflr || insns[i].Op1.type != o_reg )
      continue;

    const int reg = insns[i].Op1.reg;
    for ( size_t j = i + 1; j < insns.size(); ++j )
    {
      if ( is_displ_stack_store(insns[j], PPC_stw, reg) )
      {
        ignore->mark_prolog_insn(insns[i].ea);
        ignore->mark_prolog_insn(insns[j].ea);
        break;
      }
    }
  }
}

static bool make_u32_type(tinfo_t *out)
{
  *out = tinfo_t(BTF_UINT32);
  return true;
}

static bool make_int_type(tinfo_t *out)
{
  *out = tinfo_t(BTF_INT);
  return true;
}

static tinfo_t get_fp_tinfo(op_dtype_t dtype)
{
  if ( !is_floating_dtype(dtype) )
    dtype = dt_double;

  size_t size = get_dtype_size(dtype);
  if ( size != 4 && size != 8 )
    size = 8;

  return get_float_type(int(size));
}

static bool append_mop_arg(mcallargs_t *args, const mop_t &mop, const tinfo_t &type, const char *name, ea_t ea)
{
  mcallarg_t &arg = args->push_back();
  arg.copy_mop(mop);
  arg.type = type;
  arg.name = name;
  arg.ea = ea;
  return true;
}

static bool append_reg_arg(codegen_t &cdg, mcallargs_t *args, int opnum, const tinfo_t &type, const char *name)
{
  mreg_t mr = load_operand_as_ps(cdg, opnum);
  if ( mr == mr_none )
    return false;

  mop_t mop(mr, PS_WIDTH);
  return append_mop_arg(args, mop, type, name, cdg.insn.ea);
}

static bool append_scalar_fp_arg(
        codegen_t &cdg,
        mcallargs_t *args,
        int opnum,
        op_dtype_t dtype,
        const tinfo_t &type,
        const char *name)
{
  if ( opnum < 0 || opnum >= UA_MAXOP || is_void_op(cdg.insn.ops[opnum]) )
    return false;

  cdg.insn.ops[opnum].dtype = dtype;
  mreg_t mr = cdg.load_operand(opnum);
  if ( mr == mr_none )
    return false;

  mop_t mop(mr, int(get_dtype_size(dtype)));
  return append_mop_arg(args, mop, type, name, cdg.insn.ea);
}

static bool append_fpr_double_arg(
        codegen_t &cdg,
        mcallargs_t *args,
        int opnum,
        const tinfo_t &type,
        const char *name)
{
  if ( opnum < 0 || opnum >= UA_MAXOP || is_void_op(cdg.insn.ops[opnum]) )
    return false;

  cdg.insn.ops[opnum].dtype = dt_double;
  mreg_t mr = cdg.load_operand(opnum);
  if ( mr == mr_none )
    return false;

  mop_t mop(mr, PS_WIDTH);
  return append_mop_arg(args, mop, type, name, cdg.insn.ea);
}

static bool append_imm_arg(mcallargs_t *args, uval_t value, const tinfo_t &type, const char *name, ea_t ea, int opnum)
{
  mcallarg_t &arg = args->push_back();
  arg.make_number(value, inf_get_cc_size_i(), ea, opnum);
  arg.type = type;
  arg.name = name;
  arg.ea = ea;
  return true;
}

static bool append_ea_arg(codegen_t &cdg, mcallargs_t *args, int opnum, const tinfo_t &type, const char *name)
{
  mreg_t mr = cdg.load_effective_address(opnum);
  if ( mr == mr_none )
    return false;

  mop_t mop(mr, inf_get_cc_size_e());
  return append_mop_arg(args, mop, type, name, cdg.insn.ea);
}

static bool append_raw_arg(codegen_t &cdg, mcallargs_t *args, int opnum, const char *name)
{
  if ( opnum < 0 || opnum >= UA_MAXOP || is_void_op(cdg.insn.ops[opnum]) )
    return false;

  tinfo_t int_type;
  tinfo_t u32_type;
  make_int_type(&int_type);
  make_u32_type(&u32_type);

  const op_t &op = cdg.insn.ops[opnum];
  if ( op.type == o_imm )
    return append_imm_arg(args, op.value, int_type, name, cdg.insn.ea, opnum);

  cdg.insn.ops[opnum].dtype = dt_dword;
  mreg_t mr = cdg.load_operand(opnum);
  if ( mr == mr_none )
    return false;

  mop_t mop(mr, inf_get_cc_size_e());
  return append_mop_arg(args, mop, u32_type, name, cdg.insn.ea);
}

static bool make_dest_mop(mop_t *out, const insn_t &insn, int width = PS_WIDTH)
{
  if ( insn.Op1.type != o_reg )
    return false;

  mreg_t mr = reg2mreg(insn.Op1.reg);
  if ( mr == mr_none )
    return false;

  out->make_reg(mr, width);
  return true;
}

static merror_t insert_helper_call(codegen_t &cdg, const char *helper, const tinfo_t *ret_type, const mcallargs_t *args, const mop_t *out)
{
  minsn_t *call = cdg.mba->create_helper_call(cdg.insn.ea, helper, ret_type, args, out);
  if ( call == nullptr )
    return MERR_INSN;

  cdg.mb->insert_into_block(call, cdg.mb->tail);
  return MERR_OK;
}

static merror_t emit_psq_load(codegen_t &cdg)
{
  dtype_guard_t guard(cdg.insn);

  if ( !is_unquantized_pair_access(cdg.insn) || !is_stack_operand(cdg.insn, 1) )
    return MERR_INSN;

  mreg_t loaded = load_operand_as_ps(cdg, 1);
  if ( loaded == mr_none )
    return MERR_INSN;

  return store_operand_as_ps(cdg, 0, loaded) ? MERR_OK : MERR_INSN;
}

static merror_t emit_psq_store(codegen_t &cdg)
{
  dtype_guard_t guard(cdg.insn);

  if ( !is_unquantized_pair_access(cdg.insn) || !is_stack_operand(cdg.insn, 1) )
    return MERR_INSN;

  mreg_t value = load_operand_as_ps(cdg, 0);
  if ( value == mr_none )
    return MERR_INSN;

  return store_operand_as_ps(cdg, 1, value) ? MERR_OK : MERR_INSN;
}

static merror_t emit_ps_helper(codegen_t &cdg, const char *helper, int first_arg_opnum, int max_arg_qty)
{
  dtype_guard_t guard(cdg.insn);

  tinfo_t ps_type;
  make_ps_type(&ps_type);

  mcallargs_t args;
  static const char *arg_names[] = { "a", "b", "c", "d", "e", "f", "g" };
  int added = 0;
  for ( int opnum = first_arg_opnum; opnum < UA_MAXOP && added < max_arg_qty; ++opnum )
  {
    if ( is_void_op(cdg.insn.ops[opnum]) )
      break;
    if ( !append_reg_arg(cdg, &args, opnum, ps_type, arg_names[added]) )
      return MERR_INSN;
    ++added;
  }

  mop_t out;
  if ( !make_dest_mop(&out, cdg.insn) )
    return MERR_INSN;

  return insert_helper_call(cdg, helper, &ps_type, &args, &out);
}

static merror_t emit_ps_scalar_helper(codegen_t &cdg, const char *helper, op_dtype_t dtype, int first_arg_opnum, int max_arg_qty)
{
  dtype_guard_t guard(cdg.insn);

  tinfo_t ps_type;
  make_ps_type(&ps_type);
  tinfo_t fp_type = get_fp_tinfo(dtype);

  mcallargs_t args;
  static const char *arg_names[] = { "a", "b", "c", "d", "e", "f", "g" };
  int added = 0;
  for ( int opnum = first_arg_opnum; opnum < UA_MAXOP && added < max_arg_qty; ++opnum )
  {
    if ( is_void_op(cdg.insn.ops[opnum]) )
      break;
    if ( !append_reg_arg(cdg, &args, opnum, ps_type, arg_names[added]) )
      return MERR_INSN;
    ++added;
  }

  mop_t out;
  if ( !make_dest_mop(&out, cdg.insn, int(get_dtype_size(dtype))) )
    return MERR_INSN;

  return insert_helper_call(cdg, helper, &fp_type, &args, &out);
}

static merror_t emit_ps_compare_helper(codegen_t &cdg, const char *helper)
{
  dtype_guard_t guard(cdg.insn);

  tinfo_t ps_type;
  tinfo_t int_type;
  make_ps_type(&ps_type);
  make_int_type(&int_type);

  mcallargs_t args;
  if ( !append_reg_arg(cdg, &args, 1, ps_type, "a") )
    return MERR_INSN;
  if ( !append_reg_arg(cdg, &args, 2, ps_type, "b") )
    return MERR_INSN;

  mop_t out;
  if ( !make_dest_mop(&out, cdg.insn, inf_get_cc_size_i()) )
    return MERR_INSN;

  return insert_helper_call(cdg, helper, &int_type, &args, &out);
}

static bool operand_refs_reg(const op_t &op, int reg)
{
  return op.type == o_reg && op.reg == reg;
}

static bool is_control_flow_boundary(const insn_t &insn, uint32 feature)
{
  if ( (feature & (CF_STOP | CF_CALL | CF_JUMP)) != 0 )
    return true;

  switch ( insn.itype )
  {
    case PPC_b:
    case PPC_bc:
    case PPC_bcctr:
    case PPC_bclr:
      return true;
    default:
      return false;
  }
}

static bool should_scalarize_ps_result(const insn_t &insn, op_dtype_t *out_dtype)
{
  if ( insn.Op1.type != o_reg )
    return false;

  func_t *fn = get_func(insn.ea);
  if ( fn == nullptr )
    return false;

  const int dest_reg = insn.Op1.reg;
  ea_t ea = insn.ea + insn.size;
  bool saw_scalar_use = false;
  *out_dtype = dt_float;

  for ( int nins = 0; nins < 64 && ea < fn->end_ea; ++nins )
  {
    insn_t use_insn;
    if ( decode_insn(&use_insn, ea) <= 0 )
      break;

    uint32 feature = use_insn.get_canon_feature(PH);
    bool uses_dest = false;
    bool changes_dest = false;
    for ( int opnum = 0; opnum < UA_MAXOP; ++opnum )
    {
      if ( !operand_refs_reg(use_insn.ops[opnum], dest_reg) )
        continue;
      uses_dest |= has_cf_use(feature, opnum);
      changes_dest |= has_cf_chg(feature, opnum);
    }

    if ( uses_dest )
    {
      if ( is_paired_single_itype(use_insn.itype) )
        return false;

      for ( int opnum = 0; opnum < UA_MAXOP; ++opnum )
      {
        if ( operand_refs_reg(use_insn.ops[opnum], dest_reg)
          && has_cf_use(feature, opnum)
          && is_floating_dtype(use_insn.ops[opnum].dtype) )
        {
          *out_dtype = use_insn.ops[opnum].dtype;
          break;
        }
      }
      saw_scalar_use = true;
    }

    if ( changes_dest )
      return saw_scalar_use;
    if ( is_control_flow_boundary(use_insn, feature) )
      return false;

    ea = use_insn.ea + use_insn.size;
  }

  return saw_scalar_use;
}

static merror_t emit_fsel_helper(codegen_t &cdg)
{
  dtype_guard_t guard(cdg.insn);

  tinfo_t fp_type = get_fp_tinfo(dt_double);

  mcallargs_t args;
  if ( !append_fpr_double_arg(cdg, &args, 1, fp_type, "test") )
    return MERR_INSN;
  if ( !append_fpr_double_arg(cdg, &args, 2, fp_type, "ge_zero") )
    return MERR_INSN;
  if ( !append_fpr_double_arg(cdg, &args, 3, fp_type, "lt_zero") )
    return MERR_INSN;

  mop_t out;
  if ( !make_dest_mop(&out, cdg.insn, PS_WIDTH) )
    return MERR_INSN;

  return insert_helper_call(cdg, "__ppc_fsel", &fp_type, &args, &out);
}

static merror_t emit_psq_helper(codegen_t &cdg, const char *helper, bool is_store)
{
  dtype_guard_t guard(cdg.insn);

  tinfo_t ps_type;
  tinfo_t u32_type;
  tinfo_t int_type;
  make_ps_type(&ps_type);
  make_u32_type(&u32_type);
  make_int_type(&int_type);

  mcallargs_t args;
  if ( is_store && !append_reg_arg(cdg, &args, 0, ps_type, "value") )
    return MERR_INSN;
  if ( append_ea_arg(cdg, &args, 1, u32_type, "ea") )
  {
    if ( cdg.insn.Op3.type == o_imm )
      append_imm_arg(&args, cdg.insn.Op3.value, int_type, "w", cdg.insn.ea, 2);
    if ( cdg.insn.Op4.type == o_imm )
      append_imm_arg(&args, cdg.insn.Op4.value, int_type, "i", cdg.insn.ea, 3);
  }
  else
  {
    static const char *raw_names[] = { "op1", "op2", "op3", "op4", "op5", "op6", "op7" };
    int raw_idx = 0;
    for ( int opnum = 1; opnum < UA_MAXOP && !is_void_op(cdg.insn.ops[opnum]); ++opnum )
    {
      if ( !append_raw_arg(cdg, &args, opnum, raw_names[raw_idx++]) )
        return MERR_INSN;
    }
  }

  if ( is_store )
    return insert_helper_call(cdg, helper, nullptr, &args, nullptr);

  mop_t out;
  if ( !make_dest_mop(&out, cdg.insn) )
    return MERR_INSN;
  return insert_helper_call(cdg, helper, &ps_type, &args, &out);
}

static bool is_psq_itype(uint16 itype)
{
  switch ( itype )
  {
    case PPC_psq_l:
    case PPC_psq_lu:
    case PPC_psq_lx:
    case PPC_psq_lux:
    case PPC_psq_st:
    case PPC_psq_stu:
    case PPC_psq_stx:
    case PPC_psq_stux:
      return true;
    default:
      return false;
  }
}

static bool is_paired_single_itype(uint16 itype)
{
  int first_arg = 0;
  int max_arg_qty = 0;
  return is_psq_itype(itype) || ps_helper_name(itype, &first_arg, &max_arg_qty) != nullptr;
}

static const char *ps_helper_name(uint16 itype, int *first_arg, int *max_arg_qty)
{
  *first_arg = 1;
  *max_arg_qty = UA_MAXOP - 1;

  switch ( itype )
  {
    case PPC_ps_add:     *max_arg_qty = 2; return "__ppc_ps_add";
    case PPC_ps_sub:     *max_arg_qty = 2; return "__ppc_ps_sub";
    case PPC_ps_mul:     *max_arg_qty = 2; return "__ppc_ps_mul";
    case PPC_ps_div:     *max_arg_qty = 2; return "__ppc_ps_div";
    case PPC_ps_muls0:   *max_arg_qty = 2; return "__ppc_ps_muls0";
    case PPC_ps_muls1:   *max_arg_qty = 2; return "__ppc_ps_muls1";
    case PPC_ps_madd:    *max_arg_qty = 3; return "__ppc_ps_madd";
    case PPC_ps_msub:    *max_arg_qty = 3; return "__ppc_ps_msub";
    case PPC_ps_nmadd:   *max_arg_qty = 3; return "__ppc_ps_nmadd";
    case PPC_ps_nmsub:   *max_arg_qty = 3; return "__ppc_ps_nmsub";
    case PPC_ps_madds0:  *max_arg_qty = 3; return "__ppc_ps_madds0";
    case PPC_ps_madds1:  *max_arg_qty = 3; return "__ppc_ps_madds1";
    case PPC_ps_neg:     *max_arg_qty = 1; return "__ppc_ps_neg";
    case PPC_ps_abs:     *max_arg_qty = 1; return "__ppc_ps_abs";
    case PPC_ps_nabs:    *max_arg_qty = 1; return "__ppc_ps_nabs";
    case PPC_ps_mr:      *max_arg_qty = 1; return "__ppc_ps_mr";
    case PPC_ps_merge00: *max_arg_qty = 2; return "__ppc_ps_merge00";
    case PPC_ps_merge01: *max_arg_qty = 2; return "__ppc_ps_merge01";
    case PPC_ps_merge10: *max_arg_qty = 2; return "__ppc_ps_merge10";
    case PPC_ps_merge11: *max_arg_qty = 2; return "__ppc_ps_merge11";
    case PPC_ps_res:     *max_arg_qty = 1; return "__ppc_ps_res";
    case PPC_ps_rsqrte:  *max_arg_qty = 1; return "__ppc_ps_rsqrte";
    case PPC_ps_sel:     *max_arg_qty = 3; return "__ppc_ps_sel";
    case PPC_ps_sum0:    *max_arg_qty = 3; return "__ppc_ps_sum0";
    case PPC_ps_sum1:    *max_arg_qty = 3; return "__ppc_ps_sum1";
    case PPC_ps_cmpu0:   *max_arg_qty = 2; return "__ppc_ps_cmpu0";
    case PPC_ps_cmpu1:   *max_arg_qty = 2; return "__ppc_ps_cmpu1";
    case PPC_ps_cmpo0:   *max_arg_qty = 2; return "__ppc_ps_cmpo0";
    case PPC_ps_cmpo1:   *max_arg_qty = 2; return "__ppc_ps_cmpo1";
    default: return nullptr;
  }
}

static const cexpr_t *skip_casts(const cexpr_t *e)
{
  while ( e != nullptr && e->op == cot_cast )
    e = e->x;
  return e;
}

static bool is_zero_expr(const cexpr_t *e)
{
  e = skip_casts(e);
  return e != nullptr && e->is_zero_const();
}

static cexpr_t *clone_expr(const cexpr_t *e)
{
  return e != nullptr ? new cexpr_t(*e) : nullptr;
}

static const cexpr_t *match_helper_call(const cexpr_t *e, const char *helper)
{
  e = skip_casts(e);
  if ( e == nullptr || e->op != cot_call || e->x == nullptr )
    return nullptr;

  const cexpr_t *callee = skip_casts(e->x);
  if ( callee == nullptr || callee->op != cot_helper || callee->helper == nullptr )
    return nullptr;

  return strcmp(callee->helper, helper) == 0 ? e : nullptr;
}

static const cexpr_t *extract_ref_target(const cexpr_t *e)
{
  e = skip_casts(e);
  if ( e == nullptr || e->op != cot_ref || e->x == nullptr )
    return nullptr;

  const cexpr_t *target = skip_casts(e->x);
  if ( target == nullptr || target->has_side_effects() )
    return nullptr;
  return target;
}

static const cexpr_t *extract_address_base(const cexpr_t *e)
{
  if ( const cexpr_t *target = extract_ref_target(e) )
    return target;

  e = skip_casts(e);
  if ( e == nullptr || !e->type.is_ptr() || e->has_side_effects() )
    return nullptr;
  return e;
}

static bool collect_float_member_path(qvector<udm_t> *path, const tinfo_t &type, uint32 byte_off)
{
  if ( type.is_float() )
    return byte_off == 0;

  if ( !type.is_udt() )
    return false;

  udt_type_data_t udt;
  if ( !type.get_udt_details(&udt) )
    return false;

  udm_t member;
  if ( udt.get_best_fit_member(&member, byte_off) < 0
    || member.is_gap()
    || member.offset % 8 != 0 )
  {
    return false;
  }

  const uint32 member_off = uint32(member.offset / 8);
  const size_t member_size = member.type.get_size();
  if ( member_size == BADSIZE
    || byte_off < member_off
    || byte_off >= member_off + member_size )
  {
    return false;
  }

  path->push_back(member);
  return collect_float_member_path(path, member.type, byte_off - member_off);
}

static cexpr_t *build_float_expr_from_object(const cexpr_t *obj, uint32 byte_off)
{
  if ( obj == nullptr )
    return nullptr;

  if ( obj->type.is_float() )
    return byte_off == 0 ? clone_expr(obj) : nullptr;

  qvector<udm_t> path;
  if ( !collect_float_member_path(&path, obj->type, byte_off) || path.empty() )
    return nullptr;

  cexpr_t *expr = clone_expr(obj);
  for ( const udm_t &member : path )
  {
    cexpr_t *next = new cexpr_t(cot_memref, expr);
    next->m = uint32(member.offset / 8);
    next->type = member.type;
    next->ea = obj->ea;
    expr = next;
  }
  return expr->type.is_float() ? expr : nullptr;
}

static cexpr_t *build_float_expr_from_pointer(const cexpr_t *ptr, const tinfo_t &type, uint32 byte_off)
{
  if ( ptr == nullptr )
    return nullptr;

  if ( type.is_float() )
  {
    if ( byte_off != 0 )
      return nullptr;

    cexpr_t *expr = new cexpr_t(cot_ptr, clone_expr(ptr));
    expr->ptrsize = 4;
    expr->type = type;
    expr->ea = ptr->ea;
    return expr;
  }

  qvector<udm_t> path;
  if ( !collect_float_member_path(&path, type, byte_off) || path.empty() )
    return nullptr;

  cexpr_t *expr = new cexpr_t(cot_memptr, clone_expr(ptr));
  expr->m = uint32(path[0].offset / 8);
  expr->ptrsize = int(path[0].type.get_size());
  expr->type = path[0].type;
  expr->ea = ptr->ea;

  for ( size_t i = 1; i < path.size(); ++i )
  {
    cexpr_t *next = new cexpr_t(cot_memref, expr);
    next->m = uint32(path[i].offset / 8);
    next->type = path[i].type;
    next->ea = ptr->ea;
    expr = next;
  }
  return expr->type.is_float() ? expr : nullptr;
}

static cexpr_t *build_float_expr_at_address(const cexpr_t *base, uint32 byte_off)
{
  base = skip_casts(base);
  if ( base == nullptr )
    return nullptr;

  switch ( base->op )
  {
    case cot_memref:
      return build_float_expr_from_object(base->x, base->m + byte_off);
    case cot_memptr:
      return build_float_expr_from_pointer(base->x, remove_pointer(base->x->type), base->m + byte_off);
    case cot_ptr:
      return build_float_expr_from_pointer(base->x, remove_pointer(base->x->type), byte_off);
    default:
      if ( base->type.is_ptr() )
        return build_float_expr_from_pointer(base, remove_pointer(base->type), byte_off);
      if ( base->type.is_float() )
        return byte_off == 0 ? clone_expr(base) : nullptr;
      return build_float_expr_from_object(base, byte_off);
  }
}

static const cexpr_t *extract_pair_store_base(const cexpr_t *lhs)
{
  lhs = skip_casts(lhs);
  if ( lhs == nullptr || lhs->type.get_size() != PS_WIDTH )
    return nullptr;
  if ( lhs->op == cot_ptr )
    return extract_ref_target(lhs->x);
  return is_lvalue(lhs->op) && !lhs->has_side_effects() ? lhs : nullptr;
}

static const cexpr_t *extract_psq_load_base(const cexpr_t *expr)
{
  expr = match_helper_call(expr, "__ppc_psq_l");
  if ( expr == nullptr || expr->a == nullptr || expr->a->size() < 3 )
    return nullptr;

  if ( !is_zero_expr(&(*expr->a)[1]) || !is_zero_expr(&(*expr->a)[2]) )
    return nullptr;

  return extract_address_base(&(*expr->a)[0]);
}

static cexpr_t *build_float_expr_from_ea_value(const cexpr_t *ea_expr, uint32 byte_off)
{
  ea_expr = skip_casts(ea_expr);
  if ( ea_expr == nullptr || ea_expr->has_side_effects() )
    return nullptr;

  tinfo_t ps_type;
  make_ps_type(&ps_type);
  tinfo_t ps_ptr_type;
  if ( !ps_ptr_type.create_ptr(ps_type) )
    return nullptr;

  cexpr_t *cast = new cexpr_t(cot_cast, clone_expr(ea_expr));
  cast->type = ps_ptr_type;
  cast->ea = ea_expr->ea;

  cexpr_t *lane = build_float_expr_from_pointer(cast, ps_type, byte_off);
  delete cast;
  return lane;
}

static cexpr_t *build_psq_load_lane_expr(const cexpr_t *expr, int lane)
{
  expr = match_helper_call(expr, "__ppc_psq_l");
  if ( expr == nullptr || expr->a == nullptr || expr->a->size() < 3 )
    return nullptr;

  if ( !is_zero_expr(&(*expr->a)[1]) || !is_zero_expr(&(*expr->a)[2]) )
    return nullptr;

  const uint32 byte_off = uint32(lane * 4);
  const cexpr_t *ea_arg = &(*expr->a)[0];
  if ( const cexpr_t *base = extract_address_base(ea_arg) )
    return build_float_expr_at_address(base, byte_off);
  return build_float_expr_from_ea_value(ea_arg, byte_off);
}

static cexpr_t *make_float_binary_expr(ctype_t op, cexpr_t *lhs, cexpr_t *rhs, ea_t ea)
{
  cexpr_t *expr = new cexpr_t(op, lhs, rhs);
  expr->ea = ea;
  expr->type = lhs->type;
  expr->exflags |= EXFL_FPOP;
  return expr;
}

static cexpr_t *make_float_unary_expr(ctype_t op, cexpr_t *arg, ea_t ea)
{
  cexpr_t *expr = new cexpr_t(op, arg);
  expr->ea = ea;
  expr->type = arg->type;
  expr->exflags |= EXFL_FPOP;
  return expr;
}

static cexpr_t *make_float_assign(cexpr_t *dst, cexpr_t *value, ea_t ea)
{
  value->type = dst->type;
  cexpr_t *asg = new cexpr_t(cot_asg, dst, value);
  asg->ea = ea;
  asg->type = dst->type;
  asg->calc_type(true);
  return asg;
}

static cexpr_t *build_ps_lane_expr(const cexpr_t *expr, int lane);

static bool build_ps_arg_lanes(cexpr_t **lane0, cexpr_t **lane1, const cexpr_t *expr)
{
  *lane0 = build_ps_lane_expr(expr, 0);
  *lane1 = build_ps_lane_expr(expr, 1);
  if ( *lane0 != nullptr && *lane1 != nullptr )
    return true;

  delete *lane0;
  delete *lane1;
  *lane0 = nullptr;
  *lane1 = nullptr;
  return false;
}

static cexpr_t *build_ps_lane_expr(const cexpr_t *expr, int lane)
{
  if ( lane < 0 || lane > 1 )
    return nullptr;

  if ( cexpr_t *psq_lane = build_psq_load_lane_expr(expr, lane) )
    return psq_lane;

  expr = skip_casts(expr);
  if ( expr == nullptr )
    return nullptr;

  if ( is_lvalue(expr->op) && expr->type.get_size() == PS_WIDTH && !expr->has_side_effects() )
    return build_float_expr_at_address(expr, uint32(lane * 4));

  if ( expr->op != cot_call || expr->a == nullptr )
    return nullptr;

  const cexpr_t *callee = skip_casts(expr->x);
  if ( callee == nullptr || callee->op != cot_helper || callee->helper == nullptr )
    return nullptr;

  const char *helper = callee->helper;
  const size_t nargs = expr->a->size();
  auto arg_lane = [&](size_t arg, int arg_lane_num) -> cexpr_t *
  {
    if ( arg >= nargs )
      return nullptr;
    return build_ps_lane_expr(&(*expr->a)[arg], arg_lane_num);
  };
  auto binary = [&](ctype_t op) -> cexpr_t *
  {
    if ( nargs != 2 )
      return nullptr;
    cexpr_t *lhs = arg_lane(0, lane);
    cexpr_t *rhs = arg_lane(1, lane);
    if ( lhs == nullptr || rhs == nullptr )
    {
      delete lhs;
      delete rhs;
      return nullptr;
    }
    return make_float_binary_expr(op, lhs, rhs, expr->ea);
  };
  if ( strcmp(helper, "__ppc_ps_add") == 0 )
    return binary(cot_fadd);
  if ( strcmp(helper, "__ppc_ps_sub") == 0 )
    return binary(cot_fsub);
  if ( strcmp(helper, "__ppc_ps_mul") == 0 )
    return binary(cot_fmul);
  if ( strcmp(helper, "__ppc_ps_div") == 0 )
    return binary(cot_fdiv);

  if ( strcmp(helper, "__ppc_ps_mr") == 0 && nargs == 1 )
    return arg_lane(0, lane);
  if ( strcmp(helper, "__ppc_ps_neg") == 0 && nargs == 1 )
  {
    cexpr_t *arg = arg_lane(0, lane);
    return arg != nullptr ? make_float_unary_expr(cot_fneg, arg, expr->ea) : nullptr;
  }

  if ( strcmp(helper, "__ppc_ps_muls0") == 0 && nargs == 2 )
  {
    cexpr_t *lhs = arg_lane(0, lane);
    cexpr_t *rhs = arg_lane(1, 0);
    if ( lhs == nullptr || rhs == nullptr )
    {
      delete lhs;
      delete rhs;
      return nullptr;
    }
    return make_float_binary_expr(cot_fmul, lhs, rhs, expr->ea);
  }
  if ( strcmp(helper, "__ppc_ps_muls1") == 0 && nargs == 2 )
  {
    cexpr_t *lhs = arg_lane(0, lane);
    cexpr_t *rhs = arg_lane(1, 1);
    if ( lhs == nullptr || rhs == nullptr )
    {
      delete lhs;
      delete rhs;
      return nullptr;
    }
    return make_float_binary_expr(cot_fmul, lhs, rhs, expr->ea);
  }

  if ( strcmp(helper, "__ppc_ps_merge00") == 0 && nargs == 2 )
    return arg_lane(lane, 0);
  if ( strcmp(helper, "__ppc_ps_merge01") == 0 && nargs == 2 )
    return lane == 0 ? arg_lane(0, 0) : arg_lane(1, 1);
  if ( strcmp(helper, "__ppc_ps_merge10") == 0 && nargs == 2 )
    return lane == 0 ? arg_lane(0, 1) : arg_lane(1, 0);
  if ( strcmp(helper, "__ppc_ps_merge11") == 0 && nargs == 2 )
    return arg_lane(lane, 1);

  return nullptr;
}

static cexpr_t *build_ps_lane_rewrite(const cexpr_t *dst_base, const cexpr_t *rhs, ea_t ea)
{
  cexpr_t *dst0 = build_float_expr_at_address(dst_base, 0);
  cexpr_t *dst1 = build_float_expr_at_address(dst_base, 4);
  cexpr_t *value0 = nullptr;
  cexpr_t *value1 = nullptr;
  if ( dst0 == nullptr || dst1 == nullptr || !build_ps_arg_lanes(&value0, &value1, rhs) )
  {
    delete dst0;
    delete dst1;
    return nullptr;
  }

  cexpr_t *asg0 = make_float_assign(dst0, value0, ea);
  cexpr_t *asg1 = make_float_assign(dst1, value1, ea);
  cexpr_t *comma = new cexpr_t(cot_comma, asg0, asg1);
  comma->ea = ea;
  comma->calc_type(true);
  return comma;
}

static void rewrite_ps_pair_assignments(cfunc_t *cfunc)
{
  struct ida_local ps_pair_rewriter_t : public ctree_visitor_t
  {
    ps_pair_rewriter_t() : ctree_visitor_t(CV_FAST | CV_INSNS) {}

    int idaapi visit_insn(cinsn_t *ins) override
    {
      if ( ins->op != cit_expr || ins->cexpr == nullptr )
        return 0;

      cexpr_t *expr = ins->cexpr;
      if ( expr->op != cot_asg || expr->x == nullptr || expr->y == nullptr )
        return 0;

      const cexpr_t *dst_base = extract_pair_store_base(expr->x);
      if ( dst_base == nullptr )
        return 0;

      cexpr_t *replacement = build_ps_lane_rewrite(dst_base, expr->y, expr->ea);
      if ( replacement == nullptr )
        return 0;

      expr->replace_by(replacement);
      return 0;
    }
  };

  ps_pair_rewriter_t rewriter;
  rewriter.apply_to(&cfunc->body, nullptr);
}

struct ppc_ps_filter_t : public microcode_filter_t
{
  const function_gate_t *gate = nullptr;

  bool match(codegen_t &cdg) override
  {
    if ( gate != nullptr && !gate->should_fix_ea(cdg.insn.ea) )
      return false;

    int first_arg = 0;
    int max_arg_qty = 0;
    return is_wiiu_save_prolog_insn(cdg.insn)
        || cdg.insn.itype == PPC_fsel
        || is_fsel_mnemonic(cdg.insn)
        || is_ps_sum0_mnemonic(cdg.insn)
        || is_ps_sum1_mnemonic(cdg.insn)
        || is_psq_itype(cdg.insn.itype)
        || ps_helper_name(cdg.insn.itype, &first_arg, &max_arg_qty) != nullptr;
  }

  merror_t apply(codegen_t &cdg) override
  {
    if ( is_wiiu_save_prolog_insn(cdg.insn) )
      return MERR_OK;

    if ( cdg.insn.itype == PPC_fsel || is_fsel_mnemonic(cdg.insn) )
      return emit_fsel_helper(cdg);

    if ( cdg.insn.itype == PPC_ps_sum0 || is_ps_sum0_mnemonic(cdg.insn) )
    {
      op_dtype_t dtype = dt_float;
      if ( should_scalarize_ps_result(cdg.insn, &dtype) )
      {
        if ( emit_ps_scalar_helper(cdg, "__ppc_ps_sum0_scalar", dtype, 1, 3) == MERR_OK )
          return MERR_OK;
      }
      return emit_ps_helper(cdg, "__ppc_ps_sum0", 1, 3);
    }

    if ( cdg.insn.itype == PPC_ps_sum1 || is_ps_sum1_mnemonic(cdg.insn) )
    {
      op_dtype_t dtype = dt_float;
      if ( should_scalarize_ps_result(cdg.insn, &dtype) )
      {
        if ( emit_ps_scalar_helper(cdg, "__ppc_ps_sum1_scalar", dtype, 1, 3) == MERR_OK )
          return MERR_OK;
      }
      return emit_ps_helper(cdg, "__ppc_ps_sum1", 1, 3);
    }

    switch ( cdg.insn.itype )
    {
      case PPC_psq_l:
        if ( emit_psq_load(cdg) == MERR_OK )
          return MERR_OK;
        return emit_psq_helper(cdg, "__ppc_psq_l", false);

      case PPC_psq_st:
        if ( emit_psq_store(cdg) == MERR_OK )
          return MERR_OK;
        return emit_psq_helper(cdg, "__ppc_psq_st", true);

      case PPC_psq_lu:  return emit_psq_helper(cdg, "__ppc_psq_lu", false);
      case PPC_psq_lx:  return emit_psq_helper(cdg, "__ppc_psq_lx", false);
      case PPC_psq_lux: return emit_psq_helper(cdg, "__ppc_psq_lux", false);
      case PPC_psq_stu: return emit_psq_helper(cdg, "__ppc_psq_stu", true);
      case PPC_psq_stx: return emit_psq_helper(cdg, "__ppc_psq_stx", true);
      case PPC_psq_stux:return emit_psq_helper(cdg, "__ppc_psq_stux", true);

      case PPC_ps_cmpu0: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpu0");
      case PPC_ps_cmpu1: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpu1");
      case PPC_ps_cmpo0: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpo0");
      case PPC_ps_cmpo1: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpo1");

      case PPC_ps_sub:
        return emit_ps_helper(cdg, "__ppc_ps_sub", 1, 2);

      default:
        int first_arg = 1;
        int max_arg_qty = 0;
        if ( const char *helper = ps_helper_name(cdg.insn.itype, &first_arg, &max_arg_qty) )
          return emit_ps_helper(cdg, helper, first_arg, max_arg_qty);
        return MERR_INSN;
    }
  }
};

struct plugin_ctx_t;

struct always_fix_ah_t : public action_handler_t
{
  plugin_ctx_t *ctx = nullptr;

  int idaapi activate(action_activation_ctx_t *actx) override;
  action_state_t idaapi update(action_update_ctx_t *uctx) override;
};

struct fix_function_ah_t : public action_handler_t
{
  plugin_ctx_t *ctx = nullptr;

  int idaapi activate(action_activation_ctx_t *actx) override;
  action_state_t idaapi update(action_update_ctx_t *uctx) override;
};

struct plugin_ctx_t : public plugmod_t, public event_listener_t, public ignore_micro_t, public function_gate_t
{
  ppc_ps_filter_t filter;
  always_fix_ah_t always_fix_ah;
  fix_function_ah_t fix_function_ah;
  qvector<ea_t> session_fixed_functions;
  bool always_fix = false;

  static ea_t function_start_for_ea(ea_t ea)
  {
    func_t *func = get_func(ea);
    return func != nullptr ? func->start_ea : BADADDR;
  }

  bool is_session_fixed(ea_t func_ea) const
  {
    for ( ea_t ea : session_fixed_functions )
      if ( ea == func_ea )
        return true;
    return false;
  }

  bool should_fix_function(ea_t func_ea) const
  {
    return func_ea != BADADDR && (always_fix || is_session_fixed(func_ea));
  }

  bool should_fix_ea(ea_t ea) const override
  {
    return should_fix_function(function_start_for_ea(ea));
  }

  void add_session_fixed_function(ea_t func_ea)
  {
    if ( func_ea != BADADDR && !is_session_fixed(func_ea) )
      session_fixed_functions.push_back(func_ea);
  }

  void refresh_function(vdui_t *vu, ea_t func_ea)
  {
    if ( func_ea == BADADDR )
      return;
    mark_cfunc_dirty(func_ea, true);
    if ( vu != nullptr )
      vu->refresh_view(true);
    else
      mark_builtin_widgets(IWID_PSEUDOCODE);
  }

  void set_always_fix(bool enabled, vdui_t *vu=nullptr)
  {
    always_fix = enabled;
    reg_write_bool(REG_ALWAYS_FIX, enabled, REG_SUBKEY);
    update_action_checked(ALWAYS_FIX_ACTION_NAME, enabled);

    ea_t func_ea = BADADDR;
    if ( vu != nullptr && vu->cfunc != nullptr )
      func_ea = vu->cfunc->entry_ea;
    else
      func_ea = function_start_for_ea(get_screen_ea());
    refresh_function(vu, func_ea);
  }

  bool fix_current_pseudocode_function(vdui_t *vu)
  {
    if ( vu == nullptr || vu->cfunc == nullptr )
    {
      warning("ppc_ps_hexrays: use this from a pseudocode function");
      return false;
    }

    ea_t func_ea = vu->cfunc->entry_ea;
    add_session_fixed_function(func_ea);
    refresh_function(vu, func_ea);
    msg("ppc_ps_hexrays: enabled paired-single fixes for %a this session\n", func_ea);
    return true;
  }

  static ssize_t idaapi hr_callback(void *ud, hexrays_event_t event, va_list va)
  {
    plugin_ctx_t *ctx = static_cast<plugin_ctx_t *>(ud);
    if ( ctx == nullptr )
      return 0;

    if ( event == hxe_maturity )
    {
      cfunc_t *cfunc = va_arg(va, cfunc_t *);
      ctree_maturity_t mat = va_argi(va, ctree_maturity_t);
      if ( mat == CMAT_FINAL && ctx->should_fix_function(cfunc->entry_ea) )
        rewrite_ps_pair_assignments(cfunc);
    }
    else if ( event == hxe_populating_popup )
    {
      TWidget *widget = va_arg(va, TWidget *);
      TPopupMenu *popup_handle = va_arg(va, TPopupMenu *);
      vdui_t *vu = va_arg(va, vdui_t *);
      if ( vu != nullptr )
      {
        attach_action_to_popup(widget, popup_handle, ALWAYS_FIX_ACTION_NAME, nullptr, SETMENU_APP);
        attach_action_to_popup(widget, popup_handle, FIX_FUNCTION_ACTION_NAME, nullptr, SETMENU_APP);
      }
    }
    return 0;
  }

  plugin_ctx_t()
  {
    always_fix = reg_read_bool(REG_ALWAYS_FIX, false, REG_SUBKEY);
    filter.gate = this;
    always_fix_ah.ctx = this;
    fix_function_ah.ctx = this;

    init_ignore_micro();
    hook_event_listener(HT_IDP, this);
    install_hexrays_callback(hr_callback, this);
    install_microcode_filter(&filter, true);
    register_action(ACTION_DESC_LITERAL_OWNER(
                            ALWAYS_FIX_ACTION_NAME,
                            "Always Fix Paired Singles In Functions",
                            &always_fix_ah,
                            this,
                            nullptr,
                            "Automatically apply paired-single fixes to all decompiled functions",
                            -1,
                            ADF_OT_PLUGMOD | ADF_CHECKABLE));
    update_action_checked(ALWAYS_FIX_ACTION_NAME, always_fix);
    register_action(ACTION_DESC_LITERAL_PLUGMOD(
                            FIX_FUNCTION_ACTION_NAME,
                            "Fix Paired Single Instructions",
                            &fix_function_ah,
                            this,
                            nullptr,
                            "Apply paired-single fixes to this function for the current session",
                            -1));
    msg("ppc_ps_hexrays: installed optional PowerPC paired-single Hex-Rays filter%s\n",
        always_fix ? " (automatic fixes enabled)" : "");
  }

  ~plugin_ctx_t() override
  {
    unregister_action(FIX_FUNCTION_ACTION_NAME);
    unregister_action(ALWAYS_FIX_ACTION_NAME);
    remove_hexrays_callback(hr_callback, this);
    unhook_event_listener(HT_IDP, this);
    install_microcode_filter(&filter, false);
    term_ignore_micro();
    term_hexrays_plugin();
  }

  ssize_t idaapi on_event(ssize_t code, va_list va) override
  {
    if ( code == processor_t::ev_analyze_prolog )
    {
      ea_t func_ea = va_arg(va, ea_t);
      if ( should_fix_function(func_ea) )
        mark_wiiu_save_prolog_insns(this, func_ea);
    }
    return 0;
  }

  bool idaapi run(size_t) override
  {
    msg("ppc_ps_hexrays: active\n");
    return true;
  }
};

int idaapi always_fix_ah_t::activate(action_activation_ctx_t *actx)
{
  if ( ctx == nullptr )
    return 0;

  vdui_t *vu = actx != nullptr ? get_widget_vdui(actx->widget) : nullptr;
  ctx->set_always_fix(!ctx->always_fix, vu);
  msg("ppc_ps_hexrays: automatic paired-single fixes %s\n", ctx->always_fix ? "enabled" : "disabled");
  return 1;
}

action_state_t idaapi always_fix_ah_t::update(action_update_ctx_t *uctx)
{
  if ( ctx == nullptr || uctx == nullptr || uctx->widget_type != BWN_PSEUDOCODE )
    return AST_DISABLE_FOR_WIDGET;

  update_action_checked(ALWAYS_FIX_ACTION_NAME, ctx->always_fix);
  return AST_ENABLE_FOR_WIDGET;
}

int idaapi fix_function_ah_t::activate(action_activation_ctx_t *actx)
{
  if ( ctx == nullptr || actx == nullptr )
    return 0;

  return ctx->fix_current_pseudocode_function(get_widget_vdui(actx->widget)) ? 1 : 0;
}

action_state_t idaapi fix_function_ah_t::update(action_update_ctx_t *uctx)
{
  if ( ctx == nullptr || uctx == nullptr || uctx->widget_type != BWN_PSEUDOCODE )
    return AST_DISABLE_FOR_WIDGET;
  return AST_ENABLE_FOR_WIDGET;
}

} // namespace

static plugmod_t *idaapi init()
{
  if ( PH.id != PLFM_PPC )
    return nullptr;
  if ( !init_hexrays_plugin() )
    return nullptr;
  return new plugin_ctx_t;
}

plugin_t PLUGIN =
{
  IDP_INTERFACE_VERSION,
  PLUGIN_HIDE | PLUGIN_MULTI,
  init,
  nullptr,
  nullptr,
  "PowerPC paired-single Hex-Rays support",
  "Adds microcode/helper support for Wii U paired-single instructions.",
  "PPC paired-single Hex-Rays",
  nullptr,
};
