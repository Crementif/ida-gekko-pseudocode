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
constexpr int PS_LANE_WIDTH = 4;
constexpr const char *PS_TYPE_NAME = "ppc_ps_t";
constexpr const char *ALWAYS_FIX_ACTION_NAME = "ppc_ps_hexrays:always_fix";
constexpr const char *FIX_FUNCTION_ACTION_NAME = "ppc_ps_hexrays:fix_function";
constexpr const char *REG_SUBKEY = "ppc_ps_hexrays";
constexpr const char *REG_ALWAYS_FIX = "always_fix_paired_singles";

struct function_gate_t
{
  virtual bool should_fix_ea(ea_t ea) const = 0;
};

enum raw_ps_kind_t
{
  RAW_PS_NONE,
  RAW_PS_SUM0,
  RAW_PS_SUM1,
  RAW_PS_SEL,
  RAW_FSEL,
};

struct raw_ps_operands_t
{
  op_t dst;
  op_t a;
  op_t b;
  op_t c;
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

struct insn_ops_guard_t
{
  insn_t &insn;
  op_t old_ops[UA_MAXOP];

  explicit insn_ops_guard_t(insn_t &i) : insn(i)
  {
    for ( int n = 0; n < UA_MAXOP; ++n )
      old_ops[n] = insn.ops[n];
  }

  ~insn_ops_guard_t()
  {
    for ( int n = 0; n < UA_MAXOP; ++n )
      insn.ops[n] = old_ops[n];
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

static bool is_scalar_plus_one_pair_access(const insn_t &insn)
{
  // psq_l/st with W=1,I=0 transfers lane 0 and uses the architectural
  // single-element encoding for lane 1. Wii U affine matrix helpers commonly
  // rely on this form for xyz + implicit w=1 vectors.
  return is_imm_value(insn.Op3, 1) && is_imm_value(insn.Op4, 0);
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
// Forward-declare parse_fpr_operands_from_disasm so it can be used before its
// definition later in the file.
static bool parse_fpr_operands_from_disasm(const insn_t &insn, const char *mnem, op_t *out, int count);

static bool mnem_matches(const char *text, const char *mnem)
{
  if ( text == nullptr || mnem == nullptr )
    return false;

  while ( qisspace(*text) )
    ++text;

  size_t len = qstrlen(mnem);
  return strnicmp(text, mnem, len) == 0
      && (text[len] == '\0' || text[len] == '.' || qisspace(text[len]));
}

static const char *find_mnem_token(const char *text, const char *mnem)
{
  if ( text == nullptr || mnem == nullptr )
    return nullptr;

  const size_t len = qstrlen(mnem);
  for ( const char *p = stristr(text, mnem); p != nullptr; p = stristr(p + 1, mnem) )
  {
    const char prev = p == text ? '\0' : p[-1];
    const char next = p[len];
    const bool before_ok = prev == '\0' || qisspace(prev) || prev == ':' || prev == ';';
    const bool after_ok = next == '\0' || next == '.' || qisspace(next);
    if ( before_ok && after_ok )
      return p;
  }
  return nullptr;
}

static bool get_disasm_line(qstring *out, ea_t ea)
{
  qstring line;
  if ( generate_disasm_line(&line, ea, GENDSM_FORCE_CODE | GENDSM_REMOVE_TAGS) )
  {
    *out = line;
    return true;
  }

  if ( !print_insn_mnem(&line, ea) )
    return false;

  tag_remove(out, line.c_str());
  return true;
}

static bool has_mnem(const insn_t &insn, const char *mnem)
{
  const char *canon = insn.get_canon_mnem(PH);
  if ( mnem_matches(canon, mnem) )
    return true;

  qstring printed;
  if ( !print_insn_mnem(&printed, insn.ea) )
    return false;

  qstring plain;
  tag_remove(&plain, printed.c_str());
  if ( mnem_matches(plain.c_str(), mnem) || find_mnem_token(plain.c_str(), mnem) != nullptr )
    return true;

  qstring line;
  if ( !get_disasm_line(&line, insn.ea) )
    return false;
  return mnem_matches(line.c_str(), mnem) || find_mnem_token(line.c_str(), mnem) != nullptr;
}

static bool is_fsel_mnemonic(const insn_t &insn)
{
  return has_mnem(insn, "fsel");
}

static bool is_ps_sum0_mnemonic(const insn_t &insn)
{
  return has_mnem(insn, "ps_sum0");
}

static bool is_ps_sum1_mnemonic(const insn_t &insn)
{
  return has_mnem(insn, "ps_sum1");
}

static bool is_ps_sel_mnemonic(const insn_t &insn)
{
  return has_mnem(insn, "ps_sel");
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

static mreg_t get_fpr_lane_mreg(const op_t &op, int lane)
{
  if ( lane < 0 || lane > 1 || op.type != o_reg )
    return mr_none;

  mreg_t mr = reg2mreg(op.reg);
  if ( mr == mr_none )
    return mr_none;
  return mr + lane * PS_LANE_WIDTH;
}

static bool make_fpr_lane_mop(mop_t *out, const op_t &op, int lane)
{
  mreg_t mr = get_fpr_lane_mreg(op, lane);
  if ( mr == mr_none )
    return false;

  out->make_reg(mr, PS_LANE_WIDTH);
  return true;
}

static bool collect_reg_operands(const insn_t &insn, const op_t **out, int count)
{
  int found = 0;
  for ( int opnum = 0; opnum < UA_MAXOP && found < count; ++opnum )
  {
    if ( insn.ops[opnum].type == o_reg )
      out[found++] = &insn.ops[opnum];
  }
  return found == count;
}

static bool get_reg_operands_from_insn_or_disasm(
        const insn_t &insn,
        const char *mnem,
        const op_t **out,
        op_t *parsed,
        int count)
{
  if ( collect_reg_operands(insn, out, count) )
    return true;
  if ( mnem == nullptr || !parse_fpr_operands_from_disasm(insn, mnem, parsed, count) )
    return false;
  for ( int i = 0; i < count; ++i )
    out[i] = &parsed[i];
  return true;
}

static bool make_fpr_op(op_t *out, int fpr)
{
  if ( fpr < 0 || fpr > 31 )
    return false;

  qstring regname;
  regname.sprnt("f%d", fpr);
  int reg = str2reg(regname.c_str());
  if ( reg < 0 )
  {
    regname.sprnt("fr%d", fpr);
    reg = str2reg(regname.c_str());
  }
  if ( reg < 0 )
    return false;

  *out = op_t();
  out->type = o_reg;
  out->reg = uint16(reg);
  out->dtype = dt_float;
  return true;
}

static raw_ps_kind_t decode_raw_ps_a_form(raw_ps_operands_t *out, const insn_t &insn)
{
  const uint32 word = get_dword(insn.ea);
  if ( (word >> 26) != 4 )
    return RAW_PS_NONE;

  raw_ps_kind_t kind = RAW_PS_NONE;
  switch ( (word >> 1) & 0x1F )
  {
    case 10: kind = RAW_PS_SUM0; break;
    case 11: kind = RAW_PS_SUM1; break;
    case 23: kind = RAW_PS_SEL; break;
    default: return RAW_PS_NONE;
  }

  if ( out == nullptr )
    return kind;

  if ( !make_fpr_op(&out->dst, int((word >> 21) & 0x1F))
    || !make_fpr_op(&out->a, int((word >> 16) & 0x1F))
    || !make_fpr_op(&out->b, int((word >> 11) & 0x1F))
    || !make_fpr_op(&out->c, int((word >> 6) & 0x1F)) )
  {
    return RAW_PS_NONE;
  }

  return kind;
}

static raw_ps_kind_t decode_raw_fsel_a_form(raw_ps_operands_t *out, const insn_t &insn)
{
  const uint32 word = get_dword(insn.ea);
  if ( (word >> 26) != 63 || ((word >> 1) & 0x1F) != 23 )
    return RAW_PS_NONE;

  if ( out == nullptr )
    return RAW_FSEL;

  if ( !make_fpr_op(&out->dst, int((word >> 21) & 0x1F))
    || !make_fpr_op(&out->a, int((word >> 16) & 0x1F))
    || !make_fpr_op(&out->b, int((word >> 11) & 0x1F))
    || !make_fpr_op(&out->c, int((word >> 6) & 0x1F)) )
  {
    return RAW_PS_NONE;
  }

  return RAW_FSEL;
}

static bool parse_fpr_operands_from_disasm(const insn_t &insn, const char *mnem, op_t *out, int count)
{
  qstring line;
  if ( !get_disasm_line(&line, insn.ea) )
    return false;

  const char *p = find_mnem_token(line.c_str(), mnem);
  if ( p == nullptr )
    return false;
  p += qstrlen(mnem);

  int found = 0;
  while ( *p != '\0' && found < count )
  {
    while ( *p != '\0' && *p != 'f' && *p != 'F' )
      ++p;
    if ( *p == '\0' )
      break;

    const char *digits = p + 1;
    if ( !qisdigit(*digits) )
    {
      ++p;
      continue;
    }

    int fpr = 0;
    while ( qisdigit(*digits) )
    {
      fpr = fpr * 10 + (*digits - '0');
      ++digits;
    }
    if ( fpr < 0 || fpr > 31 )
    {
      p = digits;
      continue;
    }

    if ( !make_fpr_op(&out[found], fpr) )
      return false;
    ++found;
    p = digits;
  }
  return found == count;
}

static bool set_pair_mem_lane(insn_t *insn, int opnum, int lane)
{
  if ( lane < 0 || lane > 1 || opnum < 0 || opnum >= UA_MAXOP )
    return false;

  op_t &op = insn->ops[opnum];
  if ( op.type != o_displ )
    return false;

  op.dtype = dt_float;
  op.addr += lane * PS_LANE_WIDTH;
  return true;
}

static void mark_float_insn(minsn_t *ins)
{
  if ( ins != nullptr )
    ins->set_fpinsn();
}

static bool emit_float_insn(codegen_t &cdg, mcode_t opcode, const mop_t &lhs, const mop_t *rhs, const mop_t &dst)
{
  mark_float_insn(cdg.emit(opcode, &lhs, rhs, &dst));
  return true;
}

static bool emit_float_mov(codegen_t &cdg, const mop_t &src, const mop_t &dst)
{
  return emit_float_insn(cdg, m_mov, src, nullptr, dst);
}

static bool make_float_constant_mop(mop_t *out, float value)
{
  return out->make_fpnum(&value, sizeof(value));
}

static bool emit_float_unary_lane(codegen_t &cdg, mcode_t opcode, const op_t &dst_op, const op_t &src_op, int lane)
{
  mop_t src;
  mop_t dst;
  if ( !make_fpr_lane_mop(&src, src_op, lane) || !make_fpr_lane_mop(&dst, dst_op, lane) )
    return false;
  return emit_float_insn(cdg, opcode, src, nullptr, dst);
}

static bool emit_float_binary_lane(
        codegen_t &cdg,
        mcode_t opcode,
        const op_t &dst_op,
        const op_t &lhs_op,
        int lhs_lane,
        const op_t &rhs_op,
        int rhs_lane,
        int dst_lane)
{
  mop_t lhs;
  mop_t rhs;
  mop_t dst;
  if ( !make_fpr_lane_mop(&lhs, lhs_op, lhs_lane)
    || !make_fpr_lane_mop(&rhs, rhs_op, rhs_lane)
    || !make_fpr_lane_mop(&dst, dst_op, dst_lane) )
  {
    return false;
  }
  return emit_float_insn(cdg, opcode, lhs, &rhs, dst);
}

static bool emit_float_lane_copy(codegen_t &cdg, const op_t &dst_op, int dst_lane, const op_t &src_op, int src_lane)
{
  mop_t src;
  mop_t dst;
  if ( !make_fpr_lane_mop(&src, src_op, src_lane) || !make_fpr_lane_mop(&dst, dst_op, dst_lane) )
    return false;
  return emit_float_mov(cdg, src, dst);
}

static bool emit_float_lane_copy_from_mreg(codegen_t &cdg, const op_t &dst_op, int dst_lane, mreg_t src_mr)
{
  if ( src_mr == mr_none )
    return false;

  mop_t src(src_mr, PS_LANE_WIDTH);
  mop_t dst;
  if ( !make_fpr_lane_mop(&dst, dst_op, dst_lane) )
    return false;
  return emit_float_mov(cdg, src, dst);
}

static bool append_fpr_lane_arg(
        mcallargs_t *args,
        const op_t &op,
        int lane,
        const tinfo_t &type,
        const char *name,
        ea_t ea)
{
  mop_t mop;
  if ( !make_fpr_lane_mop(&mop, op, lane) )
    return false;
  return append_mop_arg(args, mop, type, name, ea);
}

static bool emit_float_helper_call(codegen_t &cdg, const char *helper, const mcallargs_t &args, const mop_t &out)
{
  tinfo_t fp_type = get_fp_tinfo(dt_float);
  minsn_t *call = cdg.mba->create_helper_call(cdg.insn.ea, helper, &fp_type, &args, &out);
  if ( call == nullptr )
    return false;

  cdg.mb->insert_into_block(call, cdg.mb->tail);
  return true;
}

static bool emit_float_unary_helper_lane(codegen_t &cdg, const char *helper, const op_t &dst_op, const op_t &src_op, int lane)
{
  tinfo_t fp_type = get_fp_tinfo(dt_float);
  mcallargs_t args;
  mop_t dst;
  if ( !append_fpr_lane_arg(&args, src_op, lane, fp_type, "x", cdg.insn.ea)
    || !make_fpr_lane_mop(&dst, dst_op, lane) )
  {
    return false;
  }
  return emit_float_helper_call(cdg, helper, args, dst);
}

static bool emit_float_ternary_helper_lane(
        codegen_t &cdg,
        const char *helper,
        const op_t &dst_op,
        const op_t &arg0_op,
        const op_t &arg1_op,
        const op_t &arg2_op,
        int lane)
{
  tinfo_t fp_type = get_fp_tinfo(dt_float);
  mcallargs_t args;
  mop_t dst;
  if ( !append_fpr_lane_arg(&args, arg0_op, lane, fp_type, "test", cdg.insn.ea)
    || !append_fpr_lane_arg(&args, arg1_op, lane, fp_type, "ge_zero", cdg.insn.ea)
    || !append_fpr_lane_arg(&args, arg2_op, lane, fp_type, "lt_zero", cdg.insn.ea)
    || !make_fpr_lane_mop(&dst, dst_op, lane) )
  {
    return false;
  }
  return emit_float_helper_call(cdg, helper, args, dst);
}

static merror_t insert_helper_call(codegen_t &cdg, const char *helper, const tinfo_t *ret_type, const mcallargs_t *args, const mop_t *out);

static bool append_fpr_double_mop_arg(
        mcallargs_t *args,
        const op_t &op,
        const tinfo_t &type,
        const char *name,
        ea_t ea)
{
  if ( op.type != o_reg )
    return false;

  mreg_t mr = reg2mreg(op.reg);
  if ( mr == mr_none )
    return false;

  mop_t mop(mr, PS_WIDTH);
  return append_mop_arg(args, mop, type, name, ea);
}

static merror_t emit_fsel_ops(codegen_t &cdg, const op_t &dst_op, const op_t &test_op, const op_t &ge_zero_op, const op_t &lt_zero_op)
{
  tinfo_t fp_type = get_fp_tinfo(dt_double);
  mcallargs_t args;
  if ( !append_fpr_double_mop_arg(&args, test_op, fp_type, "test", cdg.insn.ea)
    || !append_fpr_double_mop_arg(&args, ge_zero_op, fp_type, "ge_zero", cdg.insn.ea)
    || !append_fpr_double_mop_arg(&args, lt_zero_op, fp_type, "lt_zero", cdg.insn.ea) )
  {
    return MERR_INSN;
  }

  if ( dst_op.type != o_reg )
    return MERR_INSN;

  mreg_t dst_mr = reg2mreg(dst_op.reg);
  if ( dst_mr == mr_none )
    return MERR_INSN;

  mop_t out(dst_mr, PS_WIDTH);
  return insert_helper_call(cdg, "__ppc_fsel", &fp_type, &args, &out);
}

static bool pair_mem_lane_load(codegen_t &cdg, int opnum, int lane, mreg_t *out)
{
  insn_ops_guard_t guard(cdg.insn);
  if ( !set_pair_mem_lane(&cdg.insn, opnum, lane) )
    return false;

  mreg_t loaded = cdg.load_operand(opnum);
  if ( loaded == mr_none )
    return false;

  *out = loaded;
  return true;
}

static bool pair_mem_lane_store(codegen_t &cdg, int opnum, int lane, const mop_t &src)
{
  insn_ops_guard_t guard(cdg.insn);
  if ( !set_pair_mem_lane(&cdg.insn, opnum, lane) )
    return false;

  minsn_t *outins = nullptr;
  if ( !cdg.store_operand(opnum, src, 0, &outins) )
    return false;
  mark_float_insn(outins);
  return true;
}

static merror_t emit_ps_lanewise_binary(codegen_t &cdg, mcode_t opcode)
{
  const op_t *regs[3] = {};
  op_t parsed_regs[3];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 3) )
    return MERR_INSN;

  if ( !emit_float_binary_lane(cdg, opcode, *regs[0], *regs[1], 0, *regs[2], 0, 0)
    || !emit_float_binary_lane(cdg, opcode, *regs[0], *regs[1], 1, *regs[2], 1, 1) )
  {
    return MERR_INSN;
  }
  return MERR_OK;
}

static merror_t emit_ps_lanewise_unary(codegen_t &cdg, mcode_t opcode)
{
  const op_t *regs[2] = {};
  op_t parsed_regs[2];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 2) )
    return MERR_INSN;

  if ( !emit_float_unary_lane(cdg, opcode, *regs[0], *regs[1], 0)
    || !emit_float_unary_lane(cdg, opcode, *regs[0], *regs[1], 1) )
  {
    return MERR_INSN;
  }
  return MERR_OK;
}

static merror_t emit_ps_mr(codegen_t &cdg)
{
  const op_t *regs[2] = {};
  op_t parsed_regs[2];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, "ps_mr", regs, parsed_regs, 2) )
    return MERR_INSN;

  if ( !emit_float_lane_copy(cdg, *regs[0], 0, *regs[1], 0)
    || !emit_float_lane_copy(cdg, *regs[0], 1, *regs[1], 1) )
  {
    return MERR_INSN;
  }
  return MERR_OK;
}

static merror_t emit_ps_muls_lane(codegen_t &cdg, int scalar_lane)
{
  if ( scalar_lane < 0 || scalar_lane > 1 )
  {
    return MERR_INSN;
  }

  const op_t *regs[3] = {};
  op_t parsed_regs[3];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 3) )
    return MERR_INSN;

  mop_t scale_src;
  if ( !make_fpr_lane_mop(&scale_src, *regs[2], scalar_lane) )
    return MERR_INSN;

  for ( int lane = 0; lane < 2; ++lane )
  {
    mop_t lhs;
    mop_t dst;
    if ( !make_fpr_lane_mop(&lhs, *regs[1], lane)
      || !make_fpr_lane_mop(&dst, *regs[0], lane) )
    {
      return MERR_INSN;
    }
  }

  mreg_t scale_tmp = cdg.mba->alloc_kreg(PS_LANE_WIDTH);
  if ( scale_tmp == mr_none )
    return MERR_INSN;

  mop_t scale(scale_tmp, PS_LANE_WIDTH);
  emit_float_mov(cdg, scale_src, scale);
  for ( int lane = 0; lane < 2; ++lane )
  {
    mop_t lhs;
    mop_t dst;
    if ( !make_fpr_lane_mop(&lhs, *regs[1], lane)
      || !make_fpr_lane_mop(&dst, *regs[0], lane)
      || !emit_float_insn(cdg, m_fmul, lhs, &scale, dst) )
    {
      return MERR_INSN;
    }
  }
  return MERR_OK;
}

static merror_t emit_ps_madd_like(codegen_t &cdg, bool subtract, bool negate, int scalar_multiplier_lane)
{
  if ( scalar_multiplier_lane < -1 || scalar_multiplier_lane > 1 )
  {
    return MERR_INSN;
  }

  const op_t *regs[4] = {};
  op_t parsed_regs[4];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 4) )
    return MERR_INSN;

  mop_t scalar_multiplier;
  if ( scalar_multiplier_lane >= 0 )
  {
    mop_t scalar_src;
    if ( !make_fpr_lane_mop(&scalar_src, *regs[2], scalar_multiplier_lane) )
      return MERR_INSN;

    mreg_t scalar_tmp = cdg.mba->alloc_kreg(PS_LANE_WIDTH);
    if ( scalar_tmp == mr_none )
      return MERR_INSN;

    scalar_multiplier.make_reg(scalar_tmp, PS_LANE_WIDTH);
  }

  for ( int lane = 0; lane < 2; ++lane )
  {
    mop_t lhs;
    mop_t rhs;
    mop_t addend;
    mop_t dst;
    if ( !make_fpr_lane_mop(&lhs, *regs[1], lane)
      || !make_fpr_lane_mop(&addend, *regs[3], lane)
      || !make_fpr_lane_mop(&dst, *regs[0], lane) )
    {
      return MERR_INSN;
    }
    if ( scalar_multiplier_lane < 0 && !make_fpr_lane_mop(&rhs, *regs[2], lane) )
      return MERR_INSN;
  }

  mreg_t product_tmp = cdg.mba->alloc_kreg(PS_LANE_WIDTH);
  if ( product_tmp == mr_none )
    return MERR_INSN;

  if ( scalar_multiplier_lane >= 0 )
  {
    mop_t scalar_src;
    if ( !make_fpr_lane_mop(&scalar_src, *regs[2], scalar_multiplier_lane) )
      return MERR_INSN;
    emit_float_mov(cdg, scalar_src, scalar_multiplier);
  }

  mop_t product(product_tmp, PS_LANE_WIDTH);
  for ( int lane = 0; lane < 2; ++lane )
  {
    mop_t lhs;
    mop_t rhs;
    mop_t addend;
    mop_t dst;
    if ( !make_fpr_lane_mop(&lhs, *regs[1], lane)
      || !make_fpr_lane_mop(&addend, *regs[3], lane)
      || !make_fpr_lane_mop(&dst, *regs[0], lane) )
    {
      return MERR_INSN;
    }

    if ( scalar_multiplier_lane >= 0 )
      rhs = scalar_multiplier;
    else if ( !make_fpr_lane_mop(&rhs, *regs[2], lane) )
      return MERR_INSN;

    if ( !emit_float_insn(cdg, m_fmul, lhs, &rhs, product)
      || !emit_float_insn(cdg, subtract ? m_fsub : m_fadd, product, &addend, dst) )
    {
      return MERR_INSN;
    }
    if ( negate && !emit_float_insn(cdg, m_fneg, dst, nullptr, dst) )
      return MERR_INSN;
  }
  return MERR_OK;
}

static merror_t emit_ps_sum_ops(codegen_t &cdg, const op_t &dst_op, const op_t &a_op, const op_t &b_op, const op_t &c_op, bool sum0)
{
  const int sum_dst_lane = sum0 ? 0 : 1;
  const int copy_dst_lane = sum0 ? 1 : 0;
  const int copy_src_lane = sum0 ? 1 : 0;
  mop_t sum_lhs;
  mop_t sum_rhs;
  mop_t sum_dst;
  mop_t copy_src;
  mop_t copy_dst;
  if ( !make_fpr_lane_mop(&sum_lhs, a_op, 0)
    || !make_fpr_lane_mop(&sum_rhs, b_op, 1)
    || !make_fpr_lane_mop(&sum_dst, dst_op, sum_dst_lane)
    || !make_fpr_lane_mop(&copy_src, c_op, copy_src_lane)
    || !make_fpr_lane_mop(&copy_dst, dst_op, copy_dst_lane) )
  {
    return MERR_INSN;
  }

  if ( !emit_float_insn(cdg, m_fadd, sum_lhs, &sum_rhs, sum_dst)
    || !emit_float_mov(cdg, copy_src, copy_dst) )
  {
    return MERR_INSN;
  }
  return MERR_OK;
}

static merror_t emit_ps_sum(codegen_t &cdg, bool sum0)
{
  const op_t *regs[4] = {};
  op_t parsed_regs[4];
  if ( !collect_reg_operands(cdg.insn, regs, 4) )
  {
    if ( !parse_fpr_operands_from_disasm(cdg.insn, sum0 ? "ps_sum0" : "ps_sum1", parsed_regs, 4) )
      return MERR_INSN;
    for ( int i = 0; i < 4; ++i )
      regs[i] = &parsed_regs[i];
  }

  return emit_ps_sum_ops(cdg, *regs[0], *regs[1], *regs[2], *regs[3], sum0);
}

static merror_t emit_ps_unary_helper(codegen_t &cdg, const char *helper, bool negate_result=false)
{
  const op_t *regs[2] = {};
  op_t parsed_regs[2];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 2) )
    return MERR_INSN;

  for ( int lane = 0; lane < 2; ++lane )
  {
    if ( !emit_float_unary_helper_lane(cdg, helper, *regs[0], *regs[1], lane) )
      return MERR_INSN;
    if ( negate_result && !emit_float_unary_lane(cdg, m_fneg, *regs[0], *regs[0], lane) )
      return MERR_INSN;
  }
  return MERR_OK;
}

static merror_t emit_ps_sel_ops(codegen_t &cdg, const op_t &dst_op, const op_t &test_op, const op_t &ge_zero_op, const op_t &lt_zero_op)
{
  for ( int lane = 0; lane < 2; ++lane )
    if ( !emit_float_ternary_helper_lane(cdg, "__ppc_ps_sel_scalar", dst_op, test_op, ge_zero_op, lt_zero_op, lane) )
      return MERR_INSN;
  return MERR_OK;
}

static merror_t emit_ps_sel(codegen_t &cdg)
{
  const op_t *regs[4] = {};
  op_t parsed_regs[4];
  if ( !collect_reg_operands(cdg.insn, regs, 4) )
  {
    if ( !parse_fpr_operands_from_disasm(cdg.insn, "ps_sel", parsed_regs, 4) )
      return MERR_INSN;
    for ( int i = 0; i < 4; ++i )
      regs[i] = &parsed_regs[i];
  }

  return emit_ps_sel_ops(cdg, *regs[0], *regs[1], *regs[2], *regs[3]);
}

static merror_t emit_ps_merge(codegen_t &cdg, int dst0_src_opnum, int dst0_src_lane, int dst1_src_opnum, int dst1_src_lane)
{
  if ( cdg.insn.Op1.type != o_reg
    || dst0_src_opnum < 0 || dst0_src_opnum >= UA_MAXOP
    || dst1_src_opnum < 0 || dst1_src_opnum >= UA_MAXOP )
  {
    return MERR_INSN;
  }

  const op_t &src0_op = cdg.insn.ops[dst0_src_opnum];
  const op_t &src1_op = cdg.insn.ops[dst1_src_opnum];
  if ( src0_op.type != o_reg || src1_op.type != o_reg )
    return MERR_INSN;

  mop_t src0;
  mop_t src1;
  if ( !make_fpr_lane_mop(&src0, src0_op, dst0_src_lane)
    || !make_fpr_lane_mop(&src1, src1_op, dst1_src_lane) )
  {
    return MERR_INSN;
  }

  mreg_t tmp0 = cdg.mba->alloc_kreg(PS_LANE_WIDTH);
  mreg_t tmp1 = cdg.mba->alloc_kreg(PS_LANE_WIDTH);
  if ( tmp0 == mr_none || tmp1 == mr_none )
    return MERR_INSN;

  mop_t tmp0_mop(tmp0, PS_LANE_WIDTH);
  mop_t tmp1_mop(tmp1, PS_LANE_WIDTH);
  emit_float_mov(cdg, src0, tmp0_mop);
  emit_float_mov(cdg, src1, tmp1_mop);

  if ( !emit_float_lane_copy_from_mreg(cdg, cdg.insn.Op1, 0, tmp0)
    || !emit_float_lane_copy_from_mreg(cdg, cdg.insn.Op1, 1, tmp1) )
  {
    return MERR_INSN;
  }
  return MERR_OK;
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
  if ( cdg.insn.Op1.type != o_reg || cdg.insn.Op2.type != o_displ )
  {
    return MERR_INSN;
  }

  if ( is_unquantized_pair_access(cdg.insn) )
  {
    for ( int lane = 0; lane < 2; ++lane )
    {
      mreg_t loaded = mr_none;
      mop_t dst;
      if ( !pair_mem_lane_load(cdg, 1, lane, &loaded)
        || !make_fpr_lane_mop(&dst, cdg.insn.Op1, lane) )
      {
        return MERR_INSN;
      }

      mop_t src(loaded, PS_LANE_WIDTH);
      emit_float_mov(cdg, src, dst);
    }
    return MERR_OK;
  }

  if ( !is_scalar_plus_one_pair_access(cdg.insn) )
    return MERR_INSN;

  mreg_t loaded = mr_none;
  mop_t dst0;
  mop_t dst1;
  mop_t one;
  if ( !pair_mem_lane_load(cdg, 1, 0, &loaded)
    || !make_fpr_lane_mop(&dst0, cdg.insn.Op1, 0)
    || !make_fpr_lane_mop(&dst1, cdg.insn.Op1, 1)
    || !make_float_constant_mop(&one, 1.0f) )
  {
    return MERR_INSN;
  }

  mop_t src0(loaded, PS_LANE_WIDTH);
  emit_float_mov(cdg, src0, dst0);
  emit_float_mov(cdg, one, dst1);
  return MERR_OK;
}

static merror_t emit_psq_store(codegen_t &cdg)
{
  if ( cdg.insn.Op1.type != o_reg || cdg.insn.Op2.type != o_displ )
  {
    return MERR_INSN;
  }

  if ( is_unquantized_pair_access(cdg.insn) )
  {
    for ( int lane = 0; lane < 2; ++lane )
    {
      mop_t src;
      if ( !make_fpr_lane_mop(&src, cdg.insn.Op1, lane)
        || !pair_mem_lane_store(cdg, 1, lane, src) )
      {
        return MERR_INSN;
      }
    }
    return MERR_OK;
  }

  if ( !is_scalar_plus_one_pair_access(cdg.insn) )
    return MERR_INSN;

  mop_t src;
  if ( !make_fpr_lane_mop(&src, cdg.insn.Op1, 0)
    || !pair_mem_lane_store(cdg, 1, 0, src) )
  {
    return MERR_INSN;
  }

  return MERR_OK;
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
  const op_t *regs[4] = {};
  op_t parsed_regs[4];
  raw_ps_operands_t raw_ops;
  if ( collect_reg_operands(cdg.insn, regs, 4) )
    return emit_fsel_ops(cdg, *regs[0], *regs[1], *regs[2], *regs[3]);
  if ( parse_fpr_operands_from_disasm(cdg.insn, "fsel", parsed_regs, 4) )
    return emit_fsel_ops(cdg, parsed_regs[0], parsed_regs[1], parsed_regs[2], parsed_regs[3]);
  if ( decode_raw_fsel_a_form(&raw_ops, cdg.insn) == RAW_FSEL )
    return emit_fsel_ops(cdg, raw_ops.dst, raw_ops.a, raw_ops.b, raw_ops.c);

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

static const char *ps_helper_name_from_mnem(const insn_t &insn, int *max_arg_qty)
{
  struct ps_mnem_helper_t
  {
    const char *mnem;
    const char *helper;
    int max_args;
  };

  static const ps_mnem_helper_t table[] =
  {
    { "ps_add", "__ppc_ps_add", 2 },
    { "ps_sub", "__ppc_ps_sub", 2 },
    { "ps_mul", "__ppc_ps_mul", 2 },
    { "ps_div", "__ppc_ps_div", 2 },
    { "ps_muls0", "__ppc_ps_muls0", 2 },
    { "ps_muls1", "__ppc_ps_muls1", 2 },
    { "ps_madd", "__ppc_ps_madd", 3 },
    { "ps_msub", "__ppc_ps_msub", 3 },
    { "ps_nmadd", "__ppc_ps_nmadd", 3 },
    { "ps_nmsub", "__ppc_ps_nmsub", 3 },
    { "ps_madds0", "__ppc_ps_madds0", 3 },
    { "ps_madds1", "__ppc_ps_madds1", 3 },
    { "ps_neg", "__ppc_ps_neg", 1 },
    { "ps_abs", "__ppc_ps_abs", 1 },
    { "ps_nabs", "__ppc_ps_nabs", 1 },
    { "ps_mr", "__ppc_ps_mr", 1 },
    { "ps_merge00", "__ppc_ps_merge00", 2 },
    { "ps_merge01", "__ppc_ps_merge01", 2 },
    { "ps_merge10", "__ppc_ps_merge10", 2 },
    { "ps_merge11", "__ppc_ps_merge11", 2 },
    { "ps_res", "__ppc_ps_res", 1 },
    { "ps_rsqrte", "__ppc_ps_rsqrte", 1 },
    { "ps_sel", "__ppc_ps_sel", 3 },
    { "ps_sum0", "__ppc_ps_sum0", 3 },
    { "ps_sum1", "__ppc_ps_sum1", 3 },
    { "ps_cmpu0", "__ppc_ps_cmpu0", 2 },
    { "ps_cmpu1", "__ppc_ps_cmpu1", 2 },
    { "ps_cmpo0", "__ppc_ps_cmpo0", 2 },
    { "ps_cmpo1", "__ppc_ps_cmpo1", 2 },
  };

  for ( const ps_mnem_helper_t &entry : table )
  {
    if ( has_mnem(insn, entry.mnem) )
    {
      if ( max_arg_qty != nullptr )
        *max_arg_qty = entry.max_args;
      return entry.helper;
    }
  }

  return nullptr;
}

static bool is_safe_early_lowered_insn(const insn_t &insn)
{
  switch ( insn.itype )
  {
    case PPC_fsel:
      return true;

    case PPC_psq_l:
    case PPC_psq_st:
      return (is_unquantized_pair_access(insn) || is_scalar_plus_one_pair_access(insn))
          && insn.Op1.type == o_reg
          && insn.Op2.type == o_displ;

    case PPC_ps_add:
    case PPC_ps_sub:
    case PPC_ps_mul:
    case PPC_ps_div:
    case PPC_ps_muls0:
    case PPC_ps_muls1:
    case PPC_ps_madd:
    case PPC_ps_msub:
    case PPC_ps_nmadd:
    case PPC_ps_nmsub:
    case PPC_ps_madds0:
    case PPC_ps_madds1:
    case PPC_ps_neg:
    case PPC_ps_abs:
    case PPC_ps_nabs:
    case PPC_ps_mr:
    case PPC_ps_merge00:
    case PPC_ps_merge01:
    case PPC_ps_merge10:
    case PPC_ps_merge11:
    case PPC_ps_res:
    case PPC_ps_rsqrte:
    case PPC_ps_sel:
    case PPC_ps_sum0:
    case PPC_ps_sum1:
      return true;

    default:
      return decode_raw_fsel_a_form(nullptr, insn) == RAW_FSEL
          || decode_raw_ps_a_form(nullptr, insn) != RAW_PS_NONE
          || is_fsel_mnemonic(insn)
          || ps_helper_name_from_mnem(insn, nullptr) != nullptr
          || is_ps_sum0_mnemonic(insn)
          || is_ps_sum1_mnemonic(insn)
          || is_ps_sel_mnemonic(insn);
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

static cexpr_t *make_float_const_expr(float value, ea_t ea);

static cexpr_t *build_psq_load_lane_expr(const cexpr_t *expr, int lane)
{
  expr = match_helper_call(expr, "__ppc_psq_l");
  if ( expr == nullptr || expr->a == nullptr || expr->a->size() < 3 )
    return nullptr;

  if ( is_zero_expr(&(*expr->a)[1]) && is_zero_expr(&(*expr->a)[2]) )
  {
    const uint32 byte_off = uint32(lane * 4);
    const cexpr_t *ea_arg = &(*expr->a)[0];
    if ( const cexpr_t *base = extract_address_base(ea_arg) )
      return build_float_expr_at_address(base, byte_off);
    return build_float_expr_from_ea_value(ea_arg, byte_off);
  }

  if ( !is_zero_expr(&(*expr->a)[2]) )
    return nullptr;

  const cexpr_t *w_arg = skip_casts(&(*expr->a)[1]);
  if ( w_arg == nullptr || !w_arg->is_const_value(1) )
    return nullptr;

  if ( lane == 1 )
    return make_float_const_expr(1.0f, expr->ea);

  const cexpr_t *ea_arg = &(*expr->a)[0];
  if ( const cexpr_t *base = extract_address_base(ea_arg) )
    return build_float_expr_at_address(base, 0);
  return build_float_expr_from_ea_value(ea_arg, 0);
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

static cexpr_t *make_float_const_expr(float value, ea_t ea)
{
  fpvalue_t fpval;
  if ( fpval.from_float(value) != REAL_ERROR_OK )
    return nullptr;

  cexpr_t *expr = new cexpr_t();
  expr->op = cot_fnum;
  expr->ea = ea;
  expr->type = get_fp_tinfo(dt_float);
  expr->fpc = new fnumber_t();
  expr->fpc->fnum = fpval;
  expr->fpc->nbytes = sizeof(value);
  return expr;
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

  auto madd_like = [&](bool subtract, bool negate, int scalar_lane) -> cexpr_t *
  {
    if ( nargs != 3 )
      return nullptr;

    cexpr_t *lhs = arg_lane(0, lane);
    cexpr_t *rhs = scalar_lane >= 0 ? arg_lane(1, scalar_lane) : arg_lane(1, lane);
    cexpr_t *addend = arg_lane(2, lane);
    if ( lhs == nullptr || rhs == nullptr || addend == nullptr )
    {
      delete lhs;
      delete rhs;
      delete addend;
      return nullptr;
    }

    cexpr_t *product = make_float_binary_expr(cot_fmul, lhs, rhs, expr->ea);
    cexpr_t *sum = make_float_binary_expr(subtract ? cot_fsub : cot_fadd, product, addend, expr->ea);
    return negate ? make_float_unary_expr(cot_fneg, sum, expr->ea) : sum;
  };

  if ( strcmp(helper, "__ppc_ps_madd") == 0 )
    return madd_like(false, false, -1);
  if ( strcmp(helper, "__ppc_ps_msub") == 0 )
    return madd_like(true, false, -1);
  if ( strcmp(helper, "__ppc_ps_nmadd") == 0 )
    return madd_like(false, true, -1);
  if ( strcmp(helper, "__ppc_ps_nmsub") == 0 )
    return madd_like(true, true, -1);
  if ( strcmp(helper, "__ppc_ps_madds0") == 0 )
    return madd_like(false, false, 0);
  if ( strcmp(helper, "__ppc_ps_madds1") == 0 )
    return madd_like(false, false, 1);

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
    const bool full_fix_enabled = gate == nullptr || gate->should_fix_ea(cdg.insn.ea);
    if ( !full_fix_enabled )
      return is_safe_early_lowered_insn(cdg.insn);

    int first_arg = 0;
    int max_arg_qty = 0;
    return is_wiiu_save_prolog_insn(cdg.insn)
        || cdg.insn.itype == PPC_fsel
        || is_fsel_mnemonic(cdg.insn)
        || ps_helper_name_from_mnem(cdg.insn, nullptr) != nullptr
        || is_ps_sum0_mnemonic(cdg.insn)
        || is_ps_sum1_mnemonic(cdg.insn)
        || is_ps_sel_mnemonic(cdg.insn)
        || is_psq_itype(cdg.insn.itype)
        || ps_helper_name(cdg.insn.itype, &first_arg, &max_arg_qty) != nullptr;
  }

  merror_t apply(codegen_t &cdg) override
  {
    const bool full_fix_enabled = gate == nullptr || gate->should_fix_ea(cdg.insn.ea);
    const bool safe_early = is_safe_early_lowered_insn(cdg.insn);
    if ( !full_fix_enabled && !safe_early )
      return MERR_INSN;

    auto early_or_helper = [&](merror_t err, const char *helper, int max_arg_qty) -> merror_t
    {
      if ( err == MERR_OK || !full_fix_enabled )
        return err;
      return emit_ps_helper(cdg, helper, 1, max_arg_qty);
    };

    if ( full_fix_enabled && is_wiiu_save_prolog_insn(cdg.insn) )
      return MERR_OK;

    if ( cdg.insn.itype == PPC_fsel
      || decode_raw_fsel_a_form(nullptr, cdg.insn) == RAW_FSEL
      || is_fsel_mnemonic(cdg.insn) )
    {
      return emit_fsel_helper(cdg);
    }

    raw_ps_operands_t raw_ops;
    raw_ps_kind_t raw_kind = decode_raw_ps_a_form(&raw_ops, cdg.insn);
    if ( raw_kind == RAW_PS_SUM0 || raw_kind == RAW_PS_SUM1 )
    {
      merror_t err = emit_ps_sum_ops(cdg, raw_ops.dst, raw_ops.a, raw_ops.b, raw_ops.c, raw_kind == RAW_PS_SUM0);
      if ( err == MERR_OK || !full_fix_enabled )
        return err;
      return emit_ps_helper(cdg, raw_kind == RAW_PS_SUM0 ? "__ppc_ps_sum0" : "__ppc_ps_sum1", 1, 3);
    }
    if ( raw_kind == RAW_PS_SEL )
      return early_or_helper(emit_ps_sel_ops(cdg, raw_ops.dst, raw_ops.a, raw_ops.b, raw_ops.c), "__ppc_ps_sel", 3);

    if ( cdg.insn.itype == PPC_ps_sum0 || is_ps_sum0_mnemonic(cdg.insn) )
    {
      merror_t err = emit_ps_sum(cdg, true);
      if ( err == MERR_OK || !full_fix_enabled )
        return err;

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
      merror_t err = emit_ps_sum(cdg, false);
      if ( err == MERR_OK || !full_fix_enabled )
        return err;

      op_dtype_t dtype = dt_float;
      if ( should_scalarize_ps_result(cdg.insn, &dtype) )
      {
        if ( emit_ps_scalar_helper(cdg, "__ppc_ps_sum1_scalar", dtype, 1, 3) == MERR_OK )
          return MERR_OK;
      }
      return emit_ps_helper(cdg, "__ppc_ps_sum1", 1, 3);
    }

    if ( cdg.insn.itype == PPC_ps_sel || is_ps_sel_mnemonic(cdg.insn) )
      return early_or_helper(emit_ps_sel(cdg), "__ppc_ps_sel", 3);

    if ( cdg.insn.itype != PPC_ps_sum0
      && cdg.insn.itype != PPC_ps_sum1
      && cdg.insn.itype != PPC_ps_sel )
    {
      int mnem_max_args = 0;
      if ( const char *mnem_helper = ps_helper_name_from_mnem(cdg.insn, &mnem_max_args) )
      {
        if ( strcmp(mnem_helper, "__ppc_ps_add") == 0 ) return early_or_helper(emit_ps_lanewise_binary(cdg, m_fadd), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_sub") == 0 ) return early_or_helper(emit_ps_lanewise_binary(cdg, m_fsub), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_mul") == 0 ) return early_or_helper(emit_ps_lanewise_binary(cdg, m_fmul), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_div") == 0 ) return early_or_helper(emit_ps_lanewise_binary(cdg, m_fdiv), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_muls0") == 0 ) return early_or_helper(emit_ps_muls_lane(cdg, 0), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_muls1") == 0 ) return early_or_helper(emit_ps_muls_lane(cdg, 1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_madd") == 0 ) return early_or_helper(emit_ps_madd_like(cdg, false, false, -1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_msub") == 0 ) return early_or_helper(emit_ps_madd_like(cdg, true, false, -1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_nmadd") == 0 ) return early_or_helper(emit_ps_madd_like(cdg, false, true, -1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_nmsub") == 0 ) return early_or_helper(emit_ps_madd_like(cdg, true, true, -1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_madds0") == 0 ) return early_or_helper(emit_ps_madd_like(cdg, false, false, 0), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_madds1") == 0 ) return early_or_helper(emit_ps_madd_like(cdg, false, false, 1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_neg") == 0 ) return early_or_helper(emit_ps_lanewise_unary(cdg, m_fneg), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_abs") == 0 ) return early_or_helper(emit_ps_unary_helper(cdg, "fabsf"), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_nabs") == 0 ) return early_or_helper(emit_ps_unary_helper(cdg, "fabsf", true), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_mr") == 0 ) return early_or_helper(emit_ps_mr(cdg), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_merge00") == 0 ) return early_or_helper(emit_ps_merge(cdg, 2, 0, 3, 0), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_merge01") == 0 ) return early_or_helper(emit_ps_merge(cdg, 2, 0, 3, 1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_merge10") == 0 ) return early_or_helper(emit_ps_merge(cdg, 2, 1, 3, 0), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_merge11") == 0 ) return early_or_helper(emit_ps_merge(cdg, 2, 1, 3, 1), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_res") == 0 ) return early_or_helper(emit_ps_unary_helper(cdg, "__ppc_ps_res_scalar"), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_rsqrte") == 0 ) return early_or_helper(emit_ps_unary_helper(cdg, "__ppc_ps_rsqrte_scalar"), mnem_helper, mnem_max_args);
        if ( strcmp(mnem_helper, "__ppc_ps_cmpu0") == 0 ) return emit_ps_compare_helper(cdg, mnem_helper);
        if ( strcmp(mnem_helper, "__ppc_ps_cmpu1") == 0 ) return emit_ps_compare_helper(cdg, mnem_helper);
        if ( strcmp(mnem_helper, "__ppc_ps_cmpo0") == 0 ) return emit_ps_compare_helper(cdg, mnem_helper);
        if ( strcmp(mnem_helper, "__ppc_ps_cmpo1") == 0 ) return emit_ps_compare_helper(cdg, mnem_helper);
        return full_fix_enabled ? emit_ps_helper(cdg, mnem_helper, 1, mnem_max_args) : MERR_INSN;
      }
    }

    switch ( cdg.insn.itype )
    {
      case PPC_psq_l:
        if ( emit_psq_load(cdg) == MERR_OK )
          return MERR_OK;
        if ( !full_fix_enabled )
          return MERR_INSN;
        return emit_psq_helper(cdg, "__ppc_psq_l", false);

      case PPC_psq_st:
        if ( emit_psq_store(cdg) == MERR_OK )
          return MERR_OK;
        if ( !full_fix_enabled )
          return MERR_INSN;
        return emit_psq_helper(cdg, "__ppc_psq_st", true);

      case PPC_psq_lu:  return full_fix_enabled ? emit_psq_helper(cdg, "__ppc_psq_lu", false) : MERR_INSN;
      case PPC_psq_lx:  return full_fix_enabled ? emit_psq_helper(cdg, "__ppc_psq_lx", false) : MERR_INSN;
      case PPC_psq_lux: return full_fix_enabled ? emit_psq_helper(cdg, "__ppc_psq_lux", false) : MERR_INSN;
      case PPC_psq_stu: return full_fix_enabled ? emit_psq_helper(cdg, "__ppc_psq_stu", true) : MERR_INSN;
      case PPC_psq_stx: return full_fix_enabled ? emit_psq_helper(cdg, "__ppc_psq_stx", true) : MERR_INSN;
      case PPC_psq_stux:return full_fix_enabled ? emit_psq_helper(cdg, "__ppc_psq_stux", true) : MERR_INSN;

      case PPC_ps_cmpu0: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpu0");
      case PPC_ps_cmpu1: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpu1");
      case PPC_ps_cmpo0: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpo0");
      case PPC_ps_cmpo1: return emit_ps_compare_helper(cdg, "__ppc_ps_cmpo1");

      case PPC_ps_add: return early_or_helper(emit_ps_lanewise_binary(cdg, m_fadd), "__ppc_ps_add", 2);
      case PPC_ps_sub: return early_or_helper(emit_ps_lanewise_binary(cdg, m_fsub), "__ppc_ps_sub", 2);
      case PPC_ps_mul: return early_or_helper(emit_ps_lanewise_binary(cdg, m_fmul), "__ppc_ps_mul", 2);
      case PPC_ps_div: return early_or_helper(emit_ps_lanewise_binary(cdg, m_fdiv), "__ppc_ps_div", 2);
      case PPC_ps_muls0: return early_or_helper(emit_ps_muls_lane(cdg, 0), "__ppc_ps_muls0", 2);
      case PPC_ps_muls1: return early_or_helper(emit_ps_muls_lane(cdg, 1), "__ppc_ps_muls1", 2);
      case PPC_ps_madd: return early_or_helper(emit_ps_madd_like(cdg, false, false, -1), "__ppc_ps_madd", 3);
      case PPC_ps_msub: return early_or_helper(emit_ps_madd_like(cdg, true, false, -1), "__ppc_ps_msub", 3);
      case PPC_ps_nmadd: return early_or_helper(emit_ps_madd_like(cdg, false, true, -1), "__ppc_ps_nmadd", 3);
      case PPC_ps_nmsub: return early_or_helper(emit_ps_madd_like(cdg, true, true, -1), "__ppc_ps_nmsub", 3);
      case PPC_ps_madds0: return early_or_helper(emit_ps_madd_like(cdg, false, false, 0), "__ppc_ps_madds0", 3);
      case PPC_ps_madds1: return early_or_helper(emit_ps_madd_like(cdg, false, false, 1), "__ppc_ps_madds1", 3);
      case PPC_ps_neg: return early_or_helper(emit_ps_lanewise_unary(cdg, m_fneg), "__ppc_ps_neg", 1);
      case PPC_ps_abs: return early_or_helper(emit_ps_unary_helper(cdg, "fabsf"), "__ppc_ps_abs", 1);
      case PPC_ps_nabs: return early_or_helper(emit_ps_unary_helper(cdg, "fabsf", true), "__ppc_ps_nabs", 1);
      case PPC_ps_mr: return early_or_helper(emit_ps_mr(cdg), "__ppc_ps_mr", 1);
      case PPC_ps_merge00: return early_or_helper(emit_ps_merge(cdg, 2, 0, 3, 0), "__ppc_ps_merge00", 2);
      case PPC_ps_merge01: return early_or_helper(emit_ps_merge(cdg, 2, 0, 3, 1), "__ppc_ps_merge01", 2);
      case PPC_ps_merge10: return early_or_helper(emit_ps_merge(cdg, 2, 1, 3, 0), "__ppc_ps_merge10", 2);
      case PPC_ps_merge11: return early_or_helper(emit_ps_merge(cdg, 2, 1, 3, 1), "__ppc_ps_merge11", 2);
      case PPC_ps_res: return early_or_helper(emit_ps_unary_helper(cdg, "__ppc_ps_res_scalar"), "__ppc_ps_res", 1);
      case PPC_ps_rsqrte: return early_or_helper(emit_ps_unary_helper(cdg, "__ppc_ps_rsqrte_scalar"), "__ppc_ps_rsqrte", 1);
      case PPC_ps_sel: return early_or_helper(emit_ps_sel(cdg), "__ppc_ps_sel", 3);

      default:
        if ( !full_fix_enabled )
          return MERR_INSN;
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
