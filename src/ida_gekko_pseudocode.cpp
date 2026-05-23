#include <ida.hpp>
#include <idp.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <bytes.hpp>
#include <funcs.hpp>
#include <hexrays.hpp>
#include <allins.hpp>
#include <name.hpp>
#include <netnode.hpp>
#include <typeinf.hpp>

#include "const_type_toggle_action.hpp"
#include "wiiu_save_prolog.hpp"
#include "selection_mass_type_action.hpp"

#ifdef _MSC_VER
// Dummy implementation of uint128 operator<< to satisfy MSVC linker when it instantiates
// unreferenced inline functions like builtin_widget_mask_from_id from kernwin.hpp.
uint128 operator<<(const uint128&, int) { return uint128(); }
#endif

namespace
{

constexpr int PS_WIDTH = 8;
constexpr int PS_LANE_WIDTH = 4;
constexpr const char *PS_TYPE_NAME = "ppc_ps_t";
constexpr const char *ALWAYS_FIX_ACTION_NAME = "ida_gekko_pseudocode:always_fix";
constexpr const char *TOGGLE_CONST_ACTION_NAME = "ida_gekko_pseudocode:toggle_const_type";
constexpr const char *ALWAYS_FIX_NODE_NAME = "$ ida_gekko_pseudocode";
constexpr nodeidx_t ALWAYS_FIX_NODE_IDX = 0;

static bool load_always_fix_setting()
{
  netnode node(ALWAYS_FIX_NODE_NAME);
  return node == BADNODE || node.altval(ALWAYS_FIX_NODE_IDX) != 0;
}

static void save_always_fix_setting(bool enabled)
{
  netnode node;
  if ( !node.create(ALWAYS_FIX_NODE_NAME) )
    node = netnode(ALWAYS_FIX_NODE_NAME);
  if ( node != BADNODE )
    node.altset(ALWAYS_FIX_NODE_IDX, enabled ? 1 : 0);
}

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

static bool make_bool_type(tinfo_t *out)
{
  *out = tinfo_t(BTF_BOOL);
  return true;
}

static bool make_void_type(tinfo_t *out)
{
  *out = tinfo_t(BTF_VOID);
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

static bool make_dest_mop(mop_t *out, const op_t &op, int width = PS_WIDTH)
{
  if ( op.type != o_reg )
    return false;

  mreg_t mr = reg2mreg(op.reg);
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
  if ( dst0_src_opnum < 0 || dst0_src_opnum >= UA_MAXOP
    || dst1_src_opnum < 0 || dst1_src_opnum >= UA_MAXOP )
  {
    return MERR_INSN;
  }

  const op_t *regs[3] = {};
  op_t parsed_regs[3];
  const char *mnem = cdg.insn.get_canon_mnem(PH);
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, mnem, regs, parsed_regs, 3) )
    return MERR_INSN;

  const op_t &dst_op = *regs[0];
  const op_t &src0_op = *regs[dst0_src_opnum - 1];
  const op_t &src1_op = *regs[dst1_src_opnum - 1];

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

  if ( !emit_float_lane_copy_from_mreg(cdg, dst_op, 0, tmp0)
    || !emit_float_lane_copy_from_mreg(cdg, dst_op, 1, tmp1) )
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

  const op_t *regs[4] = {};
  op_t parsed_regs[4];
  bool have_regs = get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 4);

  mcallargs_t args;
  static const char *arg_names[] = { "a", "b", "c", "d", "e", "f", "g" };
  int added = 0;
  for ( int opnum = first_arg_opnum; opnum < UA_MAXOP && added < max_arg_qty; ++opnum )
  {
    if ( have_regs )
    {
      if ( opnum < 1 || opnum > 4 || regs[opnum - 1] == nullptr )
        break;
      if ( !append_fpr_double_mop_arg(&args, *regs[opnum - 1], ps_type, arg_names[added], cdg.insn.ea) )
        return MERR_INSN;
    }
    else
    {
      if ( is_void_op(cdg.insn.ops[opnum]) )
        break;
      if ( !append_reg_arg(cdg, &args, opnum, ps_type, arg_names[added]) )
        return MERR_INSN;
    }
    ++added;
  }

  mop_t out;
  if ( have_regs )
  {
    if ( !make_dest_mop(&out, *regs[0]) )
      return MERR_INSN;
  }
  else if ( !make_dest_mop(&out, cdg.insn) )
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

  const op_t *regs[3] = {};
  op_t parsed_regs[3];
  if ( !get_reg_operands_from_insn_or_disasm(cdg.insn, cdg.insn.get_canon_mnem(PH), regs, parsed_regs, 3) )
    return MERR_INSN;

  tinfo_t ps_type;
  tinfo_t int_type;
  make_ps_type(&ps_type);
  make_int_type(&int_type);

  mcallargs_t args;
  if ( !append_fpr_double_mop_arg(&args, *regs[1], ps_type, "a", cdg.insn.ea) )
    return MERR_INSN;
  if ( !append_fpr_double_mop_arg(&args, *regs[2], ps_type, "b", cdg.insn.ea) )
    return MERR_INSN;

  mop_t out;
  if ( !make_dest_mop(&out, *regs[0], inf_get_cc_size_i()) )
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

static bool same_var_ref(const var_ref_t &lhs, const var_ref_t &rhs)
{
  return lhs.compare(rhs) == 0;
}

static bool get_var_ref(const cexpr_t *e, var_ref_t *out)
{
  e = skip_casts(e);
  if ( e == nullptr || e->op != cot_var )
    return false;
  if ( out != nullptr )
    *out = e->v;
  return true;
}

static bool is_var_expr(const cexpr_t *e, const var_ref_t &var)
{
  e = skip_casts(e);
  return e != nullptr && e->op == cot_var && same_var_ref(e->v, var);
}

static int pointer_stride_bytes(const tinfo_t &ptr_type)
{
  if ( !ptr_type.is_ptr() )
    return -1;

  const size_t stride = remove_pointer(ptr_type).get_size();
  if ( stride == BADSIZE || stride == 0 || stride > size_t(INT_MAX) )
    return -1;
  return int(stride);
}

static int pointer_step_bytes(const tinfo_t &ptr_type, int fallback=1)
{
  const int stride = pointer_stride_bytes(ptr_type);
  return stride > 0 ? stride : fallback;
}

static cexpr_t *clone_expr(const cexpr_t *e)
{
  return e != nullptr ? new cexpr_t(*e) : nullptr;
}

static bool is_reg_var_expr(const cexpr_t *e, int reg)
{
  e = skip_casts(e);
  if ( e == nullptr || e->op != cot_var )
    return false;

  const lvar_t &lv = e->v.getv();
  return lv.is_reg_var() && mreg2reg(lv.get_reg1(), lv.width) == reg;
}

static const cexpr_t *find_reg_var_expr(const citem_t *item, int reg)
{
  if ( item == nullptr )
    return nullptr;

  struct ida_local reg_var_finder_t : public ctree_visitor_t
  {
    int reg = -1;
    const cexpr_t *found = nullptr;

    explicit reg_var_finder_t(int r) : ctree_visitor_t(CV_FAST), reg(r) {}

    int idaapi visit_expr(cexpr_t *expr) override
    {
      if ( is_reg_var_expr(expr, reg) )
      {
        found = expr;
        return 1;
      }
      return 0;
    }
  };

  reg_var_finder_t finder(reg);
  finder.apply_to_exprs(const_cast<citem_t *>(item), nullptr);
  return finder.found;
}

static cexpr_t *make_helper_call_expr(
        const char *helper_name,
        const tinfo_t &ret_type,
        ea_t ea,
        cexpr_t *arg0=nullptr,
        cexpr_t *arg1=nullptr,
        cexpr_t *arg2=nullptr)
{
  if ( helper_name == nullptr )
  {
    delete arg0;
    delete arg1;
    delete arg2;
    return nullptr;
  }

  carglist_t *args = new carglist_t();
  args->flags |= CFL_HELPER;

  auto append_arg = [&](cexpr_t *arg)
  {
    if ( arg == nullptr )
      return;
    carg_t &call_arg = args->push_back();
    call_arg.consume_cexpr(arg);
    call_arg.ea = ea;
  };

  append_arg(arg0);
  append_arg(arg1);
  append_arg(arg2);
  cexpr_t *call = call_helper(ret_type, args, "%s", helper_name);
  if ( call == nullptr )
  {
    delete args;
    return nullptr;
  }
  call->ea = ea;
  return call;
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
  if ( dst == nullptr || value == nullptr )
  {
    delete dst;
    delete value;
    return nullptr;
  }

  value->type = dst->type;
  cexpr_t *asg = new cexpr_t(cot_asg, dst, value);
  asg->ea = ea;
  asg->type = dst->type;
  asg->calc_type(true);
  return asg;
}

static cexpr_t *make_assign_expr(cexpr_t *dst, cexpr_t *value, ea_t ea)
{
  if ( dst == nullptr || value == nullptr )
  {
    delete dst;
    delete value;
    return nullptr;
  }

  cexpr_t *asg = new cexpr_t(cot_asg, dst, value);
  asg->ea = ea;
  asg->type = dst->type;
  asg->calc_type(true);
  return asg;
}

static cexpr_t *make_int_const_expr(cfunc_t *cfunc, uint64 value, ea_t ea)
{
  cexpr_t *expr = make_num(value, cfunc, ea);
  if ( expr != nullptr )
    expr->ea = ea;
  return expr;
}

static cexpr_t *make_cast_expr(cexpr_t *expr, const tinfo_t &type, ea_t ea)
{
  if ( expr == nullptr )
    return nullptr;
  if ( expr->type.equals_to(type) )
    return expr;

  cexpr_t *cast = new cexpr_t(cot_cast, expr);
  cast->type = type;
  cast->ea = ea;
  return cast;
}

static bool split_pointer_base_offset(const cexpr_t **out_base, int *out_byte_off, const cexpr_t *expr)
{
  if ( out_base == nullptr || out_byte_off == nullptr )
    return false;

  expr = skip_casts(expr);
  if ( expr == nullptr )
    return false;

  *out_base = expr;
  *out_byte_off = 0;
  if ( expr->op != cot_add && expr->op != cot_sub )
    return true;
  if ( expr->x == nullptr || expr->y == nullptr )
    return false;

  const cexpr_t *rhs = skip_casts(expr->y);
  uint64 units = 0;
  if ( rhs == nullptr || !rhs->get_const_value(&units) || units > uint64(INT_MAX) )
    return true;

  int scale = 1;
  const cexpr_t *lhs = skip_casts(expr->x);
  if ( lhs != nullptr && lhs->type.is_ptr() )
  {
    const int stride = pointer_stride_bytes(lhs->type);
    if ( stride > 0 )
      scale = stride;
  }

  *out_base = expr->x;
  *out_byte_off = int(units) * scale;
  if ( expr->op == cot_sub )
    *out_byte_off = -*out_byte_off;
  return true;
}

static cexpr_t *make_lvar_expr(cfunc_t *cfunc, const lvar_t &lv, ea_t ea)
{
  lvars_t *lvars = cfunc != nullptr ? cfunc->get_lvars() : nullptr;
  if ( cfunc == nullptr || cfunc->mba == nullptr || lvars == nullptr )
    return nullptr;

  int idx = -1;
  for ( int i = 0; i < lvars->size(); ++i )
  {
    if ( &(*lvars)[i] == &lv )
    {
      idx = i;
      break;
    }
  }
  if ( idx < 0 )
    return nullptr;

  cexpr_t *expr = new cexpr_t();
  expr->op = cot_var;
  expr->v.mba = cfunc->mba;
  expr->v.idx = idx;
  expr->refwidth = lv.width;
  expr->type = lv.tif;
  expr->ea = ea;
  return expr;
}

static bool extract_stack_lvalue_stkoff(const cexpr_t *expr, sval_t *out_stkoff)
{
  if ( out_stkoff == nullptr )
    return false;

  expr = skip_casts(expr);
  if ( expr == nullptr )
    return false;

  if ( expr->op == cot_var )
  {
    const lvar_t &lv = expr->v.getv();
    if ( !lv.is_stk_var() )
      return false;
    *out_stkoff = lv.get_stkoff();
    return true;
  }

  if ( expr->op == cot_memref && expr->x != nullptr )
  {
    sval_t base_off = 0;
    if ( !extract_stack_lvalue_stkoff(expr->x, &base_off) )
      return false;
    *out_stkoff = base_off + sval_t(expr->m);
    return true;
  }

  return false;
}

static bool extract_stack_address_stkoff(const cexpr_t *expr, sval_t *out_stkoff)
{
  if ( out_stkoff == nullptr )
    return false;

  expr = skip_casts(expr);
  if ( expr == nullptr )
    return false;
  if ( expr->op == cot_ref && expr->x != nullptr )
  {
    return extract_stack_lvalue_stkoff(expr->x, out_stkoff);
  }

  if ( expr->op == cot_var )
  {
    const lvar_t &lv = expr->v.getv();
    if ( !lv.is_stk_var() || !lv.tif.is_array() )
      return false;
    *out_stkoff = lv.get_stkoff();
    return true;
  }

  return false;
}

static int score_stack_pointer_lvar(const lvar_t &lv)
{
  int score = 0;
  if ( lv.tif.is_array() )
    score += 16;
  else if ( lv.tif.is_udt() )
    score += 8;
  else if ( lv.width > 1 )
    score += 4;
  if ( !lv.is_arg_var() )
    score += 4;
  if ( lv.is_used_byref() )
    score += 2;
  if ( !lv.has_regname() )
    score += 1;
  if ( lv.is_overlapped_var() )
    score -= 4;
  return score;
}

static const lvar_t *find_best_stack_lvar_at_offset(cfunc_t *cfunc, sval_t stkoff)
{
  lvars_t *lvars = cfunc != nullptr ? cfunc->get_lvars() : nullptr;
  if ( lvars == nullptr )
    return nullptr;

  const lvar_t *best = nullptr;
  int best_score = 0;
  for ( lvar_t &lv : *lvars )
  {
    if ( !lv.is_stk_var() || lv.get_stkoff() != stkoff )
      continue;

    const int score = score_stack_pointer_lvar(lv);
    if ( best == nullptr || score > best_score )
    {
      best = &lv;
      best_score = score;
    }
  }

  return best;
}

static cexpr_t *build_stack_lvar_address_expr(cfunc_t *cfunc, const lvar_t &lv, ea_t ea)
{
  cexpr_t *var_expr = make_lvar_expr(cfunc, lv, ea);
  if ( var_expr == nullptr )
    return nullptr;
  if ( lv.tif.is_array() )
    return var_expr;

  cexpr_t *ref_expr = new cexpr_t(cot_ref, var_expr);
  ref_expr->ea = ea;
  ref_expr->calc_type(true);
  return ref_expr;
}

static cexpr_t *try_build_stack_pointer_expr(
        cfunc_t *cfunc,
        const cexpr_t *base,
        int byte_off,
        ea_t ea)
{
  sval_t base_off = 0;
  if ( !extract_stack_address_stkoff(base, &base_off) )
    return nullptr;

  const sval_t target_off = base_off + byte_off;
  const lvar_t *target_lv = find_best_stack_lvar_at_offset(cfunc, target_off);
  if ( target_lv == nullptr )
    return nullptr;

  return build_stack_lvar_address_expr(cfunc, *target_lv, ea);
}

static cexpr_t *build_pointer_offset_expr(
        cfunc_t *cfunc,
        const cexpr_t *base,
        const tinfo_t &ptr_type,
        int byte_off,
        ea_t ea);

static bool get_signed_const_value(const cexpr_t *expr, int64 *out_value)
{
  if ( out_value == nullptr )
    return false;

  expr = skip_casts(expr);
  if ( expr == nullptr || expr->op != cot_num )
    return false;

  *out_value = int64(expr->numval());
  return true;
}

static cexpr_t *try_build_container_pointer_expr(
        cfunc_t *cfunc,
        const cexpr_t *base,
        int byte_off,
        ea_t ea)
{
  base = skip_casts(base);
  if ( base == nullptr || base->op != cot_ref || base->x == nullptr )
    return nullptr;

  const cexpr_t *lvalue = skip_casts(base->x);
  if ( lvalue == nullptr )
    return nullptr;

  const cexpr_t *pointer_expr = nullptr;
  tinfo_t container_type;
  int member_off = 0;
  int64 container_index_units = 0;
  bool have_container_index = false;
  if ( lvalue->op == cot_memref && lvalue->x != nullptr )
  {
    const cexpr_t *container_lvalue = skip_casts(lvalue->x);
    if ( container_lvalue == nullptr )
      return nullptr;
    container_type = container_lvalue->type;
    member_off = int(lvalue->m);

    if ( container_lvalue->op == cot_ptr && container_lvalue->x != nullptr )
      pointer_expr = skip_casts(container_lvalue->x);
    else if ( container_lvalue->op == cot_idx
           && container_lvalue->x != nullptr
           && container_lvalue->y != nullptr )
    {
      pointer_expr = skip_casts(container_lvalue->x);
      if ( !get_signed_const_value(container_lvalue->y, &container_index_units) )
        return nullptr;
      have_container_index = true;
    }
  }
  else if ( lvalue->op == cot_memptr && lvalue->x != nullptr )
  {
    pointer_expr = skip_casts(lvalue->x);
    if ( pointer_expr == nullptr || !pointer_expr->type.is_ptr() )
      return nullptr;
    container_type = remove_pointer(pointer_expr->type);
    member_off = int(lvalue->m);
  }
  else
  {
    return nullptr;
  }

  const size_t obj_size = container_type.get_size();
  if ( pointer_expr == nullptr
    || !pointer_expr->type.is_ptr()
    || obj_size == BADSIZE
    || obj_size == 0
    || obj_size > size_t(INT_MAX) )
  {
    return nullptr;
  }

  const int total_off = member_off + byte_off;
  const int obj_size_int = int(obj_size);
  if ( total_off % obj_size_int != 0 )
    return nullptr;

  int container_index_byte_off = 0;
  if ( have_container_index )
  {
    const int64 index_byte_off = container_index_units * int64(obj_size_int);
    if ( index_byte_off < INT_MIN || index_byte_off > INT_MAX )
      return nullptr;
    container_index_byte_off = int(index_byte_off);
  }

  const cexpr_t *ptr_base = nullptr;
  int ptr_byte_off = 0;
  if ( !split_pointer_base_offset(&ptr_base, &ptr_byte_off, pointer_expr) )
    return nullptr;

  return build_pointer_offset_expr(
          cfunc,
          ptr_base,
          pointer_expr->type,
          ptr_byte_off + container_index_byte_off + total_off,
          ea);
}

static cexpr_t *build_pointer_offset_expr(
        cfunc_t *cfunc,
        const cexpr_t *base,
        const tinfo_t &ptr_type,
        int byte_off,
        ea_t ea)
{
  if ( cexpr_t *stack_expr = try_build_stack_pointer_expr(cfunc, base, byte_off, ea) )
    return stack_expr;
  if ( cexpr_t *container_expr = try_build_container_pointer_expr(cfunc, base, byte_off, ea) )
    return container_expr;

  cexpr_t *expr = clone_expr(base);
  if ( expr == nullptr )
    return nullptr;
  if ( byte_off == 0 )
    return expr;

  int units = byte_off;
  tinfo_t use_type = ptr_type;
  const int stride = pointer_stride_bytes(ptr_type);
  if ( stride <= 0 || byte_off % stride != 0 )
  {
    tinfo_t char_type(BTF_CHAR);
    if ( !use_type.create_ptr(char_type) )
    {
      delete expr;
      return nullptr;
    }
  }
  else
  {
    units = byte_off / stride;
  }

  expr = make_cast_expr(expr, use_type, ea);
  cexpr_t *delta = make_int_const_expr(cfunc, qabs(units), ea);
  if ( expr == nullptr || delta == nullptr )
  {
    delete expr;
    delete delta;
    return nullptr;
  }

  cexpr_t *adjusted = new cexpr_t(units >= 0 ? cot_add : cot_sub, expr, delta);
  adjusted->ea = ea;
  adjusted->calc_type(true);
  return adjusted;
}

static cexpr_t *build_copy_start_expr(
        cfunc_t *cfunc,
        const cexpr_t *init_rhs,
        const tinfo_t &ptr_type,
        int advance_bytes,
        ea_t ea,
        int *out_init_byte_off=nullptr)
{
  const cexpr_t *base = nullptr;
  int init_byte_off = 0;
  if ( !split_pointer_base_offset(&base, &init_byte_off, init_rhs) )
    return nullptr;
  if ( out_init_byte_off != nullptr )
    *out_init_byte_off = init_byte_off;
  return build_pointer_offset_expr(cfunc, base, ptr_type, init_byte_off + advance_bytes, ea);
}

static cexpr_t *build_copy_size_expr(cfunc_t *cfunc, const cexpr_t *count_rhs, int elem_width, ea_t ea)
{
  if ( count_rhs == nullptr || elem_width <= 0 )
    return nullptr;

  uint64 count = 0;
  if ( count_rhs->get_const_value(&count) )
    return make_int_const_expr(cfunc, count * uint64(elem_width), ea);

  if ( elem_width == 1 )
    return clone_expr(count_rhs);

  cexpr_t *mul = new cexpr_t(cot_mul, clone_expr(count_rhs), make_int_const_expr(cfunc, elem_width, ea));
  mul->ea = ea;
  mul->calc_type(true);
  return mul;
}

static bool same_effect_expr(const cexpr_t *lhs, const cexpr_t *rhs)
{
  lhs = skip_casts(lhs);
  rhs = skip_casts(rhs);
  return lhs != nullptr && rhs != nullptr && lhs->equal_effect(*rhs);
}

static cexpr_t *build_copy_base_from_end_expr(
        cfunc_t *cfunc,
        const cexpr_t *init_rhs,
        const cexpr_t *count_rhs,
        const tinfo_t &ptr_type,
        int elem_width,
        ea_t ea)
{
  if ( cfunc == nullptr || init_rhs == nullptr || count_rhs == nullptr || elem_width <= 0 )
    return nullptr;

  cexpr_t *scaled_count = ptr_type.is_ptr() ? clone_expr(count_rhs) : build_copy_size_expr(cfunc, count_rhs, elem_width, ea);
  if ( scaled_count == nullptr )
    return nullptr;

  const cexpr_t *expr = skip_casts(init_rhs);
  if ( expr != nullptr && expr->op == cot_add && expr->x != nullptr && expr->y != nullptr )
  {
    if ( same_effect_expr(expr->y, scaled_count) )
    {
      delete scaled_count;
      return build_pointer_offset_expr(cfunc, expr->x, ptr_type, 0, ea);
    }
    if ( same_effect_expr(expr->x, scaled_count) )
    {
      delete scaled_count;
      return build_pointer_offset_expr(cfunc, expr->y, ptr_type, 0, ea);
    }
  }

  delete scaled_count;

  uint64 count = 0;
  if ( !count_rhs->get_const_value(&count) || count > uint64(INT_MAX / elem_width) )
    return nullptr;
  return build_pointer_offset_expr(cfunc, init_rhs, ptr_type, -int(count) * elem_width, ea);
}

static bool make_memory_copy_types(
        const char *decl,
        tinfo_t *out_func_type,
        tinfo_t *out_func_ptr_type,
        tinfo_t *out_ret_type)
{
  tinfo_t func_type;
  if ( !parse_decl(&func_type, nullptr, nullptr, decl, PT_TYP | PT_SIL | PT_SEMICOLON) )
    return false;

  if ( out_func_type != nullptr )
    *out_func_type = func_type;
  if ( out_ret_type != nullptr )
    *out_ret_type = func_type.get_rettype();
  if ( out_func_ptr_type != nullptr && !out_func_ptr_type->create_ptr(func_type) )
    return false;
  return true;
}

static ea_t find_external_name_ea(const char *name)
{
  if ( name == nullptr || *name == '\0' )
    return BADADDR;

  const ea_t ea = get_name_ea(BADADDR, name);
  if ( ea == BADADDR )
    return BADADDR;

  const segment_t *seg = getseg(ea);
  if ( seg == nullptr || seg->type != SEG_XTRN )
    return BADADDR;

  return ea;
}

static cexpr_t *make_memory_copy_call_expr(
        const char *name,
        const char *decl,
        cexpr_t *dst,
        cexpr_t *src,
        cexpr_t *size,
        ea_t ea)
{
  if ( dst == nullptr || src == nullptr || size == nullptr )
  {
    delete dst;
    delete src;
    delete size;
    return nullptr;
  }

  tinfo_t func_type;
  tinfo_t func_ptr_type;
  tinfo_t ret_type;
  if ( !make_memory_copy_types(decl, &func_type, &func_ptr_type, &ret_type) )
  {
    delete dst;
    delete src;
    delete size;
    return nullptr;
  }

  cexpr_t *callee = new cexpr_t();
  const ea_t callee_ea = find_external_name_ea(name);
  const bool is_helper = callee_ea == BADADDR;
  if ( is_helper )
  {
    callee->op = cot_helper;
    callee->helper = qstrdup(name);
    callee->type = func_ptr_type;
    callee->ea = ea;
  }
  else
  {
    callee->op = cot_obj;
    callee->obj_ea = callee_ea;
    callee->type = func_ptr_type;
    callee->ea = ea;
  }

  cexpr_t *call = new cexpr_t();
  call->op = cot_call;
  call->x = callee;
  call->a = new carglist_t();
  call->a->functype = func_type;
  if ( is_helper )
    call->a->flags |= CFL_HELPER;
  call->type = ret_type;
  call->ea = ea;

  auto append_arg = [&](cexpr_t *arg, int argnum)
  {
    tinfo_t formal_type = func_type.get_nth_arg(argnum);
    carg_t &call_arg = call->a->push_back();
    call_arg.consume_cexpr(arg);
    call_arg.ea = ea;
    call_arg.formal_type = formal_type;
    return true;
  };

  if ( !append_arg(dst, 0) || !append_arg(src, 1) || !append_arg(size, 2) )
  {
    delete call;
    return nullptr;
  }
  call->calc_type(true);
  return call;
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

struct pointer_access_t
{
  var_ref_t var;
  tinfo_t var_type;
  int access_size = 0;
  int embedded_advance = 0;
};

struct pointer_increment_t
{
  var_ref_t var;
  int byte_delta = 0;
};

enum inline_copy_call_kind_t
{
  INLINE_COPY_CALL_NONE,
  INLINE_COPY_CALL_MEMCPY,
  INLINE_COPY_CALL_MEMMOVE,
};

struct inline_copy_loop_t
{
  var_ref_t src_var;
  var_ref_t dst_var;
  var_ref_t count_var;
  tinfo_t src_ptr_type;
  tinfo_t dst_ptr_type;
  int width = 0;
  int src_advance = 0;
  int dst_advance = 0;
};

struct inline_copy_match_t
{
  cblock_t::iterator src_init_it;
  cblock_t::iterator dst_init_it;
  cblock_t::iterator count_init_it;
  inline_copy_loop_t loop;
  const cexpr_t *src_init_rhs = nullptr;
  const cexpr_t *dst_init_rhs = nullptr;
  const cexpr_t *count_init_rhs = nullptr;
  cexpr_t *dst_arg = nullptr;
  cexpr_t *src_arg = nullptr;
  cexpr_t *size_arg = nullptr;
  cexpr_t *call_expr = nullptr;
  inline_copy_call_kind_t call_kind = INLINE_COPY_CALL_NONE;
  ea_t ea = BADADDR;
};

static void cleanup_inline_copy_match(inline_copy_match_t *match)
{
  if ( match == nullptr )
    return;
  delete match->dst_arg;
  delete match->src_arg;
  delete match->size_arg;
  delete match->call_expr;
  match->dst_arg = nullptr;
  match->src_arg = nullptr;
  match->size_arg = nullptr;
  match->call_expr = nullptr;
}

static bool item_has_label(const citem_t *item);

static bool decode_pointer_access(pointer_access_t *out, const cexpr_t *expr)
{
  expr = skip_casts(expr);
  if ( out == nullptr || expr == nullptr || expr->op != cot_ptr || expr->x == nullptr )
    return false;
  if ( expr->ptrsize != 1 && expr->ptrsize != 2 && expr->ptrsize != 4 && expr->ptrsize != 8 )
    return false;

  const cexpr_t *base = skip_casts(expr->x);
  if ( base == nullptr )
    return false;

  int embedded_advance = 0;
  const cexpr_t *var_expr = base;
  if ( base->op == cot_preinc || base->op == cot_postinc || base->op == cot_predec || base->op == cot_postdec )
  {
    if ( base->x == nullptr )
      return false;
    var_expr = base->x;
    embedded_advance = pointer_step_bytes(var_expr->type);
    if ( embedded_advance <= 0 )
      return false;
    if ( base->op == cot_predec || base->op == cot_postdec )
      embedded_advance = -embedded_advance;
  }

  if ( !get_var_ref(var_expr, &out->var) )
    return false;

  out->var_type = var_expr->type;
  out->access_size = expr->ptrsize;
  out->embedded_advance = embedded_advance;
  return true;
}

static bool decode_pointer_increment(pointer_increment_t *out, const cexpr_t *expr)
{
  expr = skip_casts(expr);
  if ( out == nullptr || expr == nullptr )
    return false;

  if ( expr->op == cot_preinc || expr->op == cot_postinc || expr->op == cot_predec || expr->op == cot_postdec )
  {
    if ( expr->x == nullptr || !get_var_ref(expr->x, &out->var) )
      return false;
    out->byte_delta = pointer_step_bytes(expr->x->type);
    if ( expr->op == cot_predec || expr->op == cot_postdec )
      out->byte_delta = -out->byte_delta;
    return out->byte_delta != 0;
  }

  if ( (expr->op != cot_asgadd && expr->op != cot_asgsub)
    || expr->x == nullptr
    || expr->y == nullptr
    || !get_var_ref(expr->x, &out->var) )
  {
    return false;
  }

  uint64 units = 0;
  const cexpr_t *rhs = skip_casts(expr->y);
  if ( rhs == nullptr || !rhs->get_const_value(&units) || units == 0 || units > uint64(INT_MAX) )
    return false;

  int scale = 1;
  if ( expr->x->type.is_ptr() )
  {
    scale = pointer_step_bytes(expr->x->type, -1);
    if ( scale <= 0 )
      return false;
  }

  out->byte_delta = int(units) * scale;
  if ( expr->op == cot_asgsub )
    out->byte_delta = -out->byte_delta;
  return out->byte_delta != 0;
}

static bool decode_inline_copy_loop(inline_copy_loop_t *out, const cinsn_t &ins)
{
  if ( out == nullptr || ins.op != cit_do || ins.cdo == nullptr || ins.cdo->body == nullptr )
    return false;
  if ( item_has_label(&ins) || item_has_label(ins.cdo->body) )
    return false;
  if ( !get_var_ref(&ins.cdo->expr, &out->count_var) )
    return false;

  cinsn_t *body = ins.cdo->body;
  if ( body->op != cit_block || body->cblock == nullptr || body->cblock->size() < 2 || body->cblock->size() > 4 )
    return false;

  cblock_t::iterator last = body->cblock->end();
  --last;
  if ( last->op != cit_expr || last->cexpr == nullptr || last->cexpr->op != cot_predec || last->cexpr->x == nullptr )
    return false;
  if ( !is_var_expr(last->cexpr->x, out->count_var) )
    return false;

  qvector<pointer_increment_t> increments;
  pointer_access_t dst_access;
  pointer_access_t src_access;
  bool seen_assign = false;

  for ( cblock_t::iterator it = body->cblock->begin(); it != last; ++it )
  {
    if ( it->op != cit_expr || it->cexpr == nullptr )
      return false;

    cexpr_t *expr = it->cexpr;
    if ( expr->op == cot_asg )
    {
      if ( seen_assign || expr->x == nullptr || expr->y == nullptr )
        return false;
      if ( !decode_pointer_access(&dst_access, expr->x) || !decode_pointer_access(&src_access, expr->y) )
        return false;
      if ( dst_access.access_size != src_access.access_size )
        return false;
      seen_assign = true;
      continue;
    }

    if ( seen_assign )
      return false;

    pointer_increment_t inc;
    if ( !decode_pointer_increment(&inc, expr) )
      return false;
    increments.push_back(inc);
  }

  if ( !seen_assign )
    return false;
  if ( same_var_ref(dst_access.var, src_access.var)
    || same_var_ref(dst_access.var, out->count_var)
    || same_var_ref(src_access.var, out->count_var) )
  {
    return false;
  }

  out->dst_var = dst_access.var;
  out->src_var = src_access.var;
  out->dst_ptr_type = dst_access.var_type;
  out->src_ptr_type = src_access.var_type;
  out->width = dst_access.access_size;
  out->dst_advance = dst_access.embedded_advance;
  out->src_advance = src_access.embedded_advance;

  for ( const pointer_increment_t &inc : increments )
  {
    if ( same_var_ref(inc.var, out->dst_var) )
      out->dst_advance += inc.byte_delta;
    else if ( same_var_ref(inc.var, out->src_var) )
      out->src_advance += inc.byte_delta;
    else
      return false;
  }

  return qabs(out->src_advance) == out->width
      && out->src_advance == out->dst_advance;
}

static bool item_contains_var_ref(const citem_t *item, const var_ref_t &var)
{
  if ( item == nullptr )
    return false;

  struct ida_local var_ref_finder_t : public ctree_visitor_t
  {
    const var_ref_t &wanted;
    bool found = false;

    explicit var_ref_finder_t(const var_ref_t &v) : ctree_visitor_t(CV_FAST), wanted(v) {}

    int idaapi visit_expr(cexpr_t *expr) override
    {
      if ( expr->op == cot_var && same_var_ref(expr->v, wanted) )
      {
        found = true;
        return 1;
      }
      return 0;
    }
  };

  var_ref_finder_t finder(var);
  finder.apply_to_exprs(const_cast<citem_t *>(item), nullptr);
  return finder.found;
}

static bool item_has_label(const citem_t *item)
{
  return item != nullptr && (item->label_num != -1 || item->contains_label());
}

static bool decode_var_init_stmt(const cinsn_t &ins, const var_ref_t &var, const cexpr_t **out_rhs)
{
  if ( ins.op != cit_expr || ins.cexpr == nullptr || ins.cexpr->op != cot_asg || ins.cexpr->x == nullptr || ins.cexpr->y == nullptr )
    return false;
  if ( !is_var_expr(ins.cexpr->x, var) || item_contains_var_ref(ins.cexpr->y, var) || ins.cexpr->y->has_side_effects() )
    return false;
  if ( out_rhs != nullptr )
    *out_rhs = ins.cexpr->y;
  return true;
}

static bool find_last_clean_var_init(
        cblock_t *block,
        cblock_t::iterator loop_it,
        const var_ref_t &var,
        cblock_t::iterator *out_it,
        const cexpr_t **out_rhs)
{
  if ( block == nullptr || out_it == nullptr || out_rhs == nullptr )
    return false;

  cblock_t::iterator it = loop_it;
  while ( it != block->begin() )
  {
    --it;
    if ( !item_contains_var_ref(&*it, var) )
      continue;
    if ( !decode_var_init_stmt(*it, var, out_rhs) )
      return false;
    *out_it = it;
    return true;
  }
  return false;
}

static bool vars_live_after_loop(
        cblock_t *block,
        cblock_t::iterator loop_it,
        const var_ref_t &src_var,
        const var_ref_t &dst_var,
        const var_ref_t &count_var)
{
  if ( block == nullptr )
    return true;

  cblock_t::iterator it = loop_it;
  ++it;
  for ( ; it != block->end(); ++it )
  {
    if ( item_contains_var_ref(&*it, src_var)
      || item_contains_var_ref(&*it, dst_var)
      || item_contains_var_ref(&*it, count_var) )
    {
      return true;
    }
  }
  return false;
}

static bool match_inline_copy(
        inline_copy_match_t *out,
        cfunc_t *cfunc,
        cblock_t *block,
        cblock_t::iterator loop_it,
        inline_copy_call_kind_t required_kind=INLINE_COPY_CALL_NONE)
{
  if ( out == nullptr || cfunc == nullptr || block == nullptr )
    return false;
  if ( loop_it->op != cit_do )
    return false;

  inline_copy_loop_t loop;
  if ( !decode_inline_copy_loop(&loop, *loop_it)
    || vars_live_after_loop(block, loop_it, loop.src_var, loop.dst_var, loop.count_var) )
    return false;

  const cexpr_t *src_init_rhs = nullptr;
  const cexpr_t *dst_init_rhs = nullptr;
  const cexpr_t *count_init_rhs = nullptr;
  if ( !find_last_clean_var_init(block, loop_it, loop.src_var, &out->src_init_it, &src_init_rhs)
    || !find_last_clean_var_init(block, loop_it, loop.dst_var, &out->dst_init_it, &dst_init_rhs)
    || !find_last_clean_var_init(block, loop_it, loop.count_var, &out->count_init_it, &count_init_rhs) )
    return false;

  if ( out->src_init_it == out->dst_init_it
    || out->src_init_it == out->count_init_it
    || out->dst_init_it == out->count_init_it )
    return false;
  if ( item_has_label(&*out->src_init_it)
    || item_has_label(&*out->dst_init_it)
    || item_has_label(&*out->count_init_it) )
    return false;

  out->loop = loop;
  out->src_init_rhs = src_init_rhs;
  out->dst_init_rhs = dst_init_rhs;
  out->count_init_rhs = count_init_rhs;
  out->ea = loop_it->ea;

  cexpr_t *copy_size = build_copy_size_expr(cfunc, count_init_rhs, loop.width, loop_it->ea);
  if ( copy_size == nullptr )
    return false;

  int src_init_off = 0;
  int dst_init_off = 0;
  cexpr_t *src_start = nullptr;
  cexpr_t *dst_start = nullptr;
  inline_copy_call_kind_t call_kind = INLINE_COPY_CALL_NONE;

  if ( loop.src_advance == loop.width && loop.dst_advance == loop.width )
  {
    src_start = build_copy_start_expr(cfunc, src_init_rhs, loop.src_ptr_type, loop.src_advance, loop_it->ea, &src_init_off);
    dst_start = build_copy_start_expr(cfunc, dst_init_rhs, loop.dst_ptr_type, loop.dst_advance, loop_it->ea, &dst_init_off);
    call_kind = (src_init_off == -loop.src_advance && dst_init_off == -loop.dst_advance)
              ? INLINE_COPY_CALL_MEMMOVE
              : INLINE_COPY_CALL_MEMCPY;
  }
  else if ( loop.src_advance == -loop.width && loop.dst_advance == -loop.width )
  {
    src_start = build_copy_base_from_end_expr(cfunc, src_init_rhs, count_init_rhs, loop.src_ptr_type, loop.width, loop_it->ea);
    dst_start = build_copy_base_from_end_expr(cfunc, dst_init_rhs, count_init_rhs, loop.dst_ptr_type, loop.width, loop_it->ea);
    call_kind = INLINE_COPY_CALL_MEMMOVE;
  }

  if ( src_start == nullptr || dst_start == nullptr || call_kind == INLINE_COPY_CALL_NONE )
  {
    delete src_start;
    delete dst_start;
    delete copy_size;
    return false;
  }

  if ( required_kind != INLINE_COPY_CALL_NONE && call_kind != required_kind )
  {
    delete src_start;
    delete dst_start;
    delete copy_size;
    return false;
  }

  out->dst_arg = dst_start;
  out->src_arg = src_start;
  out->size_arg = copy_size;

  if ( call_kind == INLINE_COPY_CALL_MEMCPY )
  {
    out->call_expr = make_memory_copy_call_expr(
            "memcpy",
            "void *memcpy(void *, const void *, unsigned int);",
            clone_expr(out->dst_arg),
            clone_expr(out->src_arg),
            clone_expr(out->size_arg),
            loop_it->ea);
  }
  else
  {
    out->call_expr = make_memory_copy_call_expr(
            "memmove",
            "void *memmove(void *, const void *, unsigned int);",
            clone_expr(out->dst_arg),
            clone_expr(out->src_arg),
            clone_expr(out->size_arg),
            loop_it->ea);
  }
  if ( out->call_expr == nullptr )
  {
    cleanup_inline_copy_match(out);
    return false;
  }

  out->call_kind = call_kind;
  return true;
}

static bool match_inline_memmove_if(cexpr_t **out_call_expr, ea_t *out_ea, cfunc_t *cfunc, const cinsn_t &ins)
{
  if ( out_call_expr == nullptr || out_ea == nullptr || cfunc == nullptr || ins.op != cit_if || ins.cif == nullptr )
    return false;
  if ( ins.cif->ithen == nullptr || ins.cif->ielse == nullptr )
    return false;
  if ( ins.cif->ithen->op != cit_block || ins.cif->ithen->cblock == nullptr )
    return false;
  if ( ins.cif->ielse->op != cit_block || ins.cif->ielse->cblock == nullptr )
    return false;
  if ( ins.cif->ithen->cblock->empty() || ins.cif->ielse->cblock->empty() )
    return false;

  cblock_t::iterator then_loop_it = ins.cif->ithen->cblock->end();
  cblock_t::iterator else_loop_it = ins.cif->ielse->cblock->end();
  --then_loop_it;
  --else_loop_it;

  inline_copy_match_t then_match;
  inline_copy_match_t else_match;
  if ( !match_inline_copy(&then_match, cfunc, ins.cif->ithen->cblock, then_loop_it, INLINE_COPY_CALL_MEMMOVE)
    || !match_inline_copy(&else_match, cfunc, ins.cif->ielse->cblock, else_loop_it, INLINE_COPY_CALL_MEMMOVE) )
  {
    cleanup_inline_copy_match(&then_match);
    cleanup_inline_copy_match(&else_match);
    return false;
  }

  if ( then_match.dst_arg == nullptr
    || then_match.src_arg == nullptr
    || then_match.size_arg == nullptr
    || else_match.dst_arg == nullptr
    || else_match.src_arg == nullptr
    || else_match.size_arg == nullptr
    || !same_effect_expr(then_match.dst_arg, else_match.dst_arg)
    || !same_effect_expr(then_match.src_arg, else_match.src_arg)
    || !same_effect_expr(then_match.size_arg, else_match.size_arg) )
  {
    cleanup_inline_copy_match(&then_match);
    cleanup_inline_copy_match(&else_match);
    return false;
  }

  delete then_match.dst_arg;
  delete then_match.src_arg;
  delete then_match.size_arg;
  then_match.dst_arg = nullptr;
  then_match.src_arg = nullptr;
  then_match.size_arg = nullptr;
  cleanup_inline_copy_match(&else_match);
  *out_call_expr = then_match.call_expr;
  *out_ea = ins.ea;
  return true;
}

static void rewrite_inline_memmove_conditionals(cfunc_t *cfunc)
{
  bool changed = false;
  do
  {
    struct ida_local inline_memmove_if_rewriter_t : public ctree_visitor_t
    {
      cfunc_t *cfunc = nullptr;
      bool changed = false;

      explicit inline_memmove_if_rewriter_t(cfunc_t *f) : ctree_visitor_t(CV_FAST | CV_INSNS | CV_POST), cfunc(f) {}

      int idaapi leave_insn(cinsn_t *ins) override
      {
        if ( cfunc == nullptr || ins->op != cit_block || ins->cblock == nullptr )
          return 0;

        for ( cblock_t::iterator it = ins->cblock->begin(); it != ins->cblock->end(); ++it )
        {
          cexpr_t *call_expr = nullptr;
          ea_t call_ea = BADADDR;
          if ( !match_inline_memmove_if(&call_expr, &call_ea, cfunc, *it) )
            continue;

          it->cleanup();
          it->op = cit_expr;
          it->cexpr = call_expr;
          it->ea = call_ea;
          changed = true;
          return 1;
        }
        return 0;
      }
    };

    inline_memmove_if_rewriter_t rewriter(cfunc);
    rewriter.apply_to(&cfunc->body, nullptr);
    changed = rewriter.changed;
  }
  while ( changed );
}

static void rewrite_inline_copy_loops(cfunc_t *cfunc)
{
  bool changed = false;
  do
  {
    struct ida_local inline_copy_rewriter_t : public ctree_visitor_t
    {
      cfunc_t *cfunc = nullptr;
      bool changed = false;

      explicit inline_copy_rewriter_t(cfunc_t *f) : ctree_visitor_t(CV_FAST | CV_INSNS | CV_POST), cfunc(f) {}

      int idaapi leave_insn(cinsn_t *ins) override
      {
        if ( cfunc == nullptr || ins->op != cit_block || ins->cblock == nullptr )
          return 0;

        for ( cblock_t::iterator it = ins->cblock->begin(); it != ins->cblock->end(); )
        {
          cblock_t::iterator loop_it = it++;
          inline_copy_match_t match;
          if ( !match_inline_copy(&match, cfunc, ins->cblock, loop_it) )
            continue;

          cblock_t::iterator inserted = ins->cblock->insert(it);
          inserted->op = cit_expr;
          inserted->cexpr = match.call_expr;
          inserted->ea = match.ea;
          match.call_expr = nullptr;

          ins->cblock->erase(loop_it);
          ins->cblock->erase(match.src_init_it);
          ins->cblock->erase(match.dst_init_it);
          ins->cblock->erase(match.count_init_it);
          cleanup_inline_copy_match(&match);
          changed = true;
          return 1;
        }
        return 0;
      }
    };

    inline_copy_rewriter_t rewriter(cfunc);
    rewriter.apply_to(&cfunc->body, nullptr);
    changed = rewriter.changed;
  }
  while ( changed );
}

struct atomic_lwarx_dcbst_t
{
  int load_reg = -1;
  int base_reg = -1;
  ea_t lwarx_ea = BADADDR;
  ea_t dcbst_ea = BADADDR;
};

struct atomic_stwcx_t
{
  int value_reg = -1;
  int base_reg = -1;
  ea_t stwcx_ea = BADADDR;
};

static bool decode_atomic_lwarx_dcbst(const cinsn_t &ins, atomic_lwarx_dcbst_t *out)
{
  if ( ins.op != cit_asm || ins.casm == nullptr || ins.casm->size() != 2 || out == nullptr )
    return false;

  insn_t lwarx;
  insn_t dcbst;
  if ( decode_insn(&lwarx, ins.casm->at(0)) <= 0 || decode_insn(&dcbst, ins.casm->at(1)) <= 0 )
    return false;

  if ( !has_mnem(lwarx, "lwarx")
    || !has_mnem(dcbst, "dcbst")
    || lwarx.Op1.type != o_reg
    || !is_imm_value(lwarx.Op2, 0)
    || lwarx.Op3.type != o_reg
    || !is_imm_value(dcbst.Op1, 0)
    || dcbst.Op2.type != o_reg
    || dcbst.Op2.reg != lwarx.Op3.reg )
  {
    return false;
  }

  out->load_reg = lwarx.Op1.reg;
  out->base_reg = lwarx.Op3.reg;
  out->lwarx_ea = lwarx.ea;
  out->dcbst_ea = dcbst.ea;
  return true;
}

static bool decode_atomic_stwcx(const cinsn_t &ins, atomic_stwcx_t *out)
{
  if ( ins.op != cit_asm || ins.casm == nullptr || ins.casm->size() != 1 || out == nullptr )
    return false;

  insn_t stwcx;
  if ( decode_insn(&stwcx, ins.casm->at(0)) <= 0 )
    return false;

  if ( !has_mnem(stwcx, "stwcx")
    || stwcx.Op1.type != o_reg
    || !is_imm_value(stwcx.Op2, 0)
    || stwcx.Op3.type != o_reg )
  {
    return false;
  }

  out->value_reg = stwcx.Op1.reg;
  out->base_reg = stwcx.Op3.reg;
  out->stwcx_ea = stwcx.ea;
  return true;
}

static bool replace_atomic_condition_expr(cexpr_t *cond, cexpr_t *call)
{
  if ( cond == nullptr || call == nullptr )
    return false;

  if ( cond->op == cot_lnot && cond->x != nullptr )
  {
    cond->x->replace_by(call);
    cond->calc_type(true);
    return true;
  }

  if ( (cond->op == cot_eq || cond->op == cot_ne) && cond->x != nullptr && cond->y != nullptr )
  {
    if ( is_zero_expr(cond->x) )
    {
      cond->y->replace_by(call);
      cond->calc_type(true);
      return true;
    }
    if ( is_zero_expr(cond->y) )
    {
      cond->x->replace_by(call);
      cond->calc_type(true);
      return true;
    }
  }

  cond->replace_by(call);
  cond->calc_type(true);
  return true;
}

static cinsn_t *make_block_insn(ea_t ea)
{
  cinsn_t *block = new cinsn_t();
  block->op = cit_block;
  block->cblock = new cblock_t();
  block->ea = ea;
  return block;
}

static void append_cloned_insn(cinsn_t *block, const cinsn_t &src)
{
  if ( block == nullptr || block->op != cit_block )
    return;

  cinsn_t &dst = block->new_insn(src.ea);
  dst = src;
}

static void append_expr_insn(cinsn_t *block, cexpr_t *expr, ea_t ea)
{
  if ( block == nullptr || block->op != cit_block )
  {
    delete expr;
    return;
  }

  cinsn_t &dst = block->new_insn(ea);
  dst.op = cit_expr;
  dst.cexpr = expr;
  dst.ea = ea;
}

static void rewrite_ppc_atomic_update_loops(cfunc_t *cfunc)
{
  struct ida_local atomic_loop_rewriter_t : public ctree_visitor_t
  {
    atomic_loop_rewriter_t() : ctree_visitor_t(CV_FAST | CV_INSNS) {}

    int idaapi visit_insn(cinsn_t *ins) override
    {
      if ( ins->op != cit_do || ins->cdo == nullptr || ins->cdo->body == nullptr )
        return 0;

      cinsn_t *body = ins->cdo->body;
      if ( body->op != cit_block || body->cblock == nullptr || body->cblock->size() != 4 )
        return 0;

      cblock_t::iterator p = body->cblock->begin();
      cinsn_t *base_assign = &*p++;
      cinsn_t *load_cache_asm = &*p++;
      cinsn_t *value_assign = &*p++;
      cinsn_t *store_asm = &*p;

      atomic_lwarx_dcbst_t load_cache;
      atomic_stwcx_t store;
      if ( !decode_atomic_lwarx_dcbst(*load_cache_asm, &load_cache)
        || !decode_atomic_stwcx(*store_asm, &store)
        || load_cache.base_reg != store.base_reg )
      {
        return 0;
      }

      if ( base_assign->op != cit_expr
        || base_assign->cexpr == nullptr
        || base_assign->cexpr->op != cot_asg
        || !is_reg_var_expr(base_assign->cexpr->x, load_cache.base_reg)
        || value_assign->op != cit_expr
        || value_assign->cexpr == nullptr
        || value_assign->cexpr->op != cot_asg
        || !is_reg_var_expr(value_assign->cexpr->x, store.value_reg) )
      {
        return 0;
      }

      const cexpr_t *load_expr = find_reg_var_expr(value_assign->cexpr->y, load_cache.load_reg);
      if ( load_expr == nullptr )
        return 0;

      tinfo_t u32_type;
      tinfo_t bool_type;
      tinfo_t void_type;
      make_u32_type(&u32_type);
      make_bool_type(&bool_type);
      make_void_type(&void_type);

      cexpr_t *lwarx_call = make_helper_call_expr(
              "__ppc_lwarx",
              u32_type,
              load_cache.lwarx_ea,
              clone_expr(base_assign->cexpr->x));
      cexpr_t *load_assign_expr = make_assign_expr(clone_expr(load_expr), lwarx_call, load_cache.lwarx_ea);
      cexpr_t *dcbst_call = make_helper_call_expr(
              "__ppc_dcbst",
              void_type,
              load_cache.dcbst_ea,
              clone_expr(base_assign->cexpr->x));
      cexpr_t *stwcx_call = make_helper_call_expr(
              "__ppc_stwcx",
              bool_type,
              store.stwcx_ea,
              clone_expr(base_assign->cexpr->x),
              clone_expr(value_assign->cexpr->x));
      if ( load_assign_expr == nullptr || dcbst_call == nullptr || stwcx_call == nullptr )
      {
        delete load_assign_expr;
        delete dcbst_call;
        delete stwcx_call;
        return 0;
      }

      if ( !replace_atomic_condition_expr(&ins->cdo->expr, stwcx_call) )
      {
        delete load_assign_expr;
        delete dcbst_call;
        delete stwcx_call;
        return 0;
      }

      cinsn_t *new_body = make_block_insn(body->ea);
      append_cloned_insn(new_body, *base_assign);
      append_expr_insn(new_body, load_assign_expr, load_cache.lwarx_ea);
      append_expr_insn(new_body, dcbst_call, load_cache.dcbst_ea);
      append_cloned_insn(new_body, *value_assign);

      delete ins->cdo->body;
      ins->cdo->body = new_body;
      return 0;
    }
  };

  atomic_loop_rewriter_t rewriter;
  rewriter.apply_to(&cfunc->body, nullptr);
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
      return false;

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
    if ( !full_fix_enabled )
      return MERR_INSN;

    auto early_or_helper = [&](merror_t err, const char *helper, int max_arg_qty) -> merror_t
    {
      if ( err == MERR_OK )
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

struct ui_listener_t : public event_listener_t
{
  plugin_ctx_t *ctx = nullptr;

  ssize_t idaapi on_event(ssize_t code, va_list va) override;
};

struct plugin_ctx_t : public plugmod_t, public event_listener_t, public ignore_micro_t, public function_gate_t
{
  ppc_ps_filter_t filter;
  const_type_toggle_action_t const_type_toggle;
  selection_mass_type_action_t selection_mass_type;
  always_fix_ah_t always_fix_ah;
  ui_listener_t ui_listener;
  bool always_fix = false;

  static ea_t function_start_for_ea(ea_t ea)
  {
    func_t *func = get_func(ea);
    return func != nullptr ? func->start_ea : BADADDR;
  }

  bool should_fix_function(ea_t func_ea) const
  {
    return func_ea != BADADDR && always_fix;
  }

  bool should_fix_ea(ea_t ea) const override
  {
    return should_fix_function(function_start_for_ea(ea));
  }

  void refresh_function(vdui_t *vu, ea_t func_ea)
  {
    if ( func_ea == BADADDR )
      return;
    mark_cfunc_dirty(func_ea, false);
    if ( vu != nullptr )
      vu->refresh_view(true);
    else
      mark_builtin_widgets(IWID_PSEUDOCODE);
  }

  void set_always_fix(bool enabled, vdui_t *vu=nullptr)
  {
    always_fix = enabled;
    save_always_fix_setting(enabled);
    update_action_checked(ALWAYS_FIX_ACTION_NAME, enabled);

    ea_t func_ea = BADADDR;
    if ( vu != nullptr && vu->cfunc != nullptr )
      func_ea = vu->cfunc->entry_ea;
    else
      func_ea = function_start_for_ea(get_screen_ea());
    refresh_function(vu, func_ea);
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
      {
        rewrite_ppc_atomic_update_loops(cfunc);
        rewrite_inline_memmove_conditionals(cfunc);
        rewrite_inline_copy_loops(cfunc);
        rewrite_ps_pair_assignments(cfunc);
      }
    }
    else if ( event == hxe_populating_popup )
    {
      TWidget *widget = va_arg(va, TWidget *);
      TPopupMenu *popup_handle = va_arg(va, TPopupMenu *);
      vdui_t *vu = va_arg(va, vdui_t *);
      if ( vu != nullptr )
      {
        attach_action_to_popup(widget, popup_handle, TOGGLE_CONST_ACTION_NAME, nullptr, SETMENU_APP);
      }
    }
    return 0;
  }

  plugin_ctx_t()
  {
    always_fix = load_always_fix_setting();
    filter.gate = this;
    always_fix_ah.ctx = this;
    ui_listener.ctx = this;

    init_ignore_micro();
    hook_event_listener(HT_IDP, this);
    hook_event_listener(HT_UI, &ui_listener);
    install_hexrays_callback(hr_callback, this);
    install_microcode_filter(&filter, true);

    const_type_toggle.register_action();
    selection_mass_type.register_action();

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
    msg("ida_gekko_pseudocode: installed optional Gekko pseudocode filter%s\n",
        always_fix ? " (automatic fixes enabled)" : "");
  }

  ~plugin_ctx_t() override
  {
    const_type_toggle.unregister_action();
    selection_mass_type.unregister_action();

    unregister_action(ALWAYS_FIX_ACTION_NAME);
    remove_hexrays_callback(hr_callback, this);
    unhook_event_listener(HT_UI, &ui_listener);
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
    msg("ida_gekko_pseudocode: active\n");
    return true;
  }
};

int idaapi always_fix_ah_t::activate(action_activation_ctx_t *actx)
{
  if ( ctx == nullptr )
    return 0;

  vdui_t *vu = actx != nullptr ? get_widget_vdui(actx->widget) : nullptr;
  ctx->set_always_fix(!ctx->always_fix, vu);
  msg("ida_gekko_pseudocode: automatic paired-single fixes %s\n", ctx->always_fix ? "enabled" : "disabled");
  return 1;
}

action_state_t idaapi always_fix_ah_t::update(action_update_ctx_t *uctx)
{
  if ( ctx == nullptr || uctx == nullptr || uctx->widget_type != BWN_PSEUDOCODE )
    return AST_DISABLE_FOR_WIDGET;

  update_action_checked(ALWAYS_FIX_ACTION_NAME, ctx->always_fix);
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
  "IDA Gekko Pseudocode Extension",
  "IDA Pro plugin that improves Hex-Rays pseudocode for PowerPC paired-single instructions.",
  "IDA Gekko Pseudocode Extension",
  nullptr,
};

ssize_t idaapi ui_listener_t::on_event(ssize_t code, va_list va)
{
    if ( code == ui_finish_populating_widget_popup )
    {
      TWidget *widget = va_arg(va, TWidget *);
      TPopupMenu *popup_handle = va_arg(va, TPopupMenu *);
      const action_activation_ctx_t *actx = va_arg(va, const action_activation_ctx_t *);
      if ( widget == nullptr || ctx == nullptr )
        return 0;

      const int widget_type = get_widget_type(widget);
      if ( widget_type == BWN_PSEUDOCODE )
      {
        attach_action_to_popup(widget, popup_handle, ALWAYS_FIX_ACTION_NAME, nullptr, SETMENU_APP);
      }
      const bool can_toggle_const = actx != nullptr
                                  ? ctx->const_type_toggle.can_toggle(actx)
                                  : ctx->const_type_toggle.can_toggle(widget, widget_type);
      if ( widget_type == BWN_DISASM && can_toggle_const )
      {
        attach_action_to_popup(widget, popup_handle, TOGGLE_CONST_ACTION_NAME, nullptr, SETMENU_APP);
      }
      else if ( widget_type == BWN_PSEUDOCODE && can_toggle_const )
      {
        attach_action_to_popup(widget, popup_handle, TOGGLE_CONST_ACTION_NAME, nullptr, SETMENU_APP);
      }
    }
    return 0;
  }
