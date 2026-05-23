#include "wiiu_save_prolog.hpp"

#include <idp.hpp>
#include <bytes.hpp>
#include <funcs.hpp>
#include <allins.hpp>

namespace
{

constexpr bool DISABLE_WIIU_SAVE_PROLOG_FIX = false;

static bool is_imm_value(const op_t &op, uval_t value)
{
  return op.type == o_imm && op.value == value;
}

static bool is_same_reg(const op_t &op, int reg)
{
  return op.type == o_reg && op.reg == reg;
}

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

static const char *find_text_token(const char *text, const char *token)
{
  if ( text == nullptr || token == nullptr )
    return nullptr;

  const size_t len = qstrlen(token);
  for ( const char *p = stristr(text, token); p != nullptr; p = stristr(p + 1, token) )
  {
    const char prev = p == text ? '\0' : p[-1];
    const char next = p[len];
    const bool before_ok = prev == '\0' || qisspace(prev) || prev == ',' || prev == '(';
    const bool after_ok = next == '\0' || qisspace(next) || next == ',' || next == ')';
    if ( before_ok && after_ok )
      return p;
  }
  return nullptr;
}

static bool insn_text_has_tokens_in_order(
        const insn_t &insn,
        const char *first,
        const char *second,
        const char *third = nullptr)
{
  qstring line;
  if ( !get_disasm_line(&line, insn.ea) )
    return false;

  const char *p = line.c_str();
  p = find_text_token(p, first);
  if ( p == nullptr )
    return false;

  p = find_text_token(p + qstrlen(first), second);
  if ( p == nullptr )
    return false;

  if ( third == nullptr )
    return true;

  return find_text_token(p + qstrlen(second), third) != nullptr;
}

static bool is_wiiu_save_prolog_candidate(const insn_t &insn)
{
  switch ( insn.itype )
  {
    case PPC_stwu:
    case PPC_stmw:
    case PPC_mflr:
    case PPC_mr:
    case PPC_stw:
    case PPC_stfd:
    case PPC_stfs:
    case PPC_addi:
    case PPC_ps_merge10:
      return true;
    default:
      return has_mnem(insn, "clrlwi")
          || has_mnem(insn, "neg")
          || has_mnem(insn, "stwux");
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
    if ( !is_wiiu_save_prolog_candidate(insn) )
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

static bool is_primary_frame_alloc(const insn_t &insn)
{
  return insn.itype == PPC_stwu
      && insn_text_has_tokens_in_order(insn, "r1", "(r1)");
}

static bool is_stack_align_mask_insn(const insn_t &insn)
{
  return has_mnem(insn, "clrlwi")
      && insn_text_has_tokens_in_order(insn, "r12", "r1", "28");
}

static bool is_stack_align_negate_insn(const insn_t &insn)
{
  return has_mnem(insn, "neg")
      && insn_text_has_tokens_in_order(insn, "r12", "r12");
}

static bool is_stack_align_commit_insn(const insn_t &insn)
{
  return has_mnem(insn, "stwux")
      && insn_text_has_tokens_in_order(insn, "r11", "r1", "r12");
}

static ssize_t find_prior_insn(const qvector<insn_t> &insns, size_t before_idx, bool (*pred)(const insn_t &))
{
  if ( before_idx > insns.size() )
    before_idx = insns.size();

  for ( ssize_t i = ssize_t(before_idx) - 1; i >= 0; --i )
  {
    if ( pred(insns[size_t(i)]) )
      return i;
  }

  return -1;
}

static bool is_saved_sp_copy_insn(const insn_t &insn)
{
  return has_mnem(insn, "mr")
      && insn_text_has_tokens_in_order(insn, "r11", "r1");
}

static bool find_wiiu_aligned_frame_setup_pattern(
        const qvector<insn_t> &insns,
        size_t *start_idx,
        size_t *end_idx)
{
  for ( size_t commit_idx = 0; commit_idx < insns.size(); ++commit_idx )
  {
    if ( !is_stack_align_commit_insn(insns[commit_idx]) )
      continue;

    const ssize_t neg_idx = find_prior_insn(insns, commit_idx, is_stack_align_negate_insn);
    if ( neg_idx < 0 )
      continue;

    const ssize_t clrlwi_idx = find_prior_insn(insns, size_t(neg_idx), is_stack_align_mask_insn);
    if ( clrlwi_idx < 0 )
      continue;

    const ssize_t stwu_idx = find_prior_insn(insns, commit_idx, is_primary_frame_alloc);
    if ( stwu_idx < 0 )
      continue;

    const ssize_t mr_idx = find_prior_insn(insns, commit_idx, is_saved_sp_copy_insn);
    if ( mr_idx < 0 )
      continue;

    if ( start_idx != nullptr )
      *start_idx = 0;
    if ( end_idx != nullptr )
      *end_idx = commit_idx;
    return true;
  }

  return false;
}

} // namespace

bool is_wiiu_save_prolog_insn(const insn_t &insn)
{
  if ( DISABLE_WIIU_SAVE_PROLOG_FIX )
    return false;

  qvector<insn_t> insns;
  if ( collect_wiiu_save_prolog(&insns, insn.ea) )
  {
    size_t frame_start_idx = BADADDR;
    size_t frame_end_idx = BADADDR;
    if ( find_wiiu_aligned_frame_setup_pattern(insns, &frame_start_idx, &frame_end_idx) )
    {
      for ( size_t i = frame_start_idx; i <= frame_end_idx; ++i )
      {
        if ( insn.ea == insns[i].ea )
          return true;
      }
    }
  }

  return is_wiiu_ps_lane_save_prolog_insn(insn)
      || is_wiiu_lr_save_prolog_insn(insn);
}

void mark_wiiu_save_prolog_insns(ignore_micro_t *ignore, ea_t func_ea)
{
  if ( DISABLE_WIIU_SAVE_PROLOG_FIX || ignore == nullptr )
    return;

  qvector<insn_t> insns;
  if ( !collect_wiiu_save_prolog(&insns, func_ea) )
    return;

  size_t frame_start_idx = BADADDR;
  size_t frame_end_idx = BADADDR;
  if ( find_wiiu_aligned_frame_setup_pattern(insns, &frame_start_idx, &frame_end_idx) )
  {
    for ( size_t i = frame_start_idx; i <= frame_end_idx; ++i )
      ignore->mark_prolog_insn(insns[i].ea);
  }

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
