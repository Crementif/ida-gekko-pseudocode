#include "const_type_toggle_action.hpp"

#include <limits>

#include <ida.hpp>
#include <kernwin.hpp>
#include <bytes.hpp>
#include <hexrays.hpp>
#include <nalt.hpp>
#include <name.hpp>
#include <typeinf.hpp>

namespace
{

constexpr const char *TOGGLE_CONST_ACTION_NAME = "ida_gekko_pseudocode:toggle_const_type";

enum toggle_kind_t
{
  TOGGLE_KIND_NONE,
  TOGGLE_KIND_FLOAT,
  TOGGLE_KIND_DOUBLE,
  TOGGLE_KIND_CHAR_ARRAY,
};

struct toggle_target_t
{
  toggle_kind_t kind = TOGGLE_KIND_NONE;
  tinfo_t type;
  ea_t ea = BADADDR;
  ea_t func_ea = BADADDR;
  lvar_locator_t lvar;
  qstring lvar_name;
  bool is_lvar = false;
  vdui_t *vu = nullptr;
};

static bool is_supported_toggle_type(const tinfo_t &type)
{
  if ( type.empty() )
    return false;

  if ( type.is_float() || type.is_double() )
    return true;

  if ( type.is_array() )
  {
    tinfo_t elem = type.get_final_element();
    return !elem.empty() && elem.is_char();
  }

  return false;
}

static toggle_kind_t get_toggle_kind(const tinfo_t &type)
{
  if ( type.is_float() )
    return TOGGLE_KIND_FLOAT;
  if ( type.is_double() )
    return TOGGLE_KIND_DOUBLE;
  if ( type.is_array() )
  {
    tinfo_t elem = type.get_final_element();
    if ( !elem.empty() && elem.is_char() )
      return TOGGLE_KIND_CHAR_ARRAY;
  }
  return TOGGLE_KIND_NONE;
}

static bool build_string_array_type(tinfo_t *out, ea_t ea)
{
  if ( out == nullptr )
    return false;

  const int32 strtype = get_str_type(ea);
  if ( get_strtype_bpu(strtype) != 1 )
    return false;

  const asize_t item_size = get_item_size(ea);
  if ( item_size == 0 || item_size > std::numeric_limits<uint32>::max() )
    return false;

  tinfo_t elem(BTF_CHAR);
  return out->create_array(elem, uint32(item_size));
}

static bool get_ea_toggle_target(toggle_target_t *out, ea_t ea, vdui_t *vu)
{
  if ( out == nullptr || ea == BADADDR )
    return false;

  flags64_t flags = get_flags(ea);
  tinfo_t type;
  if ( get_tinfo(&type, ea) && is_supported_toggle_type(type) )
  {
    out->type = type;
  }
  else if ( is_float(flags) )
  {
    out->type = tinfo_t(BTF_FLOAT);
  }
  else if ( is_double(flags) )
  {
    out->type = tinfo_t(BTF_DOUBLE);
  }
  else if ( is_strlit(flags) && build_string_array_type(&out->type, ea) )
  {
  }
  else
  {
    return false;
  }

  out->kind = get_toggle_kind(out->type);
  out->ea = ea;
  out->vu = vu;
  if ( vu != nullptr && vu->cfunc != nullptr )
    out->func_ea = vu->cfunc->entry_ea;
  return out->kind != TOGGLE_KIND_NONE;
}

static bool get_pseudocode_toggle_target(toggle_target_t *out, vdui_t *vu)
{
  if ( out == nullptr || vu == nullptr || vu->cfunc == nullptr || !vu->get_current_item(USE_KEYBOARD) )
    return false;

  out->vu = vu;
  out->func_ea = vu->cfunc->entry_ea;

  if ( vu->item.citype == VDI_LVAR && vu->item.l != nullptr && is_supported_toggle_type(vu->item.l->type()) )
  {
    out->lvar = *vu->item.l;
    out->lvar_name = vu->item.l->name;
    out->is_lvar = true;
    out->type = vu->item.l->type();
    out->kind = get_toggle_kind(out->type);
    return true;
  }

  if ( vu->item.citype != VDI_EXPR || vu->item.e == nullptr )
    return false;

  cexpr_t *expr = vu->item.e;
  if ( expr->op == cot_var )
  {
    lvar_t &lv = expr->v.getv();
    if ( !is_supported_toggle_type(lv.type()) )
      return false;
    out->lvar = lv;
    out->lvar_name = lv.name;
    out->is_lvar = true;
    out->type = lv.type();
    out->kind = get_toggle_kind(out->type);
    return true;
  }

  if ( expr->op == cot_obj )
    return get_ea_toggle_target(out, expr->obj_ea, vu);

  return false;
}

static bool get_toggle_target(toggle_target_t *out, TWidget *widget, int widget_type)
{
  if ( out == nullptr || widget == nullptr )
    return false;

  if ( widget_type == BWN_PSEUDOCODE )
    return get_pseudocode_toggle_target(out, get_widget_vdui(widget));
  if ( widget_type == BWN_DISASM )
    return get_ea_toggle_target(out, get_screen_ea(), nullptr);
  return false;
}

static bool get_toggle_target(toggle_target_t *out, const action_ctx_base_t *actx)
{
  if ( out == nullptr || actx == nullptr || actx->widget == nullptr )
    return false;

  if ( actx->widget_type == BWN_PSEUDOCODE )
    return get_pseudocode_toggle_target(out, get_widget_vdui(actx->widget));

  if ( actx->widget_type != BWN_DISASM )
    return false;

  // Popup actions in disassembly are often opened over an operand/name while
  // the caret remains elsewhere. Prefer the clicked value, then the line EA.
  if ( actx->cur_value != BADADDR && get_ea_toggle_target(out, ea_t(actx->cur_value), nullptr) )
    return true;
  if ( actx->cur_ea != BADADDR && get_ea_toggle_target(out, actx->cur_ea, nullptr) )
    return true;
  return get_ea_toggle_target(out, get_screen_ea(), nullptr);
}

static void toggle_const_qualifier(tinfo_t *type)
{
  if ( type == nullptr || type->empty() )
    return;

  if ( type->is_decl_const() )
    type->clr_const();
  else
    type->set_const();
}

static const char *describe_type(const tinfo_t &type)
{
  if ( type.is_double() )
    return type.is_decl_const() ? "const double" : "double";
  if ( type.is_float() )
    return type.is_decl_const() ? "const float" : "float";
  if ( type.is_array() )
    return type.is_decl_const() ? "const char[]" : "char[]";
  return "type";
}

static qstring describe_target(const toggle_target_t &target)
{
  if ( target.is_lvar )
    return target.lvar_name;
  if ( target.ea != BADADDR )
  {
    qstring name = get_short_name(target.ea);
    if ( !name.empty() )
      return name;
  }

  qstring fallback;
  if ( target.ea != BADADDR )
    fallback.sprnt("%a", target.ea);
  else
    fallback = "selection";
  return fallback;
}

static bool apply_toggle_target(const toggle_target_t &target)
{
  if ( target.kind == TOGGLE_KIND_NONE )
    return false;

  tinfo_t new_type = target.type;
  toggle_const_qualifier(&new_type);

  if ( target.is_lvar )
  {
    lvar_saved_info_t info;
    info.ll = target.lvar;
    info.type = new_type;
    info.size = new_type.get_size();
    if ( !modify_user_lvar_info(target.func_ea, MLI_TYPE, info) )
      return false;

    // Keep the current pseudocode widget alive; closing views here can leave
    // target.vu dangling before refresh_view() runs.
    mark_cfunc_dirty(target.func_ea, false);
    if ( target.vu != nullptr )
      target.vu->refresh_view(true);
    return true;
  }

  if ( target.ea == BADADDR )
    return false;

  if ( target.kind == TOGGLE_KIND_FLOAT )
  {
    if ( !create_float(target.ea, 4, true) )
      return false;
  }
  else if ( target.kind == TOGGLE_KIND_DOUBLE )
  {
    if ( !create_double(target.ea, 8, true) )
      return false;
  }

  if ( !apply_tinfo(target.ea, new_type, TINFO_DEFINITE) )
    return false;

  if ( target.vu != nullptr && target.func_ea != BADADDR )
  {
    // The hotkey may run from an active pseudocode widget. Do not close views
    // before refreshing that same widget.
    mark_cfunc_dirty(target.func_ea, false);
    target.vu->refresh_view(true);
  }
  else
  {
    refresh_idaview_anyway();
  }

  return true;
}

struct const_type_toggle_handler_t : public action_handler_t
{
  const_type_toggle_action_t *ctx = nullptr;

  int idaapi activate(action_activation_ctx_t *actx) override
  {
    if ( actx == nullptr )
      return 0;

    toggle_target_t target;
    if ( !get_toggle_target(&target, actx) )
      return 0;

    qstring target_name = describe_target(target);
    tinfo_t new_type = target.type;
    toggle_const_qualifier(&new_type);

    if ( !apply_toggle_target(target) )
      return 0;

    msg("ida_gekko_pseudocode: %s -> %s\n",
        target_name.c_str(),
        describe_type(new_type));
    return 1;
  }

  action_state_t idaapi update(action_update_ctx_t *uctx) override
  {
    if ( uctx == nullptr )
      return AST_DISABLE_FOR_WIDGET;

    if ( ctx != nullptr && ctx->can_toggle(uctx->widget, uctx->widget_type) )
      return AST_ENABLE_FOR_WIDGET;
    return AST_DISABLE_FOR_WIDGET;
  }
};

} // namespace

const_type_toggle_action_t::const_type_toggle_action_t()
  : handler_(new const_type_toggle_handler_t())
{
  static_cast<const_type_toggle_handler_t *>(handler_)->ctx = this;
}

void const_type_toggle_action_t::register_action()
{
  ::register_action(ACTION_DESC_LITERAL(
                  TOGGLE_CONST_ACTION_NAME,
                  "Toggle const on float/double/string",
                  handler_,
                  nullptr,
                  "Toggle const on float, double, and char[] items",
                  -1));
}

const_type_toggle_action_t::~const_type_toggle_action_t()
{
  unregister_action();
  delete handler_;
}

void const_type_toggle_action_t::unregister_action()
{
  ::unregister_action(TOGGLE_CONST_ACTION_NAME);
}

bool const_type_toggle_action_t::can_toggle(TWidget *widget, int widget_type) const
{
  toggle_target_t target;
  return get_toggle_target(&target, widget, widget_type);
}

bool const_type_toggle_action_t::can_toggle(const action_ctx_base_t *actx) const
{
  toggle_target_t target;
  return get_toggle_target(&target, actx);
}
