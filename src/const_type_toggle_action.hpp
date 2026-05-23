#pragma once

class TWidget;
struct action_handler_t;
struct action_ctx_base_t;

class const_type_toggle_action_t
{
public:
  void register_action();
  void unregister_action();

  const_type_toggle_action_t();
  ~const_type_toggle_action_t();

  bool can_toggle(TWidget *widget, int widget_type) const;
  bool can_toggle(const action_ctx_base_t *actx) const;

private:
  action_handler_t *handler_;
};
