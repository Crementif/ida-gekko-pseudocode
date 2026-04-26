#pragma once

class TWidget;
struct action_handler_t;

class selection_mass_type_action_t
{
public:
  void register_action();
  void unregister_action();

  selection_mass_type_action_t();
  ~selection_mass_type_action_t();

private:
  action_handler_t *handler_;
};
