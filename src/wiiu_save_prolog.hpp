#pragma once

#include <ida.hpp>
#include <hexrays.hpp>

bool is_wiiu_save_prolog_insn(const insn_t &insn);
void mark_wiiu_save_prolog_insns(ignore_micro_t *ignore, ea_t func_ea);
