#include "selection_mass_type_action.hpp"

#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <string>

#include <bytes.hpp>
#include <ida.hpp>
#include <kernwin.hpp>
#include <loader.hpp>
#include <nalt.hpp>
#include <segment.hpp>
#include <typeinf.hpp>

namespace
{

constexpr const char *SELECTION_MASS_TYPE_ACTION_NAME = "ida_gekko_pseudocode:selection_mass_type";
constexpr const char *SELECTION_MASS_TYPE_SHORTCUT = "Ctrl+Shift+Alt+Y";
constexpr const char *SELECTION_MASS_TYPE_MENU_PATH = "Search/Sequence of bytes";

enum storage_kind_t
{
  STORAGE_KIND_NONE,
  STORAGE_KIND_BYTE,
  STORAGE_KIND_WORD,
  STORAGE_KIND_DWORD,
  STORAGE_KIND_QWORD,
  STORAGE_KIND_FLOAT,
  STORAGE_KIND_DOUBLE,
};

struct search_pattern_t
{
  compiled_binpat_vec_t patterns;
  asize_t item_size = 0;
  qstring suggested_type;
};

struct apply_stats_t
{
  size_t match_count = 0;
  size_t candidate_count = 0;
  size_t applied_count = 0;
  size_t skipped_count = 0;
  size_t alignment_skipped_count = 0;
  size_t declined_count = 0;
  size_t cancelled_count = 0;
  size_t failed_count = 0;
};

struct section_stats_t
{
  qstring name;
  apply_stats_t stats;
  qvector<ea_t> candidate_eas;
};

struct parsed_input_t
{
  storage_kind_t storage_kind = STORAGE_KIND_NONE;
  tinfo_t tif;
  asize_t item_size = 0;
  bool has_tinfo = false;
};

static const char *canonical_storage_directive(storage_kind_t kind)
{
  switch ( kind )
  {
    case STORAGE_KIND_BYTE:   return ".byte";
    case STORAGE_KIND_WORD:   return ".word";
    case STORAGE_KIND_DWORD:  return ".long";
    case STORAGE_KIND_QWORD:  return ".quad";
    case STORAGE_KIND_FLOAT:  return ".float";
    case STORAGE_KIND_DOUBLE: return ".double";
    case STORAGE_KIND_NONE:   break;
  }
  return nullptr;
}

static std::string trim_copy(const char *text)
{
  std::string out = text != nullptr ? text : "";
  size_t begin = 0;
  while ( begin < out.size() && qisspace(uchar(out[begin])) )
    ++begin;

  size_t end = out.size();
  while ( end > begin && qisspace(uchar(out[end - 1])) )
    --end;

  return out.substr(begin, end - begin);
}

static bool create_storage_item(storage_kind_t kind, ea_t ea, asize_t size)
{
  switch ( kind )
  {
    case STORAGE_KIND_BYTE:   return create_byte(ea, size, true);
    case STORAGE_KIND_WORD:   return create_word(ea, size, true);
    case STORAGE_KIND_DWORD:  return create_dword(ea, size, true);
    case STORAGE_KIND_QWORD:  return create_qword(ea, size, true);
    case STORAGE_KIND_FLOAT:  return create_float(ea, size, true);
    case STORAGE_KIND_DOUBLE: return create_double(ea, size, true);
    case STORAGE_KIND_NONE:   return create_byte(ea, size, true);
  }
  return false;
}

static bool try_parse_storage_directive(parsed_input_t *out, qstring text)
{
  if ( out == nullptr )
    return false;

  text.rtrim();
  text.ltrim();
  for ( ssize_t i = 0; i < text.length(); ++i )
    text[i] = char(qtolower(uchar(text[i])));

  if ( text == ".byte" || text == "db" || text == "byte" )
  {
    out->storage_kind = STORAGE_KIND_BYTE;
    out->item_size = 1;
    return true;
  }
  if ( text == ".word" || text == ".short" || text == "dw" || text == "word" || text == "short" )
  {
    out->storage_kind = STORAGE_KIND_WORD;
    out->item_size = 2;
    return true;
  }
  if ( text == ".long" || text == ".int" || text == "dd" )
  {
    out->storage_kind = STORAGE_KIND_DWORD;
    out->item_size = 4;
    return true;
  }
  if ( text == ".quad" || text == ".dword" || text == "dq" )
  {
    out->storage_kind = STORAGE_KIND_QWORD;
    out->item_size = 8;
    return true;
  }
  if ( text == ".float" )
  {
    out->storage_kind = STORAGE_KIND_FLOAT;
    out->item_size = 4;
    return true;
  }
  if ( text == ".double" )
  {
    out->storage_kind = STORAGE_KIND_DOUBLE;
    out->item_size = 8;
    return true;
  }

  return false;
}

static bool try_parse_type(parsed_input_t *out, const qstring &text)
{
  if ( out == nullptr )
    return false;

  tinfo_t tif;
  if ( !parse_decl(&tif, nullptr, nullptr, text.c_str(), PT_TYP | PT_SIL | PT_SEMICOLON) )
    return false;

  const asize_t size = tif.get_size();
  if ( size <= 0 )
    return false;

  out->tif = tif;
  out->item_size = size;
  out->has_tinfo = true;
  if ( tif.is_float() )
    out->storage_kind = STORAGE_KIND_FLOAT;
  else if ( tif.is_double() )
    out->storage_kind = STORAGE_KIND_DOUBLE;
  else if ( size == 1 )
    out->storage_kind = STORAGE_KIND_BYTE;
  else if ( size == 2 )
    out->storage_kind = STORAGE_KIND_WORD;
  else if ( size == 4 )
    out->storage_kind = STORAGE_KIND_DWORD;
  else if ( size == 8 )
    out->storage_kind = STORAGE_KIND_QWORD;
  return true;
}

static bool parse_mass_type_input(parsed_input_t *out, const qstring &text)
{
  if ( out == nullptr )
    return false;

  *out = parsed_input_t();
  qstring trimmed = text;
  trimmed.rtrim();
  trimmed.ltrim();
  if ( trimmed.empty() )
    return false;

  if ( try_parse_storage_directive(out, trimmed) )
    return true;
  return try_parse_type(out, trimmed);
}

static bool looks_like_typed_search_pattern(const qstring &text)
{
  const std::string trimmed = trim_copy(text.c_str());
  if ( trimmed.empty() )
    return false;

  size_t split = 0;
  while ( split < trimmed.size() && !qisspace(uchar(trimmed[split])) )
    ++split;

  qstring directive = trimmed.substr(0, split).c_str();
  parsed_input_t parsed;
  return try_parse_storage_directive(&parsed, directive);
}

static bool extract_compiled_pattern_size(asize_t *out_size, const compiled_binpat_vec_t &patterns, qstring *out_error)
{
  if ( out_size == nullptr )
    return false;

  if ( patterns.empty() )
  {
    if ( out_error != nullptr )
      *out_error = "Search pattern did not produce any bytes";
    return false;
  }

  const asize_t size = asize_t(patterns[0].bytes.size());
  if ( size <= 0 )
  {
    if ( out_error != nullptr )
      *out_error = "Search pattern has zero length";
    return false;
  }

  for ( const compiled_binpat_t &pattern : patterns )
  {
    if ( asize_t(pattern.bytes.size()) != size )
    {
      if ( out_error != nullptr )
        *out_error = "Search pattern expands to multiple byte lengths; use a concrete byte sequence";
      return false;
    }
  }

  *out_size = size;
  return true;
}

static void append_integer_bytes(bytevec_t *out, uint64 value, asize_t size)
{
  if ( out == nullptr || size <= 0 )
    return;

  if ( inf_is_be() )
  {
    for ( asize_t i = size; i > 0; --i )
      out->push_back(uchar(value >> ((i - 1) * 8)));
  }
  else
  {
    for ( asize_t i = 0; i < size; ++i )
      out->push_back(uchar(value >> (i * 8)));
  }
}

static bool parse_unsigned_token(uint64 *out, const std::string &text, unsigned bits, qstring *out_error)
{
  if ( out == nullptr || bits == 0 || bits > 64 )
    return false;

  errno = 0;
  char *end = nullptr;
  const unsigned long long value = strtoull(text.c_str(), &end, 0);
  if ( errno != 0 || end == text.c_str() || *end != '\0' )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Could not parse '%s' as an integer", text.c_str());
    return false;
  }

  const uint64 max_value = bits == 64 ? uint64(-1) : ((uint64(1) << bits) - 1);
  if ( uint64(value) > max_value )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Integer '%s' does not fit in %u bits", text.c_str(), bits);
    return false;
  }

  *out = uint64(value);
  return true;
}

static bool parse_signed_token(uint64 *out, const std::string &text, unsigned bits, qstring *out_error)
{
  if ( out == nullptr || bits == 0 || bits > 64 )
    return false;

  errno = 0;
  char *end = nullptr;
  const long long value = strtoll(text.c_str(), &end, 0);
  if ( errno != 0 || end == text.c_str() || *end != '\0' )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Could not parse '%s' as an integer", text.c_str());
    return false;
  }

  const int64 min_value = bits == 64
                        ? std::numeric_limits<int64>::min()
                        : -(int64(1) << (bits - 1));
  const int64 max_value = bits == 64
                        ? std::numeric_limits<int64>::max()
                        : ((int64(1) << (bits - 1)) - 1);
  if ( value < min_value || value > max_value )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Integer '%s' does not fit in %u bits", text.c_str(), bits);
    return false;
  }

  *out = uint64(int64(value));
  return true;
}

static bool parse_typed_integer_value(uint64 *out, const std::string &text, asize_t size, qstring *out_error)
{
  const unsigned bits = unsigned(size * 8);
  if ( !text.empty() && (text[0] == '-' || text[0] == '+') )
    return parse_signed_token(out, text, bits, out_error);
  return parse_unsigned_token(out, text, bits, out_error);
}

static bool parse_float_value(uint32 *out, const std::string &text, qstring *out_error)
{
  if ( out == nullptr )
    return false;

  errno = 0;
  char *end = nullptr;
  const float value = strtof(text.c_str(), &end);
  if ( errno != 0 || end == text.c_str() || *end != '\0' )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Could not parse '%s' as a float", text.c_str());
    return false;
  }

  std::memcpy(out, &value, sizeof(value));
  return true;
}

static bool parse_double_value(uint64 *out, const std::string &text, qstring *out_error)
{
  if ( out == nullptr )
    return false;

  errno = 0;
  char *end = nullptr;
  const double value = strtod(text.c_str(), &end);
  if ( errno != 0 || end == text.c_str() || *end != '\0' )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Could not parse '%s' as a double", text.c_str());
    return false;
  }

  std::memcpy(out, &value, sizeof(value));
  return true;
}

static bool parse_typed_search_pattern(search_pattern_t *out, const qstring &text, qstring *out_error)
{
  if ( out == nullptr )
    return false;

  *out = search_pattern_t();

  const std::string trimmed = trim_copy(text.c_str());
  size_t split = 0;
  while ( split < trimmed.size() && !qisspace(uchar(trimmed[split])) )
    ++split;

  const std::string directive_text = trimmed.substr(0, split);
  const std::string value_text = trim_copy(split < trimmed.size() ? trimmed.c_str() + split + 1 : nullptr);
  qstring directive = directive_text.c_str();

  parsed_input_t parsed;
  if ( !try_parse_storage_directive(&parsed, directive) )
    return false;

  if ( value_text.empty() )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Enter a value after %s, for example '%s 1.0'", directive.c_str(), directive.c_str());
    return false;
  }

  compiled_binpat_t &pattern = out->patterns.push_back();
  switch ( parsed.storage_kind )
  {
    case STORAGE_KIND_BYTE:
    case STORAGE_KIND_WORD:
    case STORAGE_KIND_DWORD:
    case STORAGE_KIND_QWORD:
    {
      uint64 value = 0;
      if ( !parse_typed_integer_value(&value, value_text, parsed.item_size, out_error) )
        return false;
      append_integer_bytes(&pattern.bytes, value, parsed.item_size);
      break;
    }

    case STORAGE_KIND_FLOAT:
    {
      uint32 bits = 0;
      if ( !parse_float_value(&bits, value_text, out_error) )
        return false;
      append_integer_bytes(&pattern.bytes, bits, sizeof(bits));
      break;
    }

    case STORAGE_KIND_DOUBLE:
    {
      uint64 bits = 0;
      if ( !parse_double_value(&bits, value_text, out_error) )
        return false;
      append_integer_bytes(&pattern.bytes, bits, sizeof(bits));
      break;
    }

    case STORAGE_KIND_NONE:
      if ( out_error != nullptr )
        out_error->sprnt("Unsupported typed search directive '%s'", directive.c_str());
      return false;
  }

  out->item_size = asize_t(pattern.bytes.size());
  if ( const char *canonical = canonical_storage_directive(parsed.storage_kind) )
    out->suggested_type = canonical;
  return true;
}

static bool parse_search_pattern(search_pattern_t *out, const qstring &text, qstring *out_error)
{
  if ( out == nullptr )
    return false;

  *out = search_pattern_t();

  qstring trimmed = text;
  trimmed.ltrim();
  trimmed.rtrim();
  if ( trimmed.empty() )
  {
    if ( out_error != nullptr )
      *out_error = "Search pattern is empty";
    return false;
  }

  if ( looks_like_typed_search_pattern(trimmed) )
    return parse_typed_search_pattern(out, trimmed, out_error);

  qstring parse_error;
  if ( !parse_binpat_str(&out->patterns, get_screen_ea(), trimmed.c_str(), 16, PBSENC_DEF1BPU, &parse_error) )
  {
    if ( out_error != nullptr )
      *out_error = parse_error;
    return false;
  }

  return extract_compiled_pattern_size(&out->item_size, out->patterns, out_error);
}

static bool is_required_alignment_match(ea_t ea)
{
  return (ea & 0x3) == 0;
}

static qstring get_section_name(ea_t ea)
{
  segment_t *seg = getseg(ea);
  if ( seg == nullptr )
    return "<no segment>";

  qstring name;
  if ( get_visible_segm_name(&name, seg) > 0 && !name.empty() )
    return name;
  if ( get_segm_name(&name, seg) > 0 && !name.empty() )
    return name;
  return "<unnamed segment>";
}

static section_stats_t *get_or_create_section_stats(qvector<section_stats_t> *sections, ea_t ea)
{
  if ( sections == nullptr )
    return nullptr;

  const qstring name = get_section_name(ea);
  for ( section_stats_t &section : *sections )
  {
    if ( section.name == name )
      return &section;
  }

  section_stats_t &section = sections->push_back();
  section.name = name;
  return &section;
}

static void increment_stat(size_t apply_stats_t::*field, apply_stats_t *total, apply_stats_t *section)
{
  if ( total != nullptr )
    ++(total->*field);
  if ( section != nullptr )
    ++(section->*field);
}

static bool is_safe_untyped_match(ea_t ea, asize_t size)
{
  const ea_t max_ea = inf_get_max_ea();
  if ( ea == BADADDR || size <= 0 || ea >= max_ea )
    return false;
  if ( uint64(ea) + uint64(size) > uint64(max_ea) )
    return false;

  const flags64_t start_flags = get_flags(ea);
  if ( is_code(start_flags) || has_ti(ea) )
    return false;

  if ( is_unknown(start_flags) )
  {
    for ( asize_t off = 0; off < size; ++off )
    {
      const ea_t cur = ea + off;
      if ( !is_unknown(get_flags(cur)) || has_ti(cur) )
        return false;
    }
    return true;
  }

  if ( !is_data(start_flags) || get_item_head(ea) != ea || get_item_size(ea) != size )
    return false;

  for ( asize_t off = 0; off < size; ++off )
  {
    const ea_t cur = ea + off;
    if ( get_item_head(cur) != ea || is_code(get_flags(cur)) || has_ti(cur) )
      return false;
  }
  return true;
}

static bool apply_mass_type(ea_t ea, const parsed_input_t &parsed, qstring *out_error)
{
  if ( parsed.item_size == 0 )
  {
    if ( out_error != nullptr )
      *out_error = "Could not determine item size";
    return false;
  }

  del_items(ea, DELIT_SIMPLE, parsed.item_size);
  if ( !create_storage_item(parsed.storage_kind, ea, parsed.item_size) )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Failed to create item at %a", ea);
    return false;
  }
  if ( parsed.has_tinfo && !apply_tinfo(ea, parsed.tif, TINFO_DEFINITE) )
  {
    if ( out_error != nullptr )
      out_error->sprnt("Failed to apply type at %a", ea);
    return false;
  }
  return true;
}

static void collect_search_matches(
        apply_stats_t *stats,
        qvector<section_stats_t> *sections,
        const search_pattern_t &pattern,
        asize_t item_size)
{
  if ( stats == nullptr )
    return;

  *stats = apply_stats_t();
  const ea_t max_ea = inf_get_max_ea();
  ea_t cursor = inf_get_min_ea();
  const asize_t step = item_size > 0 ? item_size : 1;

  while ( cursor < max_ea )
  {
    const ea_t match_ea = bin_search(cursor,
                                     max_ea,
                                     pattern.patterns,
                                     BIN_SEARCH_FORWARD | BIN_SEARCH_NOSHOW | BIN_SEARCH_NOBREAK);
    if ( match_ea == BADADDR )
      break;

    section_stats_t *section = get_or_create_section_stats(sections, match_ea);
    apply_stats_t *section_stats = section != nullptr ? &section->stats : nullptr;
    increment_stat(&apply_stats_t::match_count, stats, section_stats);

    if ( !is_required_alignment_match(match_ea) )
    {
      increment_stat(&apply_stats_t::alignment_skipped_count, stats, section_stats);
      increment_stat(&apply_stats_t::skipped_count, stats, section_stats);
    }
    else if ( is_safe_untyped_match(match_ea, item_size) )
    {
      if ( section != nullptr )
        section->candidate_eas.push_back(match_ea);
      increment_stat(&apply_stats_t::candidate_count, stats, section_stats);
    }
    else
    {
      increment_stat(&apply_stats_t::skipped_count, stats, section_stats);
    }

    const ea_t next_ea = match_ea + step;
    if ( next_ea <= match_ea )
      break;
    cursor = next_ea;
  }
}

static int confirm_section_apply(const section_stats_t &section, const qstring &search_input, const qstring &type_input)
{
  const uint64 candidate_count = uint64(section.candidate_eas.size());
  if ( candidate_count == 0 )
    return ASKBTN_NO;

  qstring prompt;
  if ( candidate_count == 1 )
  {
    prompt.sprnt("Section [%s]\n"
                 "Search: %s\n"
                 "Type: %s\n"
                 "Eligible matches: %llu\n"
                 "Only match: %a\n"
                 "Skipped before apply: %llu (%llu due to 0x04 alignment)\n"
                 "Apply to this section?",
                 section.name.c_str(),
                 search_input.c_str(),
                 type_input.c_str(),
                 candidate_count,
                 section.candidate_eas[0],
                 uint64(section.stats.skipped_count),
                 uint64(section.stats.alignment_skipped_count));
  }
  else
  {
    prompt.sprnt("Section [%s]\n"
                 "Search: %s\n"
                 "Type: %s\n"
                 "Eligible matches: %llu\n"
                 "First/last eligible: %a .. %a\n"
                 "Skipped before apply: %llu (%llu due to 0x04 alignment)\n"
                 "Apply to this section?",
                 section.name.c_str(),
                 search_input.c_str(),
                 type_input.c_str(),
                 candidate_count,
                 section.candidate_eas.front(),
                 section.candidate_eas.back(),
                 uint64(section.stats.skipped_count),
                 uint64(section.stats.alignment_skipped_count));
  }

  return ask_yn(ASKBTN_YES, "%s", prompt.c_str());
}

static bool confirm_and_apply_section_matches(
        apply_stats_t *stats,
        qvector<section_stats_t> *sections,
        const parsed_input_t &parsed,
        const qstring &search_input,
        const qstring &type_input,
        qstring *out_first_error)
{
  if ( stats == nullptr || sections == nullptr )
    return false;

  for ( size_t i = 0; i < sections->size(); ++i )
  {
    section_stats_t &section = sections->at(i);
    const size_t candidate_count = section.candidate_eas.size();
    if ( candidate_count == 0 )
      continue;

    const int answer = confirm_section_apply(section, search_input, type_input);
    if ( answer == ASKBTN_CANCEL )
    {
      for ( size_t j = i; j < sections->size(); ++j )
      {
        section_stats_t &remaining = sections->at(j);
        const size_t cancelled_count = remaining.candidate_eas.size();
        remaining.stats.cancelled_count += cancelled_count;
        stats->cancelled_count += cancelled_count;
      }
      return false;
    }

    if ( answer == ASKBTN_NO )
    {
      section.stats.declined_count += candidate_count;
      stats->declined_count += candidate_count;
      continue;
    }

    for ( ea_t ea : section.candidate_eas )
    {
      qstring error;
      if ( apply_mass_type(ea, parsed, &error) )
      {
        ++section.stats.applied_count;
        ++stats->applied_count;
      }
      else
      {
        ++section.stats.failed_count;
        ++stats->failed_count;
        if ( out_first_error != nullptr && out_first_error->empty() )
          *out_first_error = error;
      }
    }
  }

  return true;
}

struct selection_mass_type_handler_t : public action_handler_t
{
  qstring last_search_input;
  qstring last_type_input;

  int idaapi activate(action_activation_ctx_t *actx) override
  {
    qnotused(actx);

    qstring search_input = last_search_input;
    if ( search_input.empty() )
      search_input = ".float 1.0";

    if ( !ask_str(&search_input,
                  HIST_SRCH,
                  "Search for bytes or a typed scalar like '.float 1.0'.\n"
                  "Eligible 0x04-aligned untyped matches will be grouped and confirmed per section.") )
    {
      return 0;
    }
    last_search_input = search_input;

    search_pattern_t pattern;
    qstring parse_error;
    if ( !parse_search_pattern(&pattern, search_input, &parse_error) )
    {
      warning("ida_gekko_pseudocode: %s", parse_error.c_str());
      return 0;
    }

    qstring type_input = pattern.suggested_type;
    if ( type_input.empty() )
      type_input = last_type_input;

    qstring type_prompt;
    type_prompt.sprnt("Apply which type to each untyped %llu-byte match for '%s'?\n"
                      "Enter a C type like 'const float' or a storage directive like '.float'",
                      uint64(pattern.item_size),
                      search_input.c_str());
    if ( !ask_str(&type_input, HIST_IDENT, "%s", type_prompt.c_str()) )
      return 0;
    last_type_input = type_input;

    parsed_input_t parsed;
    if ( !parse_mass_type_input(&parsed, type_input) )
    {
      warning("ida_gekko_pseudocode: could not parse '%s' as a type or storage directive", type_input.c_str());
      return 0;
    }

    if ( parsed.item_size != pattern.item_size )
    {
      warning("ida_gekko_pseudocode: search pattern is %llu bytes, but '%s' is %llu bytes",
              uint64(pattern.item_size),
              type_input.c_str(),
              uint64(parsed.item_size));
      return 0;
    }

    apply_stats_t stats;
    qvector<section_stats_t> sections;
    qstring first_error;
    collect_search_matches(&stats, &sections, pattern, parsed.item_size);

    if ( stats.match_count == 0 )
    {
      warning("ida_gekko_pseudocode: no matches found for '%s'", search_input.c_str());
      return 0;
    }

    if ( stats.candidate_count == 0 )
    {
      msg("ida_gekko_pseudocode: search '%s' -> no eligible matches; skipped %llu/%llu (%llu due to 0x04 alignment)\n",
          search_input.c_str(),
          uint64(stats.skipped_count),
          uint64(stats.match_count),
          uint64(stats.alignment_skipped_count));
      for ( const section_stats_t &section : sections )
      {
        if ( section.stats.match_count == 0 )
          continue;
        msg("ida_gekko_pseudocode:   [%s] eligible %llu/%llu; skipped %llu (%llu due to 0x04 alignment)\n",
            section.name.c_str(),
            uint64(section.stats.candidate_count),
            uint64(section.stats.match_count),
            uint64(section.stats.skipped_count),
            uint64(section.stats.alignment_skipped_count));
      }
      warning("ida_gekko_pseudocode: found matches for '%s', but none were 0x04-aligned untyped item starts", search_input.c_str());
      return 0;
    }

    const bool completed = confirm_and_apply_section_matches(&stats,
                                                             &sections,
                                                             parsed,
                                                             search_input,
                                                             type_input,
                                                             &first_error);

    if ( stats.applied_count != 0 )
      refresh_idaview_anyway();

    msg("ida_gekko_pseudocode: search '%s' -> eligible %llu/%llu matches; applied %llu, declined %llu, cancelled %llu, skipped %llu (%llu due to 0x04 alignment), failures %llu\n",
        search_input.c_str(),
        uint64(stats.candidate_count),
        uint64(stats.match_count),
        uint64(stats.applied_count),
        uint64(stats.declined_count),
        uint64(stats.cancelled_count),
        uint64(stats.skipped_count),
        uint64(stats.alignment_skipped_count),
        uint64(stats.failed_count));

    for ( const section_stats_t &section : sections )
    {
      if ( section.stats.match_count == 0 )
        continue;
      msg("ida_gekko_pseudocode:   [%s] eligible %llu/%llu; applied %llu, declined %llu, cancelled %llu, skipped %llu (%llu due to 0x04 alignment), failures %llu\n",
          section.name.c_str(),
          uint64(section.stats.candidate_count),
          uint64(section.stats.match_count),
          uint64(section.stats.applied_count),
          uint64(section.stats.declined_count),
          uint64(section.stats.cancelled_count),
          uint64(section.stats.skipped_count),
          uint64(section.stats.alignment_skipped_count),
          uint64(section.stats.failed_count));
    }

    if ( !completed )
      warning("ida_gekko_pseudocode: cancelled while confirming sections for '%s'", search_input.c_str());

    if ( stats.applied_count == 0 )
    {
      warning("ida_gekko_pseudocode: no section was applied for '%s'", search_input.c_str());
      return 0;
    }

    if ( stats.failed_count != 0 )
      warning("ida_gekko_pseudocode: %s", first_error.c_str());
    return stats.failed_count == stats.match_count ? 0 : 1;
  }

  action_state_t idaapi update(action_update_ctx_t *uctx) override
  {
    qnotused(uctx);
    return AST_ENABLE_ALWAYS;
  }
};

} // namespace

selection_mass_type_action_t::selection_mass_type_action_t()
  : handler_(new selection_mass_type_handler_t())
{}

void selection_mass_type_action_t::register_action()
{
  if ( !::register_action(ACTION_DESC_LITERAL(
                  SELECTION_MASS_TYPE_ACTION_NAME,
                  "Search Untyped Values And Apply Type...",
                  handler_,
                  SELECTION_MASS_TYPE_SHORTCUT,
                  "Search for byte patterns or typed scalars and apply a type to untyped matches",
                  -1)) )
  {
    return;
  }

  attach_action_to_menu(SELECTION_MASS_TYPE_MENU_PATH,
                        SELECTION_MASS_TYPE_ACTION_NAME,
                        SETMENU_APP);
}

selection_mass_type_action_t::~selection_mass_type_action_t()
{
  unregister_action();
  delete handler_;
}

void selection_mass_type_action_t::unregister_action()
{
  detach_action_from_menu(SELECTION_MASS_TYPE_MENU_PATH, SELECTION_MASS_TYPE_ACTION_NAME);
  ::unregister_action(SELECTION_MASS_TYPE_ACTION_NAME);
}
