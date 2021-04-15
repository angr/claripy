/*
 * \defgroup utils Claricpp Utilities
 * @brief A group of useful classes and methods which all parts of claricpp can utilize
 */

/**
 * @file
 * @brief This file includes all public pieces of utils
 * \ingroup utils
 */
#ifndef __UTILS_HPP__
#define __UTILS_HPP__

#include "utils/affirm.hpp"
#include "utils/ansi_color_codes.hpp"
#include "utils/bitmask_operators.hpp"
#include "utils/cache.hpp"
#include "utils/const_eval.hpp"
#include "utils/enable_as_bitmask.hpp"
#include "utils/error.hpp"
#include "utils/file_line_hash.hpp"
#include "utils/fnv1a.hpp"
#include "utils/full.hpp"
#include "utils/has_constructor.hpp"
#include "utils/has_flags.hpp"
#include "utils/inc.hpp"
#include "utils/internal_type.hpp"
#include "utils/is_ancestor.hpp"
#include "utils/is_in.hpp"
#include "utils/is_same.hpp"
#include "utils/is_strong_enum.hpp"
#include "utils/log.hpp"
#include "utils/macros.hpp"
#include "utils/make_derived_shared.hpp"
#include "utils/max.hpp"
#include "utils/ostream.hpp"
#include "utils/pointer_cast.hpp"
#include "utils/pow.hpp"
#include "utils/recurrence_guard.hpp"
#include "utils/ref.hpp"
#include "utils/run_after_main.hpp"
#include "utils/run_before_main.hpp"
#include "utils/run_on_destruction.hpp"
#include "utils/select.hpp"
#include "utils/set_join.hpp"
#include "utils/sfinae_test.hpp"
#include "utils/sink.hpp"
#include "utils/strlen.hpp"
#include "utils/thread_safe.hpp"
#include "utils/to_heap_cache.hpp"
#include "utils/to_str.hpp"
#include "utils/transfer_const.hpp"
#include "utils/type_dependent_constant.hpp"
#include "utils/type_id.hpp"
#include "utils/type_pun.hpp"
#include "utils/type_to_type.hpp"
#include "utils/unconstructable.hpp"

#endif
