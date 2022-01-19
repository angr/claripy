/** @file */
#include "manager.hpp"

#include "simplifiers.hpp"

using namespace Simplify;

Util::ThreadSafe::Mutable<Vec> Manager::vec { builtin_vec() };
Util::ThreadSafe::Mutable<Map> Manager::map { builtin_map() };
