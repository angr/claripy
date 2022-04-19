/**
 * @file
 * \ingroup testlib
 */
#include "error.hpp"


#ifndef CONSTANT_LOG_LEVEL

using namespace Util::Log;
namespace T = UnitTest::TestLib;

thread_local std::shared_ptr<const Backend::Base> T::original_bk { nullptr };
thread_local std::shared_ptr<const Style::Base> T::original_sty { nullptr };

#endif
