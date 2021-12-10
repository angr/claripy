/**
 * @file
 * \ingroup util
 * @brief This file defines the multiplex log backend
 */
#ifndef R_UTIL_LOG_BACKEND_MULTIPLEX_HPP_
#define R_UTIL_LOG_BACKEND_MULTIPLEX_HPP_

#include "base.hpp"

#include "../../assert_not_null_debug.hpp"
#include "../../thread_safe.hpp"

#include <memory>
#include <vector> // NOLINT


namespace Util::Log::Backend {

    /** The multiplex backend
     *  This backend logs to multiple backends
     *  This class is not thread safe when written to after installed as a backend
     *  Backend shared pointers may not be null
     */
    struct Multiplex final : public Base {

        /** Log the given message, level, to the correct log given by log_id with each backend */
        inline void log(CCSC id, const Level::Level &lvl, std::string &&msg) const final {
            for (UInt i { 1 }; i < backends.size(); ++i) {
                const auto &bk { backends[i - 1] };
                UTIL_ASSERT_NOT_NULL_DEBUG(bk)
                bk->log(id, lvl, std::string { msg });
            }
            if (!backends.empty()) {
                backends.back()->log(id, lvl, std::move(msg));
            }
        }

        /** Flush logs */
        inline void flush() const final {
            for (const auto &i : backends) {
                i->flush();
            }
        }

        /** A container to store every backend: no backend pointers may be null */
        std::vector<std::shared_ptr<const Base>> backends; // NOLINT
    };

} // namespace Util::Log::Backend

#endif
