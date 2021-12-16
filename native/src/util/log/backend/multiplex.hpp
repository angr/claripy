/**
 * @file
 * \ingroup util
 * @brief This file defines the multiplex log backend
 */
#ifndef R_UTIL_LOG_BACKEND_MULTIPLEX_HPP_
#define R_UTIL_LOG_BACKEND_MULTIPLEX_HPP_

#include "multiplexable.hpp"

#include "../../assert_not_null_debug.hpp"

#include <memory>
#include <vector>


namespace Util::Log::Backend {

    /** The multiplex backend
     *  This backend logs to multiple backends
     *  This class is not thread safe when written to after installed as a backend
     *  Backend shared pointers may not be null
     *  This backend itself is multiplexable
     */
    struct Multiplex final : public Multiplexable {
        /** Backend name */
        inline const char *name() const noexcept final { return "Multiplex"; }

        /** Log the given message */
        inline void log(CCSC id, const Level::Level &lvl, Util::LazyStr &&lazy) const final {
            log_str(id, lvl, lazy());
        }

        /** Log the given string message */
        inline void log_str(CCSC id, const Level::Level &lvl, std::string &&msg) const final {
            if (LIKELY(!backends.empty())) {
                const UInt loop_size { backends.size() - 1 };
                for (UInt i { 0 }; i < loop_size; ++i) {
                    const auto &bk { backends[i] };
                    UTIL_ASSERT_NOT_NULL_DEBUG(bk)
                    bk->log_str(id, lvl, std::string { msg });
                }
                backends.back()->log_str(id, lvl, std::move(msg));
            }
        }

        /** Flush logs */
        inline void flush() const final {
            for (const auto &i : backends) {
                i->flush();
            }
        }

        /** A container to store every backend: no backend pointers may be null */
        std::vector<std::shared_ptr<const Multiplexable>> backends; // NOLINT
    };

} // namespace Util::Log::Backend

#endif
