/**
 * @file
 * \ingroup utils
 * @brief This file defines the multiplex log backend
 */
#ifndef R_UTILS_LOG_BACKEND_MULTIPLEX_HPP_
#define R_UTILS_LOG_BACKEND_MULTIPLEX_HPP_

#include "base.hpp"

#include "../../thread_safe.hpp"

#include <memory>
#include <vector>


namespace Utils::Log::Backend {

    /** The multiplex backend
     *  This backend logs to multiple backends
     *  This class is not thread safe when written to after installed as a backend
     */
    struct Multiplex final : public Base {

        /** Log the given message, level, to the correct log given by log_id with each backend */
        inline void log(Constants::CCSC id, const Level::Level &lvl,
                        const std::string &msg) const override final {
            for (const auto &i : backends) {
                i->log(id, lvl, msg);
            }
        }

        /** Store each backend */
        std::vector<std::shared_ptr<const Base>> backends;
    };

} // namespace Utils::Log::Backend

#endif
