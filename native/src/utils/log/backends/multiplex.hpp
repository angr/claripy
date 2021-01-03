/**
 * @file
 * \ingroup utils
 * @brief This file defines the multiplex log backend
 */
#ifndef __UTILS_LOG_BACKEND_MULTIPLEX_HPP__
#define __UTILS_LOG_BACKEND_MULTIPLEX_HPP__

#include "abstract_base.hpp"

#include <memory>
#include <set>


namespace Utils::Log::Backend {

    /** The multiplex backend
     *  This backend logs to multiple backends
     */
    struct Multiplex : public std::set<std::shared_ptr<AbstractBase>> {

        /** Used to emplace T */
        template <typename T, typename... Args> auto emplace(Args &...args) {
            static_assert(
                std::is_base_of_v<AbstractBase, T>,
                "Multiplex will only emplace subclasses of the log backend AbstractBase");
            const auto ptr = std::make_shared<T>(args...);
            return this->insert(std::static_pointer_cast<AbstractBase>(ptr));
        }

        /** Log the given message, level, to the correct log given by log_id with each backend */
        void log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg);
    };

} // namespace Utils::Log::Backend

#endif
