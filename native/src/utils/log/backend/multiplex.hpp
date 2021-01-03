/**
 * @file
 * \ingroup utils
 * @brief This file defines the multiplex log backend
 */
#ifndef __UTILS_LOG_BACKEND_MULTIPLEX_HPP__
#define __UTILS_LOG_BACKEND_MULTIPLEX_HPP__

#include "abstract_base.hpp"

#include <memory>
#include <type_traits>
#include <vector>


namespace Utils::Log::Backend {

    /** The multiplex backend
     *  This backend logs to multiple backends
     *  This class is not thread safe when written to after installed as a backend
     */
    struct Multiplex : public AbstractBase, public std::vector<std::shared_ptr<AbstractBase>> {

        /** The superclass */
        using Parent = std::vector<std::shared_ptr<AbstractBase>>;

        /** Use parent constructors
         *  This also statically asserts that Parent is Multiplex's parent
         */
        using Parent::Parent;

        /** Used to emplace T */
        template <typename T, typename... Args> auto emplace_back(Args &...args) {
            static_assert(
                std::is_base_of_v<AbstractBase, T>,
                "Multiplex will only emplace subclasses of the log backend AbstractBase");
            return Parent::emplace_back(new T(args...));
        }

        /** Log the given message, level, to the correct log given by log_id with each backend */
        void log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg);
    };

} // namespace Utils::Log::Backend

#endif
