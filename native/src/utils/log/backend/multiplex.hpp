/**
 * @file
 * \ingroup utils
 * @brief This file defines the multiplex log backend
 */
#ifndef __UTILS_LOG_BACKEND_MULTIPLEX_HPP__
#define __UTILS_LOG_BACKEND_MULTIPLEX_HPP__

#include "abstract_base.hpp"

#include "../../thread_safe_access.hpp"

#include <memory>
#include <vector>


namespace Utils::Log::Backend {

    /** The multiplex backend
     *  This backend logs to multiple backends
     *  This class is not thread safe when written to after installed as a backend
     */
    struct Multiplex : public AbstractBase {

        /** Log the given message, level, to the correct log given by log_id with each backend */
        void log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg);

        /** Backend container type */
        using BackendContainer = std::vector<std::shared_ptr<AbstractBase>>;

        /** Store each backend */
        ThreadSafeAccess<const BackendContainer> backends;
    };

} // namespace Utils::Log::Backend

#endif
