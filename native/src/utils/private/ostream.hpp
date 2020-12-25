/**
 * @file
 * @brief This file defines an ostream operator wrapper that can be passed to Utils::apply
 */
#ifndef __UTILS_PRIVATE_OSTREAM_HPP__
#define __UTILS_PRIVATE_OSTREAM_HPP__

#include "../../macros.hpp"


namespace Utils::Private {

    /** An ostream wrapper that can be passed to Utils::apply
     *  This allows passing around a class rather than templated functions directly
     */
    struct OStreamConst {

        /** A function which wraps the ostream operator but returns nothing */
        template <typename T, typename U> static void f(T &left, const U &right) { left << right; }

      private:
        /** Disable construction */
        DELETE_DEFAULTS(OStreamConst)
        /** Disable destruction */
        ~OStreamConst() = delete;
    };

} // namespace Utils::Private

#endif
