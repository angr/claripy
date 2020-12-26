/**
 * @file
 * @brief This file defines an ostream operator wrapper that can be passed to Utils::apply
 * Additionally, this function statically casts strong enums to their underlying types
 */
#ifndef __UTILS_PRIVATE_OSTREAM_HPP__
#define __UTILS_PRIVATE_OSTREAM_HPP__

#include "ostream_helper_conversions.hpp"

#include "../../macros.hpp"


namespace Utils::Private {

    /** An ostream wrapper that can be passed to Utils::apply
     *  This allows passing around a class rather than templated functions directly
     * Additionally, this function statically casts strong enums to their underlying types
     */
    struct OStreamConst {

        /** A function which wraps the ostream operator but returns nothing */
        template <typename T, typename U> static void f(T &left, const U &right) {
            left << ostream_helper_conversions(right);
        }

      private:
        /** Disable construction */
        DELETE_DEFAULTS(OStreamConst)
        /** Disable destruction */
        ~OStreamConst() = delete;
    };

} // namespace Utils::Private

#endif
