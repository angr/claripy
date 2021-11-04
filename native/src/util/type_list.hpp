#ifndef R_UTIL_TYPELIST_HPP_
#define R_UTIL_TYPELIST_HPP_

#include "unconstructable.hpp"


namespace Util {

    /** An uninstantiable type list class */
    template <typename... Args> struct TypeList : private Unconstructable {

        /** Return TypeList<Args..., Other...> */
        template <typename... Other> using Append = TypeList<Args..., Other...>;

        /** Return TypeList<Other..., Args...> */
        template <typename... Other> using Prepend = TypeList<Other..., Args...>;

        /** Return a Container<Args...> */
        template <template <typename...> typename Container> using Apply = Container<Args...>;
    };

} // namespace Util

#endif
