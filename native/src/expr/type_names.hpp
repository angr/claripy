/**
 * @file
 * @brief This file defines method of getting the type names of a parameter pack of Expr types
 */
#ifndef R_SRC_EXPR_TYPENAMES_HPP_
#define R_SRC_EXPR_TYPENAMES_HPP_

namespace Expr {

    namespace Private {
        /** Lists the names of given op types */
        template <typename Head, typename... Tail>
        constexpr void generate_type_names(std::ostringstream &o) {
            o << Head::static_type_name;
            if constexpr (sizeof...(Tail) > 0) {
                o << ", ";
                generate_type_names<Tail...>(o);
            }
        }
    } // namespace Private

    /** A struct which can list the type names of the types it holds
     *  We make this a functor class to lazily construct the string
     */
    template <typename... Types> struct TypeNames {
        /** Lists the names of given op types */
        const std::string &operator()() const {
            static bool first { true };
            static std::string out {};
            if (UNLIKELY(first)) {
                std::ostringstream o;
                Private::generate_type_names<Types...>(o); // Populate o
                out = o.str();
                first = false;
            }
            return out;
        }
    };

    /** Allow ostream usage of TypeNames */
    template <typename... Args>
    std::ostream &operator<<(std::ostream &o, const TypeNames<Args...> &tn) {
        return o << tn();
    }

} // namespace Expr

#endif
