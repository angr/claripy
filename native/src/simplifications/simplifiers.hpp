/**
 * @file simplifiers.hpp
 * @brief Define simplifiers in Simplifications::Simplifiers
 */
#ifndef __SIMPLIFICATIONS_SIMPLIFIERS_HPP__
#define __SIMPLIFICATIONS_SIMPLIFIERS_HPP__

#include "../ast/using_declarations.hpp"
#include "../ops/operations_enum.hpp"

#include <memory>
#include <vector>


/** A namespace used for the simplifications directory */
namespace Simplifications {

    /** A namespace which contains the simplifiers */
    namespace Simplifiers {

        /************************************************/
        /*                 Miscellaneous                */
        /************************************************/

        /** Return if_true, if_false, or original depending on what cond evaluates to */
        AST::Base if_(const AST::Base &original, const AST::Bool &cond, const AST::Base &if_true,
                      const AST::Base &if_false);

        /** @todo document */
        AST::Base concat(const AST::Base &original, const std::vector<AST::Bool> args);

        /** @todo document */
        AST::Base bv_reverse(const AST::Base &original, const AST::Base &body);

        /************************************************/
        /*                    Shift                     */
        /************************************************/

        /** A namespace for shift simplifiers */
        namespace Shift {

            /** @todo document */
            AST::Base r(const AST::Base &original, const AST::Base &val, const AST::Base &shift);

            /** @todo document */
            AST::Base l(const AST::Base &original, const AST::Base &val, const AST::Base &shift);

            /** @todo document */
            AST::Base lshr(const AST::Base &original, const AST::Base &val,
                           const AST::Base &shift);
        } // namespace Shift

        /************************************************/
        /*                   Equality                   */
        /************************************************/

        /** @todo document */
        AST::Base eq(const AST::Base &original, const AST::Base &a, const AST::Base &b);

        /** @todo document */
        AST::Base ne(const AST::Base &original, const AST::Base &a, const AST::Base &b);

        /************************************************/
        /*                   Boolean                    */
        /************************************************/

        /** A namespace for boolean simplifiers */
        namespace Boolean {

            /** @todo document */
            AST::Base and_(const AST::Base &original, const std::vector<AST::Base> &args);

            /** @todo document */
            AST::Base or_(const AST::Base &original, const std::vector<AST::Base> &args);

            /** @todo document */
            AST::Base not_(const AST::Base &original, const std::vector<AST::Base> &);
        } // namespace Boolean

        /************************************************/
        /*                   Bitwise                    */
        /************************************************/

        /** A namespace for bitwise simplifiers */
        namespace Bitwise {

            /** @todo document */
            AST::Base add(const AST::Base &original, const std::vector<AST::Base> &args);

            /** @todo document */
            AST::Base mul(const AST::Base &original, const std::vector<AST::Base> &args);

            /** @todo document */
            AST::Base sub(const AST::Base &original, const AST::Base &a, const AST::Base &b);

            /** @todo document */
            AST::Base xor_minmax(const AST::Base &original, const AST::Base &a,
                                 const AST::Base &b);

            /** @todo document */
            AST::Base or_(const AST::Base &original, const AST::Base &a, const AST::Base &b,
                          const std::vector<AST::Base> &args);

            /** @todo document */
            AST::Base and_(const AST::Base &original, const AST::Base &a, const AST::Base &b,
                           const std::vector<AST::Base> &args);

            /** @todo document */
            AST::Base xor_(const AST::Base &original, const AST::Base &a, const AST::Base &b,
                           const std::vector<AST::Base> &args);
        } // namespace Bitwise

    } // namespace Simplifiers

} // namespace Simplifications

#endif
