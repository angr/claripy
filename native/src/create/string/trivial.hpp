/**
 * @file
 * @brief This file defines a group of create methods for trivial passthrough string ops
 */
#ifndef R_CREATE_STRING_TRIVIAL_HPP_
#define R_CREATE_STRING_TRIVIAL_HPP_

#include "../private/binary.hpp"
#include "../private/uint_binary.hpp"
#include "../private/unary.hpp"


namespace Create::String {

    /********************************************************************/
    /*                   Unary Passthrough Functions                    */
    /********************************************************************/

    /** Create a bool Expr with an String::IsDigit op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr is_digit(const Expr::BasePtr &x, Annotation::SPAV &&sp = nullptr) {
        namespace CP = ::Create::Private;
        return CP::unary_explicit<Expr::Bool, Op::String::IsDigit, Expr::String>(x, std::move(sp));
    }

    /********************************************************************/
    /*                 Int Binary Passthrough Functions                 */
    /********************************************************************/

    /** Create an Expr with an String::SignExt op
     *  Note: Currently Ints are taken in as BVs
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr to_int(const Expr::BasePtr &expr, const UInt integer,
                                Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        namespace CP = ::Create::Private;
        return CP::uint_binary<UInt, Ex::BV, Ex::String, Op::String::ToInt, CP::SizeMode::Second,
                               Ex::String>(expr, integer, std::move(sp));
    }

    /** Create an Expr with an String::Len op
     *  Note: Currently Ints are output as BVs
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr len(const Expr::BasePtr &expr, const UInt integer,
                             Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        namespace CP = ::Create::Private;
        return CP::uint_binary<UInt, Ex::BV, Ex::String, Op::String::Len, CP::SizeMode::Second,
                               Ex::String>(expr, integer, std::move(sp));
    }

    /********************************************************************/
    /*                   Binary Passthrough Functions                   */
    /********************************************************************/

    /** Create an Expr with a String::Contains op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr contains(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                  Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        namespace CP = ::Create::Private;
        return CP::binary<Ex::Bool, Ex::String, Op::String::Contains, CP::SizeMode::NA,
                          Ex::String>(left, right, std::move(sp));
    }

    /** Create an Expr with a String::PrefixOf op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr prefix_of(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                   Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        namespace CP = ::Create::Private;
        return CP::binary<Ex::Bool, Ex::String, Op::String::PrefixOf, CP::SizeMode::NA,
                          Ex::String>(left, right, std::move(sp));
    }

    /** Create an Expr with a String::SuffixOf op
     *  Expr pointers may not be nullptr
     */
    inline Expr::BasePtr suffix_of(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                   Annotation::SPAV &&sp = nullptr) {
        namespace Ex = Expr;
        namespace CP = ::Create::Private;
        return CP::binary<Ex::Bool, Ex::String, Op::String::SuffixOf, CP::SizeMode::NA,
                          Ex::String>(left, right, std::move(sp));
    }

} // namespace Create::String

#endif
