/**
 * @file
 * @brief This file defines how the Z3 backend converts Z3 ASTs into Claricpp Expressions
 */
#ifndef R_BACKEND_Z3_ABSTRACT_HPP_
#define R_BACKEND_Z3_ABSTRACT_HPP_

#include "constants.hpp"
#include "tl_ctx.hpp"

#include "../../create.hpp"


namespace Backend::Z3::Abstract {

/** A local macro used for lengh checking a container */
#define ASSERT_ARG_LEN(X, N)                                                                      \
    Utils::affirm<Utils::Error::Unexpected::Size>((X).size() == (N), WHOAMI_WITH_SOURCE           \
                                                  "container should have " #N " elements");

/** A local macro used for adding a case for a given type
 *  Func must be take in T as its only template argument
 */
#define TYPE_CASE(TYPE, FUNC, ...)                                                                \
    case Expression::TYPE::static_cuid:                                                           \
        return FUNC<Expression::TYPE>(__VA_ARGS__);

/** A local macro used for adding a case for a given type
 *  Func must take in <TYPE, T2> as its template arguments
 */
#define TYPE_CASE_2(TYPE, T2, FUNC, ...)                                                          \
    case Expression::TYPE::static_cuid:                                                           \
        return FUNC<Expression::TYPE, T2>(__VA_ARGS__);

/** A local macro used for adding a default type case that throws an exception */
#define DEFAULT_TYPE_CASE(BAD_CUID)                                                               \
    default:                                                                                      \
        throw Utils::Error::Unexpected::Type(WHOAMI_WITH_SOURCE,                                  \
                                             "Unexpected type detected. CUID: ", (BAD_CUID));

    /**********************************************************/
    /*                        General                         */
    /**********************************************************/

    /** Abstraction function for Z3_OP_UNINTERPRETED */
    inline auto uninterpreted(const z3::func_decl &decl, const Z3_decl_kind decl_kind,
                              const z3::sort &sort, const std::vector<Expression::BasePtr> &args) {
        {
            // If b_obj is a symbolic value
            if (args.empty()) {
                // Gather info
                std::string name { decl.name().str() };
                auto symbol_type { sort.sort_kind() };
                switch (symbol_type) {
                    case Z3_BV_SORT:
                        /* const auto bl { sort.bv_size() }; */
                        /* bv_size = z3.Z3_get_bv_sort_size(ctx, z3_sort) */
                        /* (ast_args, annots) = self.extra_bvs_data.get(symbol_name, (None,
                         * None)) */
                        /* if ast_args is None: */
                        /*     ast_args = (symbol_str, None, None, None, False, False,
                         * None) */
                        /* return Create::symbol(std::move(name), bl, ans); // probably?
                         * TODO: */
                        return nullptr;
                    case Z3_BOOL_SORT:
                    case Z3_FLOATING_POINT_SORT:
                    default:
                        throw Error::Backend::Abstraction(
                            WHOAMI_WITH_SOURCE "Unknown term type: ", symbol_type,
                            "\nOp decl_kind: ", decl_kind, "\nPlease report this.");
                }
            }
            // Unknown error
            else {
                throw Error::Backend::Abstraction(
                    WHOAMI_WITH_SOURCE "Uninterpreted z3 op with args given. Op decl_kind: ",
                    decl_kind, "\nPlease report this.");
            }
        }
    }

    // Booleans

    /** A boolean expression
     *  Warning: Should not be inline b/c of ODR rules
     */
    template <bool B> const auto bool_ { Create::literal(B) };

    // Boolean logic

    /** Abstraction function for Z3_OP_EQ */
    inline auto eq(const std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN(args, 2);
        switch (args[0]->cuid) {
            TYPE_CASE(Bool, Create::eq, args[0], args[1]);
            TYPE_CASE(BV, Create::eq, args[0], args[1]);
            TYPE_CASE(FP, Create::eq, args[0], args[1]);
            TYPE_CASE(String, Create::eq, args[0], args[1]);
            DEFAULT_TYPE_CASE(args[0]->cuid);
        };
    }

// Cleanup
#undef EQ_CASE

    // Arithmetic

    // Comparisons

    /** Abstraction function ofr various Z3 comparison ops */
    template <Mode::Compare Mask>
    inline auto compare(const std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN(args, 2);
        if constexpr (Utils::BitMask::has(Mask, Mode::Compare::Unsigned)) {
            return Create::compare<Expression::BV, Mask>(args[0], args[1]);
        }
        else {
            switch (args[0]->cuid) {
                TYPE_CASE_2(FP, Mask, Create::compare, args[0], args[1]);
                TYPE_CASE_2(BV, Mask, Create::compare, args[0], args[1]);
                DEFAULT_TYPE_CASE(args[0]->cuid);
            };
        }
    }

    /**********************************************************/
    /*                      Bit Vectors                       */
    /**********************************************************/

    /** Abstraction function for Z3_OP_BNUM */
    inline auto bnum(Constants::CTSC<z3::expr> b_obj, const z3::sort &sort) {
        // Get the bv number
        uint64_t bv_num; // NOLINT
        if (!b_obj->is_numeral_u64(bv_num)) {
            std::string tmp;
            const bool success { b_obj->is_numeral(tmp) };
            Utils::affirm<Utils::Error::Unexpected::Type>(success, WHOAMI_WITH_SOURCE
                                                          "given z3 object is not a numeral");
            bv_num = std::stoull(tmp); // Faster than istringstream
            static_assert(sizeof(unsigned long long) == sizeof(uint64_t),
                          "Bad string conversion function called");
        }
        // Type pun to vector of bytes
        std::vector<std::byte> data;
        data.reserve(sizeof(bv_num));
        std::memcpy(data.data(), &bv_num, sizeof(bv_num));
        // Size check
        const auto bl { sort.bv_size() };
        Utils::affirm<Utils::Error::Unexpected::Size>(
            sizeof(bv_num) == bl * 8,
            WHOAMI_WITH_SOURCE "Int to BV type pun failed because the requested BV size"
                               "size is ",
            bl, " bits long where as the integer type is only ", sizeof(bv_num) * 8,
            "bytes long.");
        // Return literal
        return Create::literal(std::move(data));
    }

    // Bit Vector Arithemitic

    // Bit Vector Logic

    // Bit Vector Bitwise Ops

    // Bit Vector Misc

    /** Abstraction function for Z3_OP_SIGN_EXT */
    inline auto sign_ext(const z3::func_decl &decl, const std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN(args, 1);
        const auto val { static_cast<z3u>(
            Z3_get_decl_int_parameter(Private::tl_raw_ctx, decl, 0)) };
        return Create::sign_ext(args[0], Utils::widen<Constants::UInt>(val));
    }

    /** Abstraction function for Z3_OP_ZERO_EXT */
    inline auto zero_ext(const z3::func_decl &decl, const std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN(args, 1);
        const auto val { static_cast<z3u>(
            Z3_get_decl_int_parameter(Private::tl_raw_ctx, decl, 0)) };
        return Create::sign_ext(args[0], Utils::widen<Constants::UInt>(val));
    }

    /** Abstraction function for Z3_OP_EXTRACT */
    inline auto extract(Constants::CTSC<z3::expr> b_obj,
                        const std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN(args, 1);
        return Create::extract(b_obj->hi(), b_obj->lo(), args[0]);
    }

    /**********************************************************/
    /*                     Floating Point                     */
    /**********************************************************/

    // FP Conversions

    // FP Constants

    // FP Comparisons

    // FP Arithmetic

// Cleanup
#undef DEFAULT_TYPE_CASE
#undef ASSERT_ARG_LEN
#undef TYPE_CASE_2
#undef TYPE_CASE

} // namespace Backend::Z3::Abstract

#endif
