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

/** A local macro used for error checking in debug mode */
#define ASSERT_ARG_LEN_DEBUG(X, N)                                                                \
    Utils::affirm<Utils::Error::Unexpected::Size>((X).size() == (N), WHOAMI_WITH_SOURCE           \
                                                  "container should have " #N " elements");

    /**********************************************************/
    /*                        General                         */
    /**********************************************************/

    /** Abstraction function for Z3_OP_UNINTERPRETED */
    inline auto uninterpreted(const z3::func_decl &decl, const Z3_decl_kind decl_kind,
                              const z3::sort &sort, std::vector<Expression::BasePtr> &args) {
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

/** A local macro used for consistency */
#define EQ_CASE(T)                                                                                \
    case T::static_cuid:                                                                          \
        return Create::eq<T>(std::move(args[0]), std::move(args[1]));

    /** Abstraction function for Z3_OP_EQ */
    inline auto eq(std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN_DEBUG(args, 2);
        namespace Ex = Expression;
        switch (args[0]->cuid) {
            EQ_CASE(Ex::Bool);
            EQ_CASE(Ex::BV);
            EQ_CASE(Ex::FP);
            EQ_CASE(Ex::String);
            default:
                throw Utils::Error::Unexpected::Type(
                    WHOAMI_WITH_SOURCE, "Unexpected type detected. CUID: ", args[0]->cuid);
        };
    }

// Cleanup
#undef EQ_CASE

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
    inline auto sign_ext(const z3::func_decl &decl, std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN_DEBUG(args, 1);
        const auto val { static_cast<z3u>(
            Z3_get_decl_int_parameter(Private::tl_raw_ctx, decl, 0)) };
        return Create::sign_ext(args[0], Utils::widen<Constants::UInt>(val));
    }

    /** Abstraction function for Z3_OP_ZERO_EXT */
    inline auto zero_ext(const z3::func_decl &decl, std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN_DEBUG(args, 1);
        const auto val { static_cast<z3u>(
            Z3_get_decl_int_parameter(Private::tl_raw_ctx, decl, 0)) };
        return Create::sign_ext(args[0], Utils::widen<Constants::UInt>(val));
    }

    /** Abstraction function for Z3_OP_EXTRACT */
    inline auto extract(Constants::CTSC<z3::expr> b_obj, std::vector<Expression::BasePtr> &args) {
        ASSERT_ARG_LEN_DEBUG(args, 1);
        return Create::extract(b_obj->hi(), b_obj->lo(), std::move(args[0]));
    }

    /**********************************************************/
    /*                     Floating Point                     */
    /**********************************************************/

    // FP Conversions

    // FP Constants

    // FP Comparisons

    // FP Arithmetic

// Cleanup
#undef ASSERT_ARG_LEN_DEBUG

} // namespace Backend::Z3::Abstract

#endif
