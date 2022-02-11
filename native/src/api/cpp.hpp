/**
 * @file
 * @brief This header exposes the C API and C++ API helper functions
 * \ingroup api
 */
#ifndef R_API_CPP_HPP_
#define R_API_CPP_HPP_

extern "C" {
#include "../api.h"
};
#include "../backend.hpp"


// Static checks

/** A local macro used for static tests */
#define SAME_U(A, B) (sizeof(A) == sizeof(B) && std::is_unsigned_v<A> && std::is_unsigned_v<B>)

static_assert(SAME_U(UINT, UInt), "UINT needs to be changed");
static_assert(SAME_U(std::size_t, UInt), "UInt needs to be changed");
static_assert(SAME_U(SIZE_T, UInt), "UInt needs to be changed");
static_assert(SAME_U(VS_T, PyObj::Base::Ref), "VS_T needs to be changed");
static_assert(SAME_U(HASH_T, Hash::Hash), "HASH_T needs to be changed");

static_assert(std::is_same_v<UINT, CUID_T>, "CUID_T needs to be changed");
static_assert(std::is_same_v<const decltype(ClaricppPrimUnion::vs), decltype(PyObj::Base::ref)>,
              "Z3U needs to be changed");
static_assert(std::is_same_v<Z3U, unsigned>, "Z3U needs to be changed");
static_assert(std::is_same_v<CCSC, PyStr>, "PyStr needs to be changed");
static_assert(std::is_same_v<PyStr, ARRAY_IN(char)>, "ARRAY_IN needs to be changed");
static_assert((FALSE == false) && (false == FALSE) && (TRUE == true) && (true == TRUE),
              "BOOL values need to be fixed");

// Cleanup
#undef SAME_U


/********************************************************************/
/*                               C++                                */
/********************************************************************/


namespace API {

    namespace Private {
        /** Bidirectionally maps between C++ and C types
         *  CTypes are keys which must be defined in constants.h via DECLARE_WRAPPER
         *  CppTypes must be either std::shared_ptr's or raw pointers
         */
        using TypeMap = Util::Type::Map<                       //
            ClaricppAnnotation, Annotation::BasePtr,           // Annotations
            ClaricppSPAV, Annotation::SPAV,                    // SPAVs
            ClaricppExpr, Expr::BasePtr,                       // Exprs
            ClaricppBackend, std::shared_ptr<::Backend::Base>, // Backends
            ClaricppSolver, std::shared_ptr<z3::solver>        // Solvers
            >;

        /** Maps a C type to a C array type
         *  Values must be ARRAY_OUT() of their Keys
         */
        using ArrMap = Util::Type::Map<                             //
            ClaricppAnnotation, ARRAY_OUT(ClaricppAnnotation),      // Annotation
            ClaricppExpr, ARRAY_OUT(ClaricppExpr),                  // Expr
            ClaricppArg, ARRAY_OUT(ClaricppArg),                    // Arg
            ClaricppPrim, ARRAY_OUT(ClaricppPrim),                  // Prim
            ARRAY_OUT(ClaricppPrim), DOUBLE_ARRAY_OUT(ClaricppPrim) // Prim array
            >;

        /** Bidirectionally maps between C++ and C strong / weak enums
         *  Warning: Enums are assumed to have the same values between both
         */
        using EnumMap = Util::Type::Map<             //
            ClaricppLogLvl, Util::Log::Level::Level, // Log Level
            ClaricppRM, Mode::FP::Rounding,          // Rounding Mode
            ClaricppBIM, Mode::BigInt                // Big Int
            >;

        /** Bidirectionally maps between C++ and C variants / unions */
        using UnionMap = Util::Type::Map<ClaricppPrim, Op::PrimVar, ClaricppArg, Op::ArgVar>;

        /** A TypeMap abbreviation */
        template <typename T> using Map = TypeMap::template Get<T>;

        /** Heap cache; key type is in C++ */
        template <typename T> static thread_local Util::HeapCache<T> cache {};

    } // namespace Private

    // To CPP

    /** Returns a reference to the C++ type held by the C type x
     *  Warning: Returns a reference to part of x
     */
    template <typename InC> inline auto &to_cpp(const InC &x) NOEXCEPT_UNLESS_DEBUG {
        UTIL_ASSERT_NOT_NULL_DEBUG(x.ptr);
        return *static_cast<Private::Map<InC> *const>(x.ptr);
    }

    /** Returns a reference to the dereference of the C++ type held by the C type x
     *  Warning: Returns a reference to part of x
     */
    template <typename InC> inline auto &to_cpp_ref(const InC &x) NOEXCEPT_UNLESS_DEBUG {
        auto ptr { to_cpp(x) };
        UTIL_ASSERT_NOT_NULL_DEBUG(ptr);
        return *ptr;
    }

    /** Dereferences in after converting it to its C++ type; then down casts it to Out
     *  If the dynamic_cast fails, an exception is thrown
     *  If *(in.ptr) == nullptr, an exception is thrown
     *  Constness is applied as needed to out
     */
    template <typename Out, typename CType> inline auto &to_cpp_down_ref(const CType &in) {
        try {
            auto &ref { to_cpp_ref(in) };
            using RealOut = Util::Type::TransferConst<Out, decltype(ref)>;
            return dynamic_cast<RealOut &>(ref);
        }
        catch (std::bad_cast &e) {
            UTIL_THROW(Util::Err::BadCast, e.what());
        }
    }

    /** Returns an op container containing len operands */
    inline Op::FlatArgs to_op_args(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len) {
        Op::FlatArgs ops;
        ops.reserve(len);
        for (UInt i = 0; i < len; ++i) {
            ops.emplace_back(to_cpp(operands[i]));
        }
        return ops;
    }

    // To C

    /** Heap cache function
     *  @todo: make this inc a reference count for much greater speed
     */
    template <typename InCpp> inline auto to_c(InCpp &&x) {
        static_assert(!std::is_reference_v<InCpp>, "Did you mean to std::move this?");
        return Private::Map<InCpp> { Private::cache<InCpp>.move_to_heap(std::move(x)) };
    }

    /** Heap cache function; prefer to_c! Use this when x cannot be moved for some reason. */
    template <typename InCpp> inline auto copy_to_c(const InCpp &x) { return to_c(InCpp { x }); }

    /** Heap cache function with emplacement */
    template <typename InCpp, typename... Args> inline auto emplace_to_c(Args &&...args) {
        return Private::Map<InCpp> { Private::cache<InCpp>.emplace_on_heap(
            std::forward<Args>(args)...) };
    }

    /** Return a dynamically allocated string containing s */
    inline const char *c_str(CCSC s, const UInt len) {
        char *ret { new char[len + 1] };
        std::memcpy(ret, s, len);
        ret[len] = 0;
        return ret;
    }

    /** Return a dynamically allocated string containing s */
    inline const char *c_str(const std::string &s) { return c_str(s.data(), s.size()); }

    namespace Private {
        /** Return a corresponding array-type of CTypes of size len */
        template <typename CType> auto new_arr(const SIZE_T len) {
            Util::Log::verbose("Allocating an array of C types of length: ", len);
            using Wrapper = typename Private::ArrMap::template GetValue<CType>;
            return Wrapper { .arr = new CType[len], .len = len };
        }

        /** Convert a C++ vector to a C array */
        template <typename InCpp, typename CType, typename ToC>
        inline auto to_arr(std::vector<InCpp> &&arr, const ToC &to_c) {
            auto ret { Private::new_arr<CType>(arr.size()) };
            for (SIZE_T i { 0 }; i < ret.len; ++i) {
                ret.arr[i] = to_c(std::move(arr[i]));
            }
            arr.clear();
            return ret;
        }
    } // namespace Private

    /** Convert a C++ vector to a C array */
    template <typename InCpp> inline auto to_arr(std::vector<InCpp> &&arr) {
        using CType = decltype(API::to_c(std::move(arr[0])));
        return Private::to_arr<InCpp, CType>(std::move(arr), API::to_c<InCpp>);
    }

    /** Convert a C++ vector to a C array */
    template <typename InCpp> inline auto copy_to_arr(const std::vector<InCpp> &arr) {
        return to_arr(std::vector<InCpp> { arr });
    }

    /** Convert a C++ vector of vectors to a C array of arrays */
    template <typename InCpp> inline auto to_double_arr(std::vector<std::vector<InCpp>> &&d_arr) {
        using CType = decltype(API::to_arr(std::move(d_arr[0])));
        return Private::to_arr<std::vector<InCpp>, CType>(std::move(d_arr), API::to_arr<InCpp>);
    }

    /** Convert a C++ vector of vectors to a C array of arrays */
    template <typename InCpp>
    inline auto copy_to_double_arr(const std::vector<std::vector<InCpp>> &d_arr) {
        return to_double_arr(std::vector<std::vector<InCpp>> { d_arr });
    }

    // Other conversions

    /** Converts between a C++ strong enums and C weak enums
     *  Currently supported conversions:
     *  1. Mode::FP::Rounding <-> ClaricppRM
     */
    template <typename In> constexpr auto mode(const In in) noexcept {
        using Ret = typename Private::EnumMap::template Get<In>;
        return static_cast<Ret>(in);
    }

    /** Converts between a C and C++ bool */
    template <typename In> constexpr auto bool_(const In in) noexcept {
        return static_cast<std::conditional_t<std::is_same_v<In, bool>, BOOL, bool>>(in);
    }

    // Variants / Unions

/** A local macro used for consistency */
#define CASE(INDEX, TYPE)                                                                          \
    case INDEX: {                                                                                  \
        UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(in, INDEX, TYPE);                              \
        TYPE &got { std::get<INDEX>(in) };
/** A local macro used for consistency */
#define CASE_END }
/** A local macro used for consistency */
#define TRIVIAL_CASE(INDEX, TYPE, NAME, ETYPE)                                                     \
    CASE(INDEX, TYPE);                                                                             \
    return { { .NAME = got }, ETYPE };                                                             \
    CASE_END

    namespace Private {
        /** Converts Var into a ClaricppPrim, throws an exception on failure if not MayFail
         *  If MayFail and failure occurs, success is set to false and the output is undefined
         */
        template <typename Var, bool MayFail = false>
        ClaricppPrim prim_var(Var &in, bool &success) {
            success = true;
            switch (in.index()) {
                // Literal types
                TRIVIAL_CASE(0, bool, boolean, ClaricppTypeEnumBool)
                CASE(1, std::string) { return { { .str = API::c_str(got) }, ClaricppTypeEnumStr }; }
                CASE_END
                TRIVIAL_CASE(2, float, flt, ClaricppTypeEnumFloat)
                TRIVIAL_CASE(3, double, dbl, ClaricppTypeEnumDouble)
                CASE(4, PyObj::VSPtr) { return { { .vs = got->ref }, ClaricppTypeEnumVS }; }
                CASE_END
                /* Literal BV types */
                TRIVIAL_CASE(5, uint8_t, u8, ClaricppTypeEnumU8)
                TRIVIAL_CASE(6, uint16_t, u16, ClaricppTypeEnumU16)
                TRIVIAL_CASE(7, uint32_t, u32, ClaricppTypeEnumU32)
                TRIVIAL_CASE(8, uint64_t, u64, ClaricppTypeEnumU64)
                /* Other */
                CASE(9, BigInt) {
                    got.convert<BigInt::Mode::Str>();
                    const std::string &gstr { std::get<std::string>(got.value) };
                    char *const ret { new char[gstr.size() + 1] };
                    std::memcpy(ret, gstr.c_str(), gstr.size());
                    return { { .big_int = ret }, ClaricppTypeEnumBigInt };
                }
                CASE_END
                default: {
                    // Failure
                    success = false;
                    if constexpr (MayFail) {
                        return ClaricppPrim {}; // Garbage data
                    }
                    UTIL_THROW(Util::Err::Unknown, "Variant shouldn't have this index");
                }
            }
        };
    } // namespace Private

    /** A specialization of to_c for Op::PrimVar
     *  Convert an Op::PrimVar to a C ClaricppPrim
     *  Note: Strings are dynamically allocated
     */
    template <> inline auto to_c<Op::PrimVar>(Op::PrimVar &&in) {
        static bool b { true };
        return Private::prim_var(in, b);
    }

    /** A specialization of to_c for Op::ArgVar
     *  Convert an Op::ArgVar to a C ClaricppArg
     *  Note: Strings are dynamically allocated
     */
    template <> inline auto to_c<Op::ArgVar>(Op::ArgVar &&in) {
        bool success; // NOLINT
        const auto ret { Private::prim_var<Op::ArgVar, true>(in, success) };
        if (success) {
            return ClaricppArg { { .prim = ret.data }, ret.type }; // NOLINT (not a memory leak)
        }
        switch (in.index()) {
            CASE(10, Expr::BasePtr) {
                return ClaricppArg { { .expr = to_c(std::move(got)) }, ClaricppTypeEnumExpr };
            }
            CASE_END
            CASE(11, Mode::FP::Rounding) {
                return ClaricppArg { { .rounding_mode = API::mode(got) }, ClaricppTypeEnumRM };
            }
            CASE_END
            CASE(12, Mode::FP::Width) {
                const auto w { (got == Mode::FP::dbl) ? ClaricppWidthDouble : ClaricppWidthFloat };
                return ClaricppArg { { .width = w }, ClaricppTypeEnumWidth };
            }
            CASE_END
            default:
                UTIL_THROW(Util::Err::Unknown, "Variant shouldn't have this index");
        }
    }

// Cleanup
#undef TRIVIAL_CASE
#undef CASE_END
#undef CASE

    // Cleanup functions

    // Forward declaration
    template <typename InC> inline void free_union(InC &x);

    /** Multi-array-optional Heap cache free function
     *  @todo: make to_c inc a reference count and this dec one for much greater speed
     */
    template <unsigned ArrayLayer, typename InC> inline void free(InC &x) {
        if constexpr (ArrayLayer == 0) {
            if constexpr (Private::TypeMap::template contains<InC>) {
                if (x.ptr != nullptr) {
                    Private::cache<Private::Map<InC>>.free(&to_cpp(x));
                    x.ptr = nullptr;
                }
            }
            else {
                free_union(x);
            }
        }
        else {
            if (x.arr != nullptr) {
                for (SIZE_T i { 0 }; i < x.len; ++i) {
                    API::free<ArrayLayer - 1>(x.arr[i]); // NOLINT (false positive)
                }
                delete[](x.arr); // NOLINT (false positive)
                x.arr = nullptr;
            }
            else if (x.len > 0) {
                Util::Log::error(WHOAMI "Array being freed has null data but non-zero length");
                // No need to throw probably
            }
            x.len = 0;
        }
    }

    /** Non-array Heap cache free function */
    template <typename InC> inline void free(InC &x) { free<0, InC>(x); }

    /** Used to free a C type in UnionMap */
    template <typename InC> inline void free_union(InC &x) {
        static_assert(Private::UnionMap::template contains<InC>, "Can't free this");
        if constexpr (std::is_same_v<InC, ClaricppArg>) {
            if (x.type == ClaricppTypeEnumExpr) {
                API::free(x.data.expr);
            }
            else if (x.type == ClaricppTypeEnumBigInt) {
                delete[](x.data.prim.big_int); // Safe b/c memory is from new
                x.data.prim.big_int = nullptr;
            }
            else if (x.type == ClaricppTypeEnumStr) {
                delete[](x.data.prim.str); // Safe b/c memory is from new
                x.data.prim.str = nullptr;
            }
        }
        else if constexpr (std::is_same_v<InC, ClaricppPrim>) {
            if (x.type == ClaricppTypeEnumStr) {
                delete[](x.data.str); // Safe b/c memory is from new
                x.data.str = nullptr;
            }
        }
        else {
            static_assert(Util::TD::false_<InC>, "Needs implementation");
        }
    }

    // Exceptions

    /** A thread local exception pointer */
    extern thread_local std::exception_ptr exception_ptr;

/** Starts the exception handling
 *  Call at the beginning of every API function that can throw exceptions
 */
#define API_FUNC_START                                                                             \
    API::exception_ptr = nullptr;                                                                  \
    try {

// @todo exception tests

/** Call at the end of every API function
 *  Ends the exception handling
 *  Does not call return
 */
#define API_FUNC_END_NO_RETURN                                                                     \
    }                                                                                              \
    catch (...) {                                                                                  \
        API::exception_ptr = std::current_exception();                                             \
    }

/** Call at the end of every API function
 *  Ends the exception handling
 *  returns {}
 *  @todo: maybe no return?
 */
#define API_FUNC_END                                                                               \
    API_FUNC_END_NO_RETURN;                                                                        \
    return {};

} // namespace API

#endif
