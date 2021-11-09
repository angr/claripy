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

// @todo: Handle exceptions

// Static checks

/** A local macro used for static tests */
#define SAME_U(A, B) (sizeof(A) == sizeof(B) && std::is_unsigned_v<A> && std::is_unsigned_v<B>)

static_assert(SAME_U(UINT, UInt), "UINT needs to be changed");
static_assert(SAME_U(std::size_t, UInt), "UInt needs to be changed");
static_assert(SAME_U(SIZE_T, UInt), "UInt needs to be changed");
static_assert(SAME_U(VS_T, PyObj::Base::Ref), "VS_T needs to be changed");
static_assert(SAME_U(HASH_T, Hash::Hash), "HASH_T needs to be changed");

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
        /** Bidirectionally maps between C++ and C types */
        template <typename T> struct InternalMap;
        /** Maps a C type to a C array type */
        template <typename T> struct InternalArrMap;
        /** Bidirectionally maps between C++ and C types
         *  Warning: Enums are assumed to have the same values between both
         */
        template <typename T> struct InternalEnumMap;

/** A local macro used to add a Map entry */
#define MAP_ADD(CTYPE, CPPTYPE)                                                                    \
    static_assert(std::is_pod_v<CTYPE>, "Struct must be of the structure { void * ptr };");        \
    static_assert(sizeof(CTYPE) == sizeof(void *), "Struct should only contain a void *");         \
    static_assert(std::is_same_v<void *, decltype(std::declval<CTYPE>().ptr)>, "Bad ptr type");    \
    static_assert(Util::is_shared_ptr<CPPTYPE> || std::is_pointer_v<CPPTYPE>,                      \
                  "CPPTYPE should be a shared or raw pointer");                                    \
    template <> struct InternalMap<CPPTYPE> final { using Result = CTYPE; };                       \
    template <> struct InternalMap<CTYPE> final { using Result = CPPTYPE; };

/** A local macro used to add an array Map entry */
#define ARR_MAP_ADD(CTYPE)                                                                         \
    template <> struct InternalArrMap<CTYPE> final { using Result = ARRAY_OUT(CTYPE); };

/** A local macro used to add an Enum Map entry */
#define ENUM_MAP_ADD(CTYPE, CPPTYPE)                                                               \
    static_assert(std::is_enum_v<CTYPE>, "Must be an enum");                                       \
    static_assert(Util::is_strong_enum<CPPTYPE>, "Must be a strong enum");                         \
    template <> struct InternalEnumMap<CPPTYPE> final { using Result = CTYPE; };                   \
    template <> struct InternalEnumMap<CTYPE> final { using Result = CPPTYPE; };

        // Populate internal maps
        MAP_ADD(ClaricppAnnotation, Annotation::BasePtr);
        MAP_ADD(ClaricppSPAV, Annotation::SPAV);
        MAP_ADD(ClaricppExpr, Expr::BasePtr);
        MAP_ADD(ClaricppBackend, std::shared_ptr<::Backend::Base>);
        MAP_ADD(ClaricppSolver, std::shared_ptr<z3::solver>);

        ARR_MAP_ADD(ClaricppExpr);
        ARR_MAP_ADD(ClaricppPrim);

        ENUM_MAP_ADD(ClaricppRM, Mode::FP::Rounding);
        ENUM_MAP_ADD(ClaricppBIM, Mode::BigInt);

// Cleanup
#undef MAP_ADD
#undef ARR_MAP_ADD
#undef ENUM_MAP_ADD

        /** A shortcut used to access InternalMap */
        template <typename T> using Map = typename InternalMap<T>::Result;

        /** Heap cache; key type is in C++ */
        template <typename T> static thread_local Util::HeapCache<T> cache {};

    } // namespace Private

    // To CPP

    /** Returns a reference to the C++ type held by the C type x
     *  Warning: Returns a reference to part of x
     */
    template <typename InC> inline auto &to_cpp(const InC &x) noexcept {
        UTILS_AFFIRM_NOT_NULL_DEBUG(x.ptr);
        return *static_cast<Private::Map<InC> *const>(x.ptr);
    }

    /** Returns a reference to the dereference of the C++ type held by the C type x
     *  Warning: Returns a reference to part of x
     */
    template <typename InC> inline auto &to_cpp_ref(const InC &x) noexcept {
        auto ptr { to_cpp(x) };
        UTILS_AFFIRM_NOT_NULL_DEBUG(ptr);
        return *ptr;
    }

    /** Dereferences in after converting it to its C++ type; then down casts it to Out
     *  If the dynmaic_cast fails, an exception is thrown
     *  If *(in.ptr) == nullptr, an exception is thrown
     *  Constness is applied as needed to out
     */
    template <typename Out, typename CType> inline auto &to_cpp_down_ref(const CType &in) {
        try {
            auto &ref { to_cpp_ref(in) };
            return dynamic_cast<Util::TransferConst<Out, decltype(ref)> &>(ref);
        }
        catch (std::bad_cast &e) {
            throw Util::Err::BadCast(WHOAMI, e.what());
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

    /** Heap cache function */
    template <typename InCpp> inline auto to_c(InCpp &&x) {
        static_assert(!std::is_reference_v<InCpp>, "Did you mean to std::move this?");
        return Private::Map<InCpp> { Private::cache<InCpp>.move_to_heap(std::move(x)) };
    }

    /** Heap cache function; prefer to_c! Use this when x cannot be moved for some reason. */
    template <typename InCpp> inline auto copy_to_c(const InCpp &x) {
        InCpp tmp { x };
        return Private::Map<InCpp> { Private::cache<InCpp>.template emplace_on_heap(std::move(x)) };
    }

    /** Heap cache function with emplacement */
    template <typename InCpp, typename... Args> inline auto emplace_to_c(Args &&...args) {
        return Private::Map<InCpp> { Private::cache<InCpp>.emplace_on_heap(
            std::forward<Args>(args)...) };
    }

    /** Convert a C++ vector to a C array */
    template <typename InCpp> inline auto to_arr(std::vector<InCpp> &&arr) {
        using CType = decltype(API::to_c(std::move(arr[0])));
        typename Private::InternalArrMap<CType>::Result ret;
        // Array allocation
        ret.len = arr.size();
        Util::Log::debug("Allocating an array C types of length: ", ret.len);
        ret.arr = Util::Safe::malloc<CType>(ret.len);
        // Array population
        for (SIZE_T i { 0 }; i < ret.len; ++i) {
            ret.arr[i] = API::to_c(std::move(arr[i]));
        }
        // Cleanup and return
        arr.clear();
        return ret;
    }

    // Rounding mode

    /** Converts between a C++ strong enums and C weak enums
     *  Currently supported conversions:
     *  1. Mode::FP::Rounding <-> ClaricppRM
     */
    template <typename In> inline auto mode(const In in) noexcept {
        return typename Private::InternalEnumMap<In>::Result(in); // Must be (), not {}
    }

    // Variants / Unions

/** A local macro used for consistency */
#define CASE(INDEX, TYPE)                                                                          \
    case INDEX: {                                                                                  \
        UTILS_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(in, INDEX, TYPE);                             \
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
                TRIVIAL_CASE(0, bool, boolean, ClaricppPrimEnumBool)
                CASE(1, std::string) {
                    char *const ret { Util::Safe::malloc<char>(got.size() + 1) };
                    std::strcpy(ret, got.c_str());
                    return { { .str = ret }, ClaricppPrimEnumStr };
                }
                CASE_END
                TRIVIAL_CASE(2, float, flt, ClaricppPrimEnumFloat)
                TRIVIAL_CASE(3, double, dbl, ClaricppPrimEnumDouble)
                CASE(4, PyObj::VSPtr) { return { { .vs = got->ref }, ClaricppPrimEnumVS }; }
                CASE_END
                /* Literal BV types */
                TRIVIAL_CASE(5, uint8_t, u8, ClaricppPrimEnumU8)
                TRIVIAL_CASE(6, uint16_t, u16, ClaricppPrimEnumU16)
                TRIVIAL_CASE(7, uint32_t, u32, ClaricppPrimEnumU32)
                TRIVIAL_CASE(8, uint64_t, u64, ClaricppPrimEnumU64)
                /* Other */
                CASE(9, BigInt) {
                    got.to<BigInt::Str>();
                    const std::string &gstr { std::get<std::string>(got.value) };
                    char *const ret { Util::Safe::malloc<char>(gstr.size() + 1) };
                    std::strcpy(ret, gstr.c_str());
                    return { { .big_int = ret }, ClaricppPrimEnumBigInt };
                }
                CASE_END
            }
            // Failure
            success = false;
            if constexpr (MayFail) {
                return ClaricppPrim {}; // Garbage data
            }
            throw Util::Err::Unknown(WHOAMI "Variant shouldn't have this index");
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
            return ClaricppArg { { .prim = ret.data }, static_cast<ClaricppArgEnum>(ret.type) };
        }
        switch (in.index()) {
            CASE(10, Expr::BasePtr) {
                return ClaricppArg { { .expr = to_c(std::move(got)) }, ClaricppArgEnumExpr };
            }
            CASE_END
            CASE(11, Mode::FP::Rounding) {
                return ClaricppArg { { .rounding_mode = API::mode(got) }, ClaricppArgEnumRM };
            }
            CASE_END
            CASE(12, Mode::FP::Width) {
                const auto w { (got == Mode::FP::dbl) ? ClaricppWidthDouble : ClaricppWidthFloat };
                return ClaricppArg { { .width = w }, ClaricppArgEnumWidth };
            }
            CASE_END
        }
        throw Util::Err::Unknown(WHOAMI "Variant shouldn't have this index");
    }

// Cleanup
#undef TRIVIAL_CASE
#undef CASE_END
#undef CASE

    // Cleanup functions

    /** Heap cache free function */
    template <typename InC> inline void free(InC &x) {
        Private::cache<Private::Map<InC>>.free(&to_cpp(x));
        x.ptr = nullptr;
    }

    /** Array free function */
    template <typename InC> inline void free_array(InC &x) {
        using CType = std::remove_pointer_t<decltype(x.arr)>;
        static_assert(Util::TD::true_<Private::Map<CType>>, "Unknown array type");
        for (SIZE_T i { 0 }; i < x.len; ++i) {
            API::free(x.arr[i]);
        }
        std::free(x.arr);
        x.arr = nullptr;
        x.len = 0;
    }

} // namespace API

#endif