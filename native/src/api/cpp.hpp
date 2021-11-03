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

/** A local macro used to add an array Map entry
 *  Requires C type be in InternalMap
 */
#define ARR_MAP_ADD(CTYPE)                                                                         \
    static_assert(Util::TD::true_<InternalMap<CTYPE>::Result>, "CTYPE not in InternalMap");        \
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
    template <typename InC> static inline auto &to_cpp(const InC &x) noexcept {
        UTILS_AFFIRM_NOT_NULL_DEBUG(x.ptr);
        return *static_cast<Private::Map<InC> *const>(x.ptr);
    }

    /** Returns a reference to the dereference of the C++ type held by the C type x
     *  Warning: Returns a reference to part of x
     */
    template <typename InC> static inline auto &to_cpp_ref(const InC &x) noexcept {
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
    static inline Op::FlatArgs to_op_args(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len) {
        Op::FlatArgs ops;
        ops.reserve(len);
        for (UInt i = 0; i < len; ++i) {
            ops.emplace_back(to_cpp(operands[i]));
        }
        return ops;
    }

    // To C

    /** Heap cache function */
    template <typename InCpp> static inline auto to_c(InCpp &&x) {
        return Private::Map<InCpp> { Private::cache<InCpp>.move_to_heap(std::move(x)) };
    }

    /** Heap cache function; prefer to_c! Use this when x cannot be moved for some reason. */
    template <typename InCpp> static inline auto copy_to_c(const InCpp &x) {
        InCpp tmp { x };
        return Private::Map<InCpp> { Private::cache<InCpp>.template emplace_on_heap(std::move(x)) };
    }

    /** Heap cache function with emplacement */
    template <typename InCpp, typename... Args> static inline auto emplace_to_c(Args &&...args) {
        return Private::Map<InCpp> { Private::cache<InCpp>.emplace_on_heap(
            std::forward<Args>(args)...) };
    }

    /** Convert a C++ vector to a C array */
    template <typename InCpp> static inline auto to_arr(std::vector<InCpp> &&arr) {
        using CType = Private::Map<InCpp>;
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

    // Cleanup

    /** Heap cache free function */
    template <typename InC> static inline void free(InC &x) {
        Private::cache<Private::Map<InC>>.free(&to_cpp(x));
        x.ptr = nullptr;
    }

    /** Array free function */
    template <typename InC> static inline void free_array(InC &x) {
        using CType = std::remove_pointer_t<decltype(x.arr)>;
        static_assert(Util::TD::true_<Private::Map<CType>>, "Unknown array type");
        for (SIZE_T i { 0 }; i < x.len; ++i) {
            API::free(x.arr[i]);
        }
        std::free(x.arr);
        x.arr = nullptr;
        x.len = 0;
    }

    // Rounding mode

    /** Converts between a C++ strong enums and C weak enums
     *  Currently supported conversions:
     *  1. Mode::FP::Rounding <-> ClaricppRM
     */
    template <typename In> static inline auto mode(const In in) noexcept {
        return typename Private::InternalEnumMap<In>::Result(in); // Must be (), not {}
    }

} // namespace API

#endif