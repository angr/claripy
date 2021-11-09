/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"


/** A local macro used for consistency */
#define DEFINE_FREE_FUNC(TYPE, NAME)                                                               \
    void claricpp_free_##NAME(TYPE *const c_object) {                                              \
        UTIL_AFFIRM_NOT_NULL_DEBUG(c_object);                                                      \
        API::free(*c_object);                                                                      \
    }

/** A local macro used for consistency */
#define DEFINE_ARR_FREE_FUNC(TYPE, NAME)                                                           \
    void claricpp_free_array_##NAME(ARRAY_OUT(TYPE) *const c_array) {                              \
        UTIL_AFFIRM_NOT_NULL_DEBUG(c_array);                                                       \
        API::free_array(*c_array);                                                                 \
    }

extern "C" {
    DEFINE_FREE_FUNC(ClaricppAnnotation, annotation);
    DEFINE_FREE_FUNC(ClaricppSPAV, spav);
    DEFINE_FREE_FUNC(ClaricppExpr, expr);
    DEFINE_FREE_FUNC(ClaricppBackend, backend);
    DEFINE_FREE_FUNC(ClaricppSolver, solver);

    DEFINE_ARR_FREE_FUNC(ClaricppExpr, expr);
}

// Cleanup
#undef DEFINE_FREE_FUNC
#undef DEFINE_ARR_FREE_FUNC
