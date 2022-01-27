/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

extern "C" {

    ClaricppBIM claricpp_big_int_mode_get() {
        API_FUNC_START
        return API::mode(BigInt::mode());
        API_FUNC_END
    }

    ClaricppBIM claricpp_big_int_mode_set(const ClaricppBIM m) {
        API_FUNC_START
        return API::mode(BigInt::mode(API::mode(m)));
        API_FUNC_END
    }
}