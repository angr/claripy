/**
 * @file
 * \ingroup api
 */
#include "../annotation.hpp"

#include "cpp.hpp"


extern "C" {

    ClaricppAnnotation claricpp_annotation_new_base() {
        return API::to_c(Annotation::factory<Annotation::Base>());
    }

    ClaricppAnnotation claricpp_annotation_new_simplification_avoidance() {
        return API::to_c(Annotation::factory<Annotation::SimplificationAvoidance>());
    }

    ClaricppSPAV claricpp_annotation_create_spav(ARRAY_IN(ClaricppAnnotation) list,
                                                 const SIZE_T len) {
        UTIL_AFFIRM_NOT_NULL_DEBUG(list);
        Annotation::Vec::RawVec raw;
        raw.reserve(len);
        for (SIZE_T i = 0; i < len; ++i) {
            raw.emplace_back(API::to_cpp(list[i])); // NOLINT
            UTIL_AFFIRM_NOT_NULL_DEBUG(raw.back());
        }
        using CV = Util::InternalType<Annotation::SPAV>;
        return API::to_c(std::make_shared<CV>(std::move(raw)));
    }

    ARRAY_OUT(ClaricppAnnotation) claricpp_annotation_spav_array(const ClaricppSPAV spav) {
        if (spav.ptr == nullptr) {
            return { .arr = nullptr, .len = 0 };
        }
        return API::copy_to_arr(API::to_cpp_ref(spav).vec);
    }

    SIZE_T claricpp_annotation_spav_len(const ClaricppSPAV spav) {
        if (spav.ptr == nullptr) {
            return 0;
        }
        return API::to_cpp_ref(spav).vec.size();
    }

    ClaricppAnnotation claricpp_annotation_spav_get(const ClaricppSPAV spav, const SIZE_T i) {
#ifdef DEBUG
        Util::affirm<Util::Err::Index>(i < API::to_cpp_ref(spav).vec.size(),
                                       WHOAMI "Index out of bounds");
#endif
        return API::copy_to_c(API::to_cpp_ref(spav).vec[i]);
    }
}
