/**
 * @file
 * \ingroup api
 */
#include "../annotation.hpp"

#include "cpp.hpp"


extern "C" {

    ClaricppAnnotation claricpp_annotation_new_base() {
        API_FUNC_START
        return API::to_c(Annotation::factory<Annotation::Base>());
        API_FUNC_END
    }

    ClaricppAnnotation claricpp_annotation_new_simplification_avoidance() {
        API_FUNC_START
        return API::to_c(Annotation::factory<Annotation::SimplificationAvoidance>());
        API_FUNC_END
    }

    ClaricppSPAV claricpp_annotation_create_empty_spav() { return { nullptr }; }

    ClaricppSPAV claricpp_annotation_create_spav(ARRAY_IN(ClaricppAnnotation) list,
                                                 const SIZE_T len) {
        if (UNLIKELY(len == 0)) {
            return claricpp_annotation_create_empty_spav();
        }
        API_FUNC_START
        UTIL_ASSERT_NOT_NULL_DEBUG(list);
        Annotation::Vec::RawVec raw;
        raw.reserve(len);
        for (SIZE_T i = 0; i < len; ++i) {
            raw.emplace_back(API::to_cpp(list[i])); // NOLINT
            UTIL_ASSERT_NOT_NULL_DEBUG(raw.back());
        }
        using CV = Util::Type::Internal<Annotation::SPAV>;
        return API::to_c(std::make_shared<CV>(std::move(raw)));
        API_FUNC_END
    }

    ARRAY_OUT(ClaricppAnnotation) claricpp_annotation_spav_to_array(const ClaricppSPAV spav) {
        if (spav.ptr == nullptr) {
            return { .arr = nullptr, .len = 0 };
        }
        API_FUNC_START
        return API::copy_to_arr(API::to_cpp_ref(spav).vec);
        API_FUNC_END
    }

    SIZE_T claricpp_annotation_spav_len(const ClaricppSPAV spav) {
        if (spav.ptr == nullptr) {
            return 0;
        }
        API_FUNC_START
        return API::to_cpp_ref(spav).vec.size();
        API_FUNC_END
    }

    ClaricppAnnotation claricpp_annotation_spav_get(const ClaricppSPAV spav, const SIZE_T i) {
        API_FUNC_START
#ifdef DEBUG
        UTIL_ASSERT(Util::Err::Index, i < API::to_cpp_ref(spav).vec.size(), "Index out of bounds");
#endif
        return API::copy_to_c(API::to_cpp_ref(spav).vec[i]);
        API_FUNC_END
    }
}
