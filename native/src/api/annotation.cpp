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
        Annotation::Vec::RawVec raw;
        raw.reserve(len);
        for (SIZE_T i = 0; i < len; ++i) {
            raw.emplace_back(API::to_cpp(list[i])); // NOLINT
        }
        using CV = Util::InternalType<Annotation::SPAV>;
        return API::to_c(std::make_shared<CV>(std::move(raw)));
    }
}
