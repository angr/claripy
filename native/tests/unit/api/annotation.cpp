/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the Annotation API works */
void annotation() {
    namespace A = Annotation;
    using SA = A::SimplificationAvoidance;

    const ClaricppAnnotation arr[] = { // NOLINT
                                       claricpp_annotation_new_base(),
                                       claricpp_annotation_new_simplification_avoidance()
    };
    const ClaricppSPAV spav { claricpp_annotation_create_spav(arr, 2) };

    // Constants
    const A::BasePtr base { API::to_cpp(arr[0]) };
    const A::BasePtr sa { API::to_cpp(arr[1]) };
    CTSC<SA> sa_raw { dynamic_cast<CTSC<SA>>(sa.get()) };
    const A::SPAV vec { API::to_cpp(spav) };
    const auto &raw_vec { vec.get()->vec };

    // Technically 0 can be a hash but more likely it's due to a failure so:
    UNITTEST_ASSERT(base != nullptr && base->hash != 0);

    UNITTEST_ASSERT(sa != nullptr && sa->hash != 0);
    UNITTEST_ASSERT(sa_raw != nullptr && sa->hash == sa_raw->hash);

    UNITTEST_ASSERT(raw_vec.size() == 2)
    UNITTEST_ASSERT(raw_vec[0] == base);
    UNITTEST_ASSERT(raw_vec[1] == sa);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(annotation)
