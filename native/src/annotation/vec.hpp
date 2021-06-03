/**
 * @file
 * @brief This file defines the Annotation::Vec class
 */
#ifndef R_ANNOTATION_VEC_HPP_
#define R_ANNOTATION_VEC_HPP_

#include "base.hpp"

#include "../hash.hpp"


namespace Annotation {

    /* A class that represents a constant vector of annotations with a pre-computed hash */
    struct Vec final : public Hash::Hashed {
      public:
        /** Constructor
         *  in pointers may not be nullptr
         */
        explicit inline Vec(std::vector<BasePtr> &&in)
            : Hashed { Hash::hash(in) }, vec { std::move(in) } {
#ifdef DEBUG
            for (auto &i : vec) {
                UTILS_AFFIRM_NOT_NULL_DEBUG(i);
            }
#endif
        }
        /** Internal vector */
        const std::vector<BasePtr> vec;
    };

} // namespace Annotation

#endif
