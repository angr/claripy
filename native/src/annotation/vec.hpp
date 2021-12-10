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
        /** The raw vector type Vec holds */
        using RawVec = std::vector<BasePtr>;
        /** Constructor
         *  in pointers may not be nullptr
         */
        explicit inline Vec(RawVec &&in) : Hashed { Hash::hash(in) }, vec { std::move(in) } {
#ifdef DEBUG
            for (auto &i : vec) {
                UTIL_ASSERT_NOT_NULL_DEBUG(i);
            }
#endif
        }
        /** Internal vector */
        const RawVec vec;
        /** repr */
        inline void repr(std::ostream &o) const {
            o << R"|({"size":)|" << vec.size() << R"|(, "values": [)|";
            for (UInt i { 0 }; i < vec.size(); ++i) {
                o << (i == 0 ? " \"" : ", \"") << vec[i]->name() << '"';
            }
            o << " ] }";
        }
    };

    /** A shared pointer to a const annotation vector */
    using SPAV = std::shared_ptr<const Annotation::Vec>;

} // namespace Annotation

#endif
