/**
 * @file
 * @brief This file defines the Annotation::Vec class
 */
#ifndef R_SRC_ANNOTATION_VEC_HPP_
#define R_SRC_ANNOTATION_VEC_HPP_

#include "base.hpp"

#include "../hash.hpp"


namespace Annotation {

    /* A class that represents a constant vector of annotations with a pre-computed hash */
    struct Vec final : public HasRepr, public Hash::Hashed {
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
        /** Fast repr append */
        virtual inline void repr_stream(std::ostream &o) const override {
            o << R"|({"size":)|" << vec.size() << R"|(, "values": [)|";
            static constexpr CCSC delim { ", " };
            for (U64 i { 0 }; i < vec.size(); ++i) {
                vec[i]->repr_stream(o);
                o << delim;
            }
            if (vec.size() != 0) {
                o.seekp(Util::strlen(delim), o.cur); // Pop off last ", ";
            }
            o << " ] }";
        }
    };

    /** A shared pointer to a const annotation vector */
    using SPAV = std::shared_ptr<const Annotation::Vec>;

} // namespace Annotation

#endif
