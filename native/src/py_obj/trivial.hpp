/**
 * @file
 * @brief This file defines trivial PyObjs
 */
#ifndef R_SRC_PYOBJ_TRIVIAL_HPP_
#define R_SRC_PYOBJ_TRIVIAL_HPP_

#include "base.hpp"


#define M_NEW_PYOBJ(NAME)                                                                          \
    class NAME : public Sized {                                                                    \
      public:                                                                                      \
        CUID_DEFINE_MAYBE_UNUSED                                                                   \
        using Ptr = std::shared_ptr<const NAME>;                                                   \
                                                                                                   \
      protected:                                                                                   \
        /** Constructor */                                                                         \
        using Sized::Sized;                                                                        \
        /** Protected destructor to avoid slicing */                                               \
        virtual inline ~NAME() noexcept = default;                                                 \
        /* Rule of 5 */                                                                            \
        DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(NAME);                                         \
    };

namespace PyObj {
    /** A VS PyObj for VSs
     *  Warning: Exactly one class should ever subclass this
     *  We give this abstract object a CUID, it should be for the subclass
     *  We do this so that the API can subclass this to hook it with python stuff
     */
    M_NEW_PYOBJ(VSVS);
    /** A VS PyObj for BVs
     *  Warning: Exactly one class should ever subclass this
     *  We give this abstract object a CUID, it should be for the subclass
     *  We do this so that the API can subclass this to hook it with python stuff
     */
    M_NEW_PYOBJ(BVVS);
} // namespace PyObj

#undef M_NEW_PYOBJ

#endif