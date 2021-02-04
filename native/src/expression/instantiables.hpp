/**
 * @file
 * @brief This file defines trivial subclasses of Base and Bits
 */
#ifndef __EXPRESSION_INSTANTIABLES_HPP__
#define __EXPRESSION_INSTANTIABLES_HPP__

#include "bits.hpp"


/********************************************************************/
/*                           Local Macros                           */
/********************************************************************/


/** Local: A macro to declare trivial subclasses of BASE */
#define EXPRESSION_SUBCLASS(CLASS, BASE, CTOR)                                                    \
    /** This class is an Expression subclass */                                                   \
    class CLASS : public BASE {                                                                   \
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expression::Base)                                 \
      protected:                                                                                  \
        /** Protected Constructor */                                                              \
        CTOR /** Pure virtual destructor */                                                       \
            inline ~CLASS() noexcept override final = default;                                    \
        /* Disable other methods of construction */                                               \
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete)                                                \
    };


/** Local: A macro to define a passthrough constructor for a subclass of Base */
#define BASE_SUBCLASS_CTOR(CLASS)                                                                 \
    explicit inline CLASS(EXPRESSION_BASE_ARGS(h, c, sym, op_, annotations_)) noexcept            \
        : Base { h, c, sym, op_, annotations_ } {}

/** Local: A macro to define a passthrough constructor for a subclass of Bits */
#define BITS_SUBCLASS_CTOR(CLASS)                                                                 \
    explicit inline CLASS(EXPRESSION_BASE_ARGS(h, c, sym, op_, annotations_),                     \
                          const Constants::UInt size_) noexcept                                   \
        : Bits { h, c, sym, op_, annotations_, size_ } {}


/** Local: A macro to declare trivial subclasses of BASE */
#define DEFINE_SUBCLASS(CLASS, BASE)                                                              \
    static_assert(std::is_same_v<BASE, ::Expression::Base> ||                                     \
                      std::is_same_v<BASE, ::Expression::Bits>,                                   \
                  "DEFINE_SUBCLASS macro invoked on unspported base");                            \
    EXPRESSION_SUBCLASS(CLASS, BASE, BASE_SUBCLASS_CTOR(CLASS))


/********************************************************************/
/*                        Class Definitions                         */
/********************************************************************/


namespace Expression {

    // Base subclasses
    DEFINE_SUBCLASS(Int, Base)
    DEFINE_SUBCLASS(Bool, Base)

    // Bits subclasses
    DEFINE_SUBCLASS(String, Bits)
    DEFINE_SUBCLASS(VS, Bits)
    DEFINE_SUBCLASS(BV, Bits)
    DEFINE_SUBCLASS(FP, Bits)

} // namespace Expression


// Cleanup
#undef EXPRESSION_SUBCLASS
#undef BASE_SUBCLASS_CTOR
#undef BITS_SUBCLASS_CTOR
#undef DEFINE_SUBCLASS


#endif
