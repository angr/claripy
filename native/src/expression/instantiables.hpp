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
#define EXPRESSION_SUBCLASS(CLASS, BASE, CTOR_MIDDLE)                                             \
    /** This class is an Expression subclass */                                                   \
    class CLASS final : public BASE {                                                             \
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::Expression::Base)                                 \
      public:                                                                                     \
        /** Default destructor */                                                                 \
        inline ~CLASS() noexcept override final = default;                                        \
                                                                                                  \
      private:                                                                                    \
        /** Private Constructor */                                                                \
        explicit inline CLASS(const Hash::Hash h, const bool sym, Factory::Ptr<Op::Base> && op_, \
			AnnotationVec && annotations_ CTOR_MIDDLE {} \
        /* Disable other methods of construction */                                               \
        SET_IMPLICITS_CONST_MEMBERS(CLASS, delete)                                                \
    };

/** Local: Forward op and annotations */
#define FORWARD_OP_ANS                                                                            \
    std::forward<Factory::Ptr<Op::Base>>(op_), std::forward<AnnotationVec>(annotations_)

/** Local: A macro to define a passthrough constructor for a subclass of Base */
#define BASE_SUBCLASS_CTOR(CLASS)                                                                 \
        ) noexcept \
	: Base { h, static_cuid, sym, FORWARD_OP_ANS }


/** Local: A macro to define a passthrough constructor for a subclass of Bits */
#define BITS_SUBCLASS_CTOR(CLASS)                                                                 \
        , const Constants::UInt size_) noexcept \
	: Bits { h, static_cuid, sym, FORWARD_OP_ANS, size_ }


/** Local: A macro to declare trivial subclasses of Base */
#define DEFINE_BASE_SUBCLASS(CLASS) EXPRESSION_SUBCLASS(CLASS, Base, BASE_SUBCLASS_CTOR(CLASS))

/** Local: A macro to declare trivial subclasses of Bits */
#define DEFINE_BITS_SUBCLASS(CLASS) EXPRESSION_SUBCLASS(CLASS, Bits, BITS_SUBCLASS_CTOR(CLASS))


/********************************************************************/
/*                        Class Definitions                         */
/********************************************************************/


namespace Expression {

    // Base subclasses
    DEFINE_BASE_SUBCLASS(Int)

    // Bits subclasses
    DEFINE_BITS_SUBCLASS(String)
    DEFINE_BITS_SUBCLASS(VS)
    DEFINE_BITS_SUBCLASS(BV)
    DEFINE_BITS_SUBCLASS(FP)

} // namespace Expression


// Cleanup
#undef EXPRESSION_SUBCLASS
#undef FORWARD_OP_ANS
#undef BASE_SUBCLASS_CTOR
#undef BITS_SUBCLASS_CTOR
#undef DEFINE_BASE_SUBCLASS
#undef DEFINE_BITS_SUBCLASS


#endif
