/**
 * @file
 * @brief The expression representing a Literal
 */
#ifndef __EXPRESSION_RAW_OP_LITERAL_HPP__
#define __EXPRESSION_RAW_OP_LITERAL_HPP__

#include "base.hpp"

#include "../type.hpp"


namespace Expression::Raw::Op {

    /** The op class Literal */
    class Literal : virtual public Base, virtual public CUSized {
        EXPRESSION_RAW_ABSTRACT_INIT(Literal)
      public:
        /** Return the op */
        Constants::CCS op() const override final;

      protected:
		/** Constructor
		 *  @todo figure out how this will work
		 */
		Literal(Constants::CCSC data);

#if 0
		/** Value type */
		using ValueT = std::variant<
			int_fast64_t,
			boost::multiprecision::int128_t,
			boost::multiprecision::mpz_int
		>;

		/** Representation */
		const ValueT value;
#endif

        /** Delete default constructor */
        Literal() = delete;
    };

} // namespace Expression::Raw::Op

#endif
