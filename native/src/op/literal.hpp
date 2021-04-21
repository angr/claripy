/**
 * @file
 * @brief The OP representing a Literal
 */
#ifndef __OP_LITERAL_HPP__
#define __OP_LITERAL_HPP__

#include "base.hpp"

#include "../bit_length.hpp"
#include "../utils.hpp"

#include <cstddef>
#include <variant>

/** @todo */
#ifdef ENABLE_MPZ
    #include <boost/multiprecision/cpp_int.hpp>
    #include <boost/multiprecision/gmp.hpp>
#endif


namespace Op {

    /** The op class Literal */
    class Literal final : public Base, public BitLength {
        OP_FINAL_INIT(Literal, 0);

      public:
#ifdef ENABLE_MPZ
        /** Value type */
        using ValueT = std::variant<int_fast64_t, boost::multiprecision::int128_t,
                                    boost::multiprecision::mpz_int>;

        /** Representation */
        const ValueT value;
#else
        /** Representation */
        const std::string value;
#endif

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &) const noexcept override final {}

      private:
        /** Private constructor
         *  @todo figure out how this will work
         *  @todo Intern strings
         */
        explicit inline Literal(const Hash::Hash &h, std::string &&data)
#ifndef ENABLE_MPZ
            : Base { h, static_cuid },
              BitLength { BitLength::char_bit * data.size() },
              value { data } {
        }
#else
            : Base { h, static_cuid },
              BitLength { BitLength::char_bit * data.size() },
              value { create_value(data) } {
        }

        /** Used by the constructor to initalize value */
        static inline ValueT create_value(std::string &&data) {
            using Usage = Utils::Error::Unexpected::IncorrectUsage;
            namespace MP = boost::multiprecision;
            // Constants
            static const constexpr Constants::UInt max64 =
                sizeof(int_fast64_t);                               // >= 64 / CHAR_BIT
            static const constexpr Constants::UInt max128 = 128ULL; // exactly 128 / CHAR_BIT
            // Construct differently depending on size
            if (bit_length <= max64) {
                Utils::affirm<Usage>(data == max64,
                                     WHOAMI_WITH_SOURCE "Literal constructor with bit length ",
                                     bit_length, " given a string with only ", rdata.size(),
                                     " bytes in it."
                                     " The minimum amount allowed is: ",
                                     max64);
                Constants::CCSC data = rdata.data();
                return { Utils::type_pun<int_fast64_t, char, true>(data) }; // Used with caution
            }
            else if (bit_length <= max128) {
                Constants::CCSC data = rdata.data();
                return { MP::int128_t(data) };
            }
            else {
                return { MP::mpz_int(rdata) };
            }
        }
#endif
    };

} // namespace Op

#endif
