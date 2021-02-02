/**
 * @file
 * @brief The OP representing a Literal
 */
#ifndef __OP_LITERAL_HPP__
#define __OP_LITERAL_HPP__

#include "base.hpp"

#include "../csized.hpp"
#include "../utils.hpp"

#include <variant>

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/gmp.hpp>


namespace Op {

    /** The op class Literal */
    class Literal final : virtual public Base, virtual public CSized {
        OP_FINAL_INIT(Literal)
      public:
        /** Value type */
        using ValueT = std::variant<int_fast64_t, boost::multiprecision::int128_t,
                                    boost::multiprecision::mpz_int>;

        /** Representation */
        const ValueT value;

      private:
        /** Private constructor
         *  @todo figure out how this will work
         *  @todo Intern strings
         */
        explicit inline Literal(const Hash::Hash &h, const std::string &data,
                                const Constants::UInt size)
            : Base { h, static_cuid }, CSized { size }, value { create_value(data, size) } {}

        /** Used by the constructor to initalize value */
        static inline ValueT create_value(const std::string &rdata, Constants::UInt size) {
            using Usage = Utils::Error::Unexpected::IncorrectUsage;
            using MP = boost::multiprecision;
            // Constants
            static const constexpr Constants::UInt max64 = sizeof(int_fast64_t);
            static const constexpr Constants::UInt max128 = 128;
            // Construct differently depending on size
            if (size <= max64) {
                Utils::affirm<Usage>(rdata.size() == (max64 / CHAR_BIT),
                                     "Literal constructor with size ", size,
                                     " given a string with less than 8 bytes in it");
                Constants::CCSC data = rdata.data();
                return { Utils::type_pun<int_fast64_t>(data) }; // Used with caution
            }
            else if (size <= max128) {
                Constants::CCSC data = rdata.data();
                return { MP::int128_t(data) };
            }
            else {
                return { MP::mpz_int(rdata) };
            }
        }
    };

} // namespace Op

#endif
