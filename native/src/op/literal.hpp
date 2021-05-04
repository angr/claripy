/**
 * @file
 * @brief The OP representing a Literal
 */
#ifndef __OP_LITERAL_HPP__
#define __OP_LITERAL_HPP__

#include "base.hpp"

#include "../utils.hpp"

#include <cstddef>
#include <variant>


namespace Op {

    /** The op class Literal */
    class Literal final : public Base {
        OP_FINAL_INIT(Literal, 0);

      public:
        /** The value type */
        using Data = std::variant<bool,              // Bool
                                  std::string,       // String
                                  std::vector<char>, // BV
                                  float, double      // FP
#warning Literal doesn't have support for VS
                                  >;

        /** Representation */
        const Data value;

        /** Returns the bit_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expression that is a subclass
         *  of BitLength then an IncorrectUsage exception is thrown
         */
        Constants::UInt bit_length() const {
            if (std::holds_alternative<std::string>(value)) {
                return std::get<std::string>(value).size();
            }
            else if (std::holds_alternative<std::vector<char>>(value)) {
                return std::get<std::vector<char>>(value).size();
            }
            else if (std::holds_alternative<float>(value)) {
                return sizeof(float);
            }
            else if (std::holds_alternative<std::vector<char>>(value)) {
                return sizeof(double);
            }
            // Invalid types: bool
            throw Utils::Error::Unexpected::IncorrectUsage(
                WHOAMI_WITH_SOURCE, "invoked when internal type does not correspond"
                                    " to an Expression which subclasses BitLength");
        }

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &) const noexcept override final {}

      private:
/** A local macro used to define a private constructor for Literal */
#define P_CTOR(TYPE)                                                                              \
    /** Private constructor */                                                                    \
    explicit inline Literal(const Hash::Hash &h, TYPE &&data)                                     \
        : Base { h, static_cuid }, value { std::move(data) } {}

        // The different private constructors we allow
        // There should be one for each variant type
        P_CTOR(bool);
        P_CTOR(std::string);
        P_CTOR(std::vector<char>);
        P_CTOR(float);
        P_CTOR(double);
    };

} // namespace Op

#endif
