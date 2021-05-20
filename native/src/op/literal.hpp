/**
 * @file
 * @brief The OP representing a Literal
 */
#ifndef R_OP_LITERAL_HPP_
#define R_OP_LITERAL_HPP_

#include "base.hpp"

#include "../py_obj.hpp"

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
                                  float, double,     // FP
                                  PyObj::VSPtr       // VS
                                  >;

        /** Representation */
        const Data value;

        /** Returns the bit_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expression that is a subclass
         *  of BitLength then an IncorrectUsage exception is thrown
         */
        constexpr Constants::UInt bit_length() const { return C_CHAR_BIT * byte_length(); }

        /** Python's repr function (outputs json)
         *  @todo This could be a switch-case statement; do when more stable
         */
        inline void repr(std::ostringstream &out, const bool) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "value":)|";
            if (std::holds_alternative<std::string>(value)) {
                out << '"' << std::get<std::string>(value) << '"';
            }
            else if (std::holds_alternative<std::vector<char>>(value)) {
                out << "[BV-" << std::get<std::vector<char>>(value).size() << "]";
            }
            else if (std::holds_alternative<float>(value)) {
                out << std::get<float>(value);
            }
            else if (std::holds_alternative<double>(value)) {
                out << std::get<double>(value);
            }
            else if (std::holds_alternative<bool>(value)) {
                out << std::boolalpha << std::get<bool>(value);
            }
            else {
                throw Utils::Error::Unexpected::NotSupported(WHOAMI_WITH_SOURCE,
                                                             "given bad CUIDl unknown type");
            }
            out << " }";
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
        P_CTOR(PyObj::VSPtr);

// Cleanup
#undef P_CTOR

        /** Returns the byte_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expression that is a subclass
         *  of BitLength then an IncorrectUsage exception is thrown
         *  @todo This could be a switch-case statement; do when more stable
         */
        constexpr Constants::UInt byte_length() const {
            if (std::holds_alternative<std::string>(value)) { // String
                return std::get<std::string>(value).size();
            }
            else if (std::holds_alternative<std::vector<char>>(value)) { // BV
                return std::get<std::vector<char>>(value).size();
            }
            else if (std::holds_alternative<float>(value)) { // FP
                return sizeof(float);
            }
            else if (std::holds_alternative<double>(value)) { // FP
                return sizeof(double);
            }
            else if (std::holds_alternative<PyObj::VSPtr>(value)) { // VS
#ifdef DEBUG
                const auto bl { std::get<PyObj::VSPtr>(value)->bit_length };
                Utils::affirm<Utils::Error::Unexpected::Size>(
                    bl % C_CHAR_BIT == 0, WHOAMI_WITH_SOURCE "VS of bit length ", bl,
                    " which is not divisible by ", C_CHAR_BIT, " aka C_CHAR_BIT");
#endif
                return std::get<PyObj::VSPtr>(value)->bit_length / C_CHAR_BIT;
            }
            // Invalid types: bool
            throw Utils::Error::Unexpected::IncorrectUsage(
                WHOAMI_WITH_SOURCE,
                "invoked when internal type does not correspond"
                " to an Expression which subclasses BitLength."
                " Current variant index is: ",
                value.index());
        }
    };

} // namespace Op

#endif
