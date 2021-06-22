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
        using Data = std::variant<bool,                   // Bool
                                  std::string,            // String
                                  std::vector<std::byte>, // BV
                                  float, double,          // FP
                                  PyObj::VSPtr            // VS
                                  >;

        /** Representation */
        const Data value;

        /** Returns the bit_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expression that is a subclass
         *  of BitLength then an Usage exception is thrown
         */
        constexpr Constants::UInt bit_length() const { return C_CHAR_BIT * byte_length(); }

        /** Python's repr function (outputs json)
         *  @todo This could be a switch-case statement; do when more stable
         */
        inline void repr(std::ostream &out, const bool) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "value":)|";
            if (std::holds_alternative<std::string>(value)) {
                out << '"' << std::get<std::string>(value) << '"';
            }
            else if (std::holds_alternative<std::vector<std::byte>>(value)) {
                out << "[BV-" << std::get<std::vector<std::byte>>(value).size() << "]";
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
    /** Private constructor                                                                       \
     *  Literal constructors should never be given shared pointers to nulllptr                    \
     */                                                                                           \
    explicit inline Literal(const Hash::Hash &h, TYPE &&data)                                     \
        : Base { h, static_cuid }, value { std::move(data) }

        // The different private constructors we allow
        // There should be one for each variant type
        P_CTOR(bool) {};
        P_CTOR(std::string) {};
        P_CTOR(std::vector<std::byte>) {};
        P_CTOR(float) {};
        P_CTOR(double) {};
        P_CTOR(PyObj::VSPtr) { UTILS_AFFIRM_NOT_NULL_DEBUG(std::get<PyObj::VSPtr>(value)); }

// Cleanup
#undef P_CTOR

        /** Returns the byte_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expression that is a subclass
         *  of BitLength then an Usage exception is thrown
         *  This function requires that if value is a shared_ptr is be non-null
         *  @todo This could be a switch-case statement; do when more stable
         */
        constexpr Constants::UInt byte_length() const {
            if (std::holds_alternative<std::string>(value)) { // String
                return std::get<std::string>(value).size();
            }
            else if (std::holds_alternative<std::vector<std::byte>>(value)) { // BV
                return std::get<std::vector<std::byte>>(value).size();
            }
            else if (std::holds_alternative<float>(value)) { // FP
                return sizeof(float);
            }
            else if (std::holds_alternative<double>(value)) { // FP
                return sizeof(double);
            }
            else if (std::holds_alternative<PyObj::VSPtr>(value)) { // VS
#ifdef DEBUG
                UTILS_AFFIRM_NOT_NULL_DEBUG(std::get<PyObj::VSPtr>(value));
                const auto bl { std::get<PyObj::VSPtr>(value)->bit_length };
                Utils::affirm<Utils::Error::Unexpected::Size>(
                    bl % C_CHAR_BIT == 0, WHOAMI_WITH_SOURCE "VS of bit length ", bl,
                    " which is not divisible by ", C_CHAR_BIT, " aka C_CHAR_BIT");
#endif
                return std::get<PyObj::VSPtr>(value)->bit_length / C_CHAR_BIT;
            }
            // Invalid types: bool
            throw Utils::Error::Unexpected::Usage(WHOAMI_WITH_SOURCE,
                                                  "invoked when internal type does not correspond"
                                                  " to an Expression which subclasses BitLength."
                                                  " Current variant index is: ",
                                                  value.index());
        }
    };

} // namespace Op

#endif
