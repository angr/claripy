/**
 * @file
 * @brief The OP representing a Literal
 */
#ifndef R_SRC_OP_LITERAL_HPP_
#define R_SRC_OP_LITERAL_HPP_

#include "base.hpp"
#include "constants.hpp"


namespace Op {

    /** The op class Literal */
    class Literal final : public Base {
        OP_FINAL_INIT(Literal, "", 0);

      public:
        /** Representation */
        const PrimVar value;

        /** Returns the bit_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expr that is a subclass
         *  of BitLength then an Usage exception is thrown
         */
        constexpr U64 bit_length() const {
            if (std::holds_alternative<BigInt>(value)) {
                return std::get<BigInt>(value).bit_length;
            }
            else {
                return CHAR_BIT * byte_length();
            }
        }

        /** repr */
        inline void repr_stream(std::ostream &out) const final {

/** A local macro used for consistency */
#define VCASE_PRE(INDEX, TYPE)                                                                     \
    case (INDEX): {                                                                                \
        UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(value, INDEX, TYPE)                            \
        const auto &got { std::get<TYPE>(value) };

/** A local macro used for consistency */
#define VCASE_POST                                                                                 \
    break;                                                                                         \
    }

/** A local macro used for consistency */
#define VCASE(INDEX, TYPE)                                                                         \
    VCASE_PRE(INDEX, TYPE);                                                                        \
    out << got;                                                                                    \
    VCASE_POST;

            // Repr depending on type
            out << R"|({ "name":")|" << op_name() << R"|(", "value":)|";
            switch (value.index()) {
                // Bool
                VCASE_PRE(0, bool);
                out << std::boolalpha << got;
                VCASE_POST;
                // String
                VCASE_PRE(1, std::string);
                out << std::quoted(got);
                VCASE_POST;
                // FP
                VCASE(2, float);
                VCASE(3, double);
                // VS
                VCASE(4, PyObj::VSPtr);
                // BV
                VCASE_PRE(5, uint8_t);
                out << uint16_t { got }; // To avoid printing as a char
                VCASE_POST;
                VCASE(6, uint16_t);
                VCASE(7, uint32_t);
                VCASE(8, U64);
                VCASE_PRE(9, BigInt);
                got.write_value(out);
                out << R"|(, "Bit length":)|" << got.bit_length;
                VCASE_POST;
                    // Bad variant
                default:
                    UTIL_THROW(Util::Err::Unknown, "unknown type in variant");
            }
            out << " }";

// Cleanup
#undef VCASE_PRE
#undef VCASE_POST
#undef VCASE
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &) const noexcept final {}

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final {
/** A local macro used for consistency */
#define CASE(INDEX)                                                                                \
    case (INDEX):                                                                                  \
        return { std::get<INDEX>(value) };                                                         \
        break
            static_assert(std::variant_size_v<decltype(value)> == 10);
            switch (value.index()) {
                CASE(0);
                CASE(1);
                CASE(2);
                CASE(3);
                CASE(4);
                CASE(5);
                CASE(6);
                CASE(7);
                CASE(8);
                CASE(9);
                default:
                    UTIL_THROW(Util::Err::Unknown, "Broken variant detected");
            }
// Cleanup
#undef CASE
        }

      private:
/** A local macro used to define a private constructor for Literal */
#define P_CTOR(TYPE)                                                                               \
    /** Private constructor                                                                        \
     *  Literal constructors should never be given shared pointers to nulllptr                     \
     */                                                                                            \
    explicit inline Literal(const Hash::Hash &h, TYPE &&data)                                      \
        : Base { h, static_cuid }, value { std::move(data) }

        // The different private constructors we allow
        // There should be one for each variant type
        P_CTOR(bool) {};
        P_CTOR(std::string) {};
        P_CTOR(float) {};
        P_CTOR(double) {};
        P_CTOR(PyObj::VSPtr) {
            UTIL_ASSERT_NOT_NULL_DEBUG(std::get<PyObj::VSPtr>(value));
        }
        // BV constructors
        P_CTOR(uint8_t) {};
        P_CTOR(uint16_t) {};
        P_CTOR(uint32_t) {};
        P_CTOR(U64) {};
        P_CTOR(BigInt) {};

// Cleanup
#undef P_CTOR

        /** Returns the byte_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expr that is a subclass
         *  of BitLength then an Usage exception is thrown
         *  This function requires that if value is a shared_ptr is be non-null
         *  This function may not be called on a BigInt
         */
        constexpr U64 byte_length() const {

/** A local macro used for consistency */
#define VCASE_PRE(INDEX, TYPE)                                                                     \
    case (INDEX): {                                                                                \
        UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(value, INDEX, TYPE)                            \
        const auto &got { std::get<TYPE>(value) };

/** A local macro used for consistency */
#define RET(X)                                                                                     \
    return (X);                                                                                    \
    }

/** A local macro used for consistency */
#define VCASE(INDEX, TYPE)                                                                         \
    VCASE_PRE(INDEX, TYPE);                                                                        \
    RET(sizeof(got));

            switch (value.index()) {
                // String
                VCASE_PRE(1, std::string);
                RET(got.size());
                // FP
                VCASE(2, float);
                VCASE(3, double);
                // VS
                VCASE_PRE(4, PyObj::VSPtr);
#ifdef DEBUG
                UTIL_ASSERT_NOT_NULL_DEBUG(std::get<PyObj::VSPtr>(value));
                const auto bl { std::get<PyObj::VSPtr>(value)->bit_length };
                UTIL_ASSERT(Util::Err::Size, bl % CHAR_BIT == 0, "VS of bit length ", bl,
                            " which is not divisible by ", CHAR_BIT, " aka CHAR_BIT");
#endif
                RET(got->bit_length / CHAR_BIT);
                // BV
                VCASE(5, uint8_t);
                VCASE(6, uint16_t);
                VCASE(7, uint32_t);
                VCASE(8, U64);
                // Bool
                default: {
                    UTIL_THROW(Util::Err::Usage,
                               "invoked when internal type does not correspond to an Expr which "
                               "subclasses BitLength. Current variant index is: ",
                               value.index());
                };
            }

// Cleanup
#undef VCASE_PRE
#undef RET
#undef VCASE
        }
    };

} // namespace Op

#endif
