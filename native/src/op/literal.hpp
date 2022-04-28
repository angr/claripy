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
            out << R"|({ "name":")|" << op_name() << R"|(", "value":)|";
            switch (value.index()) {

#define M_VCASE_PRE(INDEX, TYPE)                                                                   \
    case (INDEX): {                                                                                \
        UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(value, INDEX, TYPE)                            \
        const auto &got { std::get<TYPE>(value) };

#define M_VCASE_POST                                                                               \
    break;                                                                                         \
    }

#define M_VCASE(INDEX, TYPE)                                                                       \
    M_VCASE_PRE(INDEX, TYPE);                                                                      \
    out << got;                                                                                    \
    M_VCASE_POST;

                // Bool
                M_VCASE_PRE(0, bool);
                out << std::boolalpha << got;
                M_VCASE_POST;
                // String
                M_VCASE_PRE(1, std::string);
                out << std::quoted(got);
                M_VCASE_POST;
                // FP
                M_VCASE(2, float);
                M_VCASE(3, double);
                // VS
                M_VCASE(4, PyObj::VSPtr);
                // BV
                M_VCASE_PRE(5, uint8_t);
                out << uint16_t { got }; // To avoid printing as a char
                M_VCASE_POST;
                M_VCASE(6, uint16_t);
                M_VCASE(7, uint32_t);
                M_VCASE(8, U64);
                M_VCASE_PRE(9, BigInt);
                got.write_value(out);
                out << R"|(, "Bit length":)|" << got.bit_length;
                M_VCASE_POST;
#undef M_VCASE_PRE
#undef M_VCASE_POST
#undef M_VCASE
                // Bad variant
                default:
                    UTIL_THROW(Util::Err::Unknown, "unknown type in variant");
            }
            out << " }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &) const noexcept final {}

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final {
            static_assert(std::variant_size_v<decltype(value)> == 10);
            switch (value.index()) {
#define M_CASE(INDEX)                                                                              \
    case (INDEX):                                                                                  \
        return { std::get<INDEX>(value) }
                M_CASE(0);
                M_CASE(1);
                M_CASE(2);
                M_CASE(3);
                M_CASE(4);
                M_CASE(5);
                M_CASE(6);
                M_CASE(7);
                M_CASE(8);
                M_CASE(9);
#undef M_CASE
                default:
                    UTIL_THROW(Util::Err::Unknown, "Broken variant detected");
            }
        }

        /** Return true iff the op is a leaf op */
        inline bool is_leaf() const noexcept final {
            return true;
        }

      private:
#define M_P_CTOR(TYPE)                                                                             \
    /** Private constructor                                                                        \
     *  Literal constructors should never be given shared pointers to nulllptr                     \
     */                                                                                            \
    explicit inline Literal(const Hash::Hash &h, TYPE &&data)                                      \
        : Base { h, static_cuid }, value { std::move(data) }

        // The different private constructors we allow
        // There should be one for each variant type
        M_P_CTOR(bool) {};
        M_P_CTOR(std::string) {};
        M_P_CTOR(float) {};
        M_P_CTOR(double) {};
        M_P_CTOR(PyObj::VSPtr) {
            UTIL_ASSERT_NOT_NULL_DEBUG(std::get<PyObj::VSPtr>(value));
        }
        // BV constructors
        M_P_CTOR(uint8_t) {};
        M_P_CTOR(uint16_t) {};
        M_P_CTOR(uint32_t) {};
        M_P_CTOR(U64) {};
        M_P_CTOR(BigInt) {};
#undef M_P_CTOR

        /** Returns the byte_length of the value stored in Data
         *  If Data contains a type that doesn't correspond to an Expr that is a subclass
         *  of BitLength then an Usage exception is thrown
         *  This function requires that if value is a shared_ptr is be non-null
         *  This function may not be called on a BigInt
         */
        constexpr U64 byte_length() const {
            switch (value.index()) {

#define M_VCASE_PRE(INDEX, TYPE)                                                                   \
    case (INDEX): {                                                                                \
        UTIL_VARIANT_VERIFY_INDEX_TYPE_IGNORE_CONST(value, INDEX, TYPE)                            \
        const auto &got { std::get<TYPE>(value) };

#define M_RET(X)                                                                                   \
    return (X);                                                                                    \
    }

#define M_VCASE(INDEX, TYPE)                                                                       \
    M_VCASE_PRE(INDEX, TYPE);                                                                      \
    M_RET(sizeof(got));

                // String
                M_VCASE_PRE(1, std::string);
                M_RET(got.size());
                // FP
                M_VCASE(2, float);
                M_VCASE(3, double);
                // VS
                M_VCASE_PRE(4, PyObj::VSPtr);
#ifdef DEBUG
                UTIL_ASSERT_NOT_NULL_DEBUG(std::get<PyObj::VSPtr>(value));
                const auto bl { std::get<PyObj::VSPtr>(value)->bit_length };
                UTIL_ASSERT(Util::Err::Size, bl % CHAR_BIT == 0, "VS of bit length ", bl,
                            " which is not divisible by ", CHAR_BIT, " aka CHAR_BIT");
#endif
                M_RET(got->bit_length / CHAR_BIT);
                // BV
                M_VCASE(5, uint8_t);
                M_VCASE(6, uint16_t);
                M_VCASE(7, uint32_t);
                M_VCASE(8, U64);
#undef M_VCASE_PRE
#undef M_RET
#undef M_VCASE
                // Bool
                default: {
                    UTIL_THROW(Util::Err::Usage,
                               "invoked when internal type does not correspond to an Expr which "
                               "subclasses BitLength. Current variant index is: ",
                               value.index());
                };
            }
        }
    };

} // namespace Op

#endif
