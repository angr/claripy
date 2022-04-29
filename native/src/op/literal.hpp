/**
 * @file
 * @brief The OP representing a Literal
 */
#ifndef R_SRC_OP_LITERAL_HPP_
#define R_SRC_OP_LITERAL_HPP_

#include "base.hpp"
#include "constants.hpp"


namespace Op {

    // Forward declare
    inline std::ostream &operator<<(std::ostream &, const PrimVar &);

    /** The op class Literal */
    class Literal final : public Base {
        OP_FINAL_INIT(Literal, "", 0);

#define M_CASE(TYPE, EXPR)                                                                         \
    case (Util::Type::index<decltype(value), TYPE>): {                                             \
        const auto &got { std::get<TYPE>(value) };                                                 \
        return EXPR;                                                                               \
    }

      public:
        /** Representation */
        const PrimVar value;

        /** Returns the bit_length of the value stored in Data
         *  Raise an exception if called on a size without a bitlength (like a bool)
         */
        constexpr U64 bit_length() const {
            switch (value.index()) {
                // String
                M_CASE(std::string, CHAR_BIT * got.size());
                // FP
                M_CASE(float, CHAR_BIT * sizeof(got));
                M_CASE(double, CHAR_BIT * sizeof(got));
                // VS
                M_CASE(PyObj::VSPtr, got->bit_length);
                // BV
                M_CASE(uint8_t, CHAR_BIT * sizeof(got));
                M_CASE(uint16_t, CHAR_BIT * sizeof(got));
                M_CASE(uint32_t, CHAR_BIT * sizeof(got));
                M_CASE(U64, CHAR_BIT * sizeof(got));
                M_CASE(BigInt, got.bit_length);
                // Bool
                default: {
                    UTIL_THROW(Util::Err::Usage,
                               "invoked when internal type does not correspond to an Expr which "
                               "subclasses BitLength. Current variant index is: ",
                               value.index());
                };
            }
        }

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "value":)|" << value << " }";
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
                M_CASE(bool, { got });
                M_CASE(std::string, { got });
                M_CASE(float, { got });
                M_CASE(double, { got });
                M_CASE(PyObj::VSPtr, { got });
                M_CASE(uint8_t, { got });
                M_CASE(uint16_t, { got });
                M_CASE(uint32_t, { got });
                M_CASE(U64, { got });
                M_CASE(BigInt, { got });
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
    /** Private constructor;  constructor should not be given shared pointers to nulllptr */       \
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
    };

    /** Ostream operator for PrimVar */
    inline std::ostream &operator<<(std::ostream &o, const PrimVar &value) {
        switch (value.index()) {
            M_CASE(bool, o << std::boolalpha << got);
            M_CASE(std::string, o << std::quoted(got));
            M_CASE(float, o << got);
            M_CASE(double, o << got);
            M_CASE(PyObj::VSPtr, o << got);
            M_CASE(uint8_t, o << static_cast<uint16_t>(got));
            M_CASE(uint16_t, o << got);
            M_CASE(uint32_t, o << got);
            M_CASE(U64, o << got);
            M_CASE(BigInt, o << got);
            // Bad variant
            default:
                UTIL_THROW(Util::Err::Unknown, "unknown type in variant");
        }
    }
#undef M_CASE

} // namespace Op

#endif
