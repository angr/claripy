/**
 * @file
 * @brief The OP representing a Symbol
 */
#ifndef R_SRC_OP_SYMBOL_HPP_
#define R_SRC_OP_SYMBOL_HPP_

#include "base.hpp"


namespace Op {

    /** The op class Symbol */
    class Symbol final : public Base {
        OP_FINAL_INIT(Symbol, "", 0)
      public:
        /** Symbol name */
        const std::string name;

        /** repr */
        inline void repr_stream(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "symbol":")|" << name << "\" }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &) const noexcept final {}

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline std::vector<ArgVar> python_children() const final { return { name }; }

      private:
        /** A protected constructor to disallow public creation */
        explicit inline Symbol(const Hash::Hash &h, const std::string &n)
            : Base { h, static_cuid }, name { n } {}
    };

} // namespace Op

#endif
