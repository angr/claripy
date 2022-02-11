/**
 * @file
 * @brief The OP representing a Symbol
 */
#ifndef R_OP_SYMBOL_HPP_
#define R_OP_SYMBOL_HPP_

#include "base.hpp"


namespace Op {

    /** The op class Symbol */
    class Symbol final : public Base {
        OP_FINAL_INIT(Symbol, "", 0)
      public:
        /** Symbol name */
        const std::string name;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostream &out) const final {
            out << R"|({ "name":")|" << op_name() << R"|(", "symbol":")|" << name << "\" }";
        }

        /** Adds the raw expr children of the expr to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void unsafe_add_reversed_children(Stack &) const noexcept final {}

        /** Appends the expr children of the expr to the given vector
         *  Note: This should only be used when returning children to python
         */
        inline void python_children(std::vector<ArgVar> &v) const final { v.emplace_back(name); }

      private:
        /** A protected constructor to disallow public creation */
        explicit inline Symbol(const Hash::Hash &h, const std::string &n)
            : Base { h, static_cuid }, name { n } {}
    };

} // namespace Op

#endif
