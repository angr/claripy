/**
 * @file
 * @brief The OP representing a Symbol
 */
#ifndef __OP_SYMBOL_HPP__
#define __OP_SYMBOL_HPP__

#include "base.hpp"


namespace Op {

    /** The op class Symbol */
    class Symbol final : public Base {
        OP_FINAL_INIT(Symbol, 0)
      public:
        /** Symbol name */
        const std::string name;

        /** Python's repr function (outputs json) */
        inline void repr(std::ostringstream &out, const bool) const override final {
            out << R"|({ "name":")|" << op_name() << R"|(", "symbol":")|" << name << "\" }";
        }

        /** Add's the raw expression children of the expression to the given stack in reverse
         *  Warning: This does *not* give ownership, it transfers raw pointers
         */
        inline void add_reversed_children(Stack &) const noexcept override final {}

      private:
        /** A protected constructor to disallow public creation */
        explicit inline Symbol(const Hash::Hash &h, const std::string &n)
            : Base { h, static_cuid }, name { n } {}
    };

} // namespace Op

#endif
