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
        OP_FINAL_INIT(Symbol)
      public:
        /** Symbol name */
        const std::string name;

      private:
        /** A protected constructor to disallow public creation */
        explicit inline Symbol(const Hash::Hash &h, const std::string &n)
            : Base { h, class_uid }, name { n } {}
    };

} // namespace Op

#endif
