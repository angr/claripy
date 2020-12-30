/**
 * @file
 * @brief This file defines the If Op AST Interface
 */
#ifndef __INTERFACE_OP_IF_HPP__
#define __INTERFACE_OP_IF_HPP__

#include "op.hpp"


namespace Interface::Op {

    /** The abstract Op AST Interface
     *  All Op interfaces must subclass this class
     */
    class If : public Op {
      public:
        /** Constructor */
        If(const AST::Base &b);

        /** If condition */
        AST::Bool cond() const;

        /** The if true clause */
        AST::Base if_true() const;

        /** The if false clause */
        AST::Base if_false() const;

      private:
        /** Delete the default constructor */
        If() = delete;
    };

} // namespace Interface::Op

#endif
