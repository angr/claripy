/**
 * @file
 * @brief This file defines the abstract Op AST Interface
 */
#ifndef __INTERFACE_OP_OP_HPP__
#define __INTERFACE_OP_OP_HPP__

#include "../../op/operations.hpp"
#include "../base.hpp"


namespace Interface::Op {

    /** The abstract Op AST Interface
     *  All Op interfaces must subclass this class
     */
    class Op : public Base {
      public:
        /** Constructor */
        Op(const AST::Base &b, const ::Op::Operation o);

        /** Declare this class as abstract */
        virtual ~Op() = 0;

      private:
        /** Delete the default constructor */
        Op() = delete;

        /** The operation this interface represents */
        ::Op::Operation op;
    };

} // namespace Interface::Op

#endif
