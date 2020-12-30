/**
 * @file
 * @brief This file defines the abstract base AST interface
 */
#ifndef __INTERFACE_BASE_HPP__
#define __INTERFACE_BASE_HPP__

#include "../ast/base.hpp"


namespace Interface {

    /** The abstract base AST Interface
     *  All AST Interfaces must subclass this
     */
    class Base {
      public:
        /** Constructor */
        Base(const AST::Base &b);

        /** Declare this class as abstract */
        virtual ~Base() = 0;

      protected:
        /** Use to get the number of children of ast */
        Constants::UInt size() const;

        /** Used to access the children of ast */
        AST::Base child(const Constants::UInt index) const;

      private:
        /** Delete the default constructor */
        Base() = delete;

        /** The AST being interfaced */
        AST::Base ast;
    };

} // namespace Interface

#endif
