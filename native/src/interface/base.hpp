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
		Base(const AST::Base & b);

		/** Declare this class as abstract */
		virtual ~Base()=0;

private:
		/** Delete the default constructor */
		Base() = delete;

		/** The AST being interfaced */
		AST::Base ast;
	};

}

#endif
