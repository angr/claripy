/**
 * @file errors.hpp
 * @brief This file contains the possible exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERRORS_HPP__
#define __ERRORS_HPP__

#include <exception>


/** Base AST exception
 *  All AST exceptions must derive from this
 */
class ClaripyASTError : public std::exception {};

class ClaripyBalancerError : public ClaripyASTError {};
class ClaripyBalancerUnsatError : public ClaripyBalancerError {};
class ClaripyTypeError : public ClaripyASTError {};
class ClaripyValueError : public ClaripyASTError {};
class ClaripySizeError : public ClaripyASTError {};
class ClaripyOperationError : public ClaripyASTError {};
class ClaripyReplacementError : public ClaripyASTError {};
class ClaripyRecursionError : public ClaripyOperationError {};
class ClaripyZeroDivisionError : public ClaripyOperationError {};

#endif
