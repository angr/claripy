#ifndef __ERRORS_HPP__
#define __ERRORS_HPP__

#include <exception>


// Base AST exception
class ClaripyASTError: public std::exception {};

class ClaripyBalancerError: public ClaripyASTError {};
class ClaripyBalancerUnsatError: public ClaripyBalancerError {};
class ClaripyTypeError: public ClaripyASTError {};
class ClaripyValueError: public ClaripyASTError {};
class ClaripySizeError: public ClaripyASTError {};
class ClaripyOperationError: public ClaripyASTError {};
class ClaripyReplacementError: public ClaripyASTError {};
class ClaripyRecursionError: public ClaripyOperationError {};
class ClaripyZeroDivisionError: public ClaripyOperationError {};

#endif
