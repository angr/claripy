/**
 * @file
 * @brief This file contains the base claricpp exception
 * These exceptions have python analogs and must be caught and sent to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERRORS_CLARICPP_HPP__
#define __ERRORS_CLARICPP_HPP__

#include <exception>
#include <string>


/** A namespace used for the errors directory */
namespace Errors {

    class Claricpp : public std::exception {
      public:
        /** Public constructor */
        template <typename S> Claricpp(const S m) : msg(m) {}

        /** Message getter */
        const char *what() const throw();

      protected:
        /** Delete default constructor */
        Claricpp() = delete;

      private:
        /** The message */
        const std::string msg;

        /** Allow all error factories friend access */
        template <typename T, typename S> friend T factory(const S msg);
    };

} // namespace Errors

#endif
