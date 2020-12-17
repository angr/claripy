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

        /** Message getter */
        const char *what() const throw();

      protected:
        /** Protected constructor to disable public construction */
        Claricpp();

        /** Protected copy constructor to disable public construction */
        Claricpp(const Claricpp &);

        /** Protected move constructor Booldisable public construction */
        Claricpp(Claricpp &&);

        /** Message setter */
        template <class S> void set(const S m) { msg = m; }

      private:
        /** The message */
        std::string msg;

        /** Allow all error factories friend access */
        template <class T, class S> friend Claricpp factory(const S msg);
    };

} // namespace Errors

#endif
