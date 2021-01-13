/**
 * @file
 * \ingroup utils
 * @brief This file contains the base claricpp exception
 * These exceptions have python analogs and must be caught and sent to python
 * via a different method.
 */
#ifndef __UTILS_ERRORS_CLARICPP_HPP__
#define __UTILS_ERRORS_CLARICPP_HPP__

#include "../to_str.hpp"

#include <exception>
#include <string>


namespace Utils::Error {

	/** The base claricpp exception class
     *  Any exception thrown intentioanlly must subclass this
	 */
    class Claricpp : public std::exception {
      public:
        /** Public constructor
         *  This constructor consumes its arguments via const reference
         */
        template <typename... Args> Claricpp(const Args &...args) : msg(Utils::to_str(args...)) {}

        /** Virtual destructor */
        virtual ~Claricpp();

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

} // namespace Utils::Error

#endif
