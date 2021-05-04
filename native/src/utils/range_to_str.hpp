/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::range_to_str
 */
#ifndef __UTILS_RANGETOSTR_HPP__
#define __UTILS_RANGETOSTR_HPP__

#include "ref.hpp"

#include "../constants.hpp"

#include <sstream>


namespace Utils {

    /** This function takes in two iterators and returns delim.join(elms) where elms is
     *  every element from begin, inclusive to end, exclusive
     */
    template <typename Itr>
    inline std::string range_to_str(Itr begin, const Itr &end, Constants::CCSC delim = ", ") {
        std::ostringstream s;
        s << *(begin++);
        for (; begin != end; ++begin) {
            s << delim << *begin;
        }
        return s.str();
    }

    /** This function applies range_to_str to a container's elements */
    template <typename T> std::string container_to_str(const T &c, Constants::CCSC delim = ", ") {
        return range_to_str(c.begin(), c.end(), delim);
    }

} // namespace Utils

#endif
