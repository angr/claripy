/**
 * @file
 * \ingroup util
 * @brief This file defines Util::range_to_str
 */
#ifndef R_SRC_UTIL_RANGETOSTR_HPP_
#define R_SRC_UTIL_RANGETOSTR_HPP_

#include "ref.hpp"

#include "../constants.hpp"

#include <sstream>


namespace Util {

    /** This function takes in two iterators and returns delim.join(elms) where elms is
     *  every element from begin, inclusive to end, exclusive
     */
    template <typename Itr>
    inline std::string range_to_str(Itr begin, const Itr &end, CCSC delim = ", ") {
        std::ostringstream s;
        s << *(begin++);
        for (; begin != end; ++begin) {
            s << delim << *begin;
        }
        return s.str();
    }

    /** This function applies range_to_str to a container's elements */
    template <typename T> std::string container_to_str(const T &c, CCSC delim = ", ") {
        if (LIKELY(not c.empty())) {
            return range_to_str(c.begin(), c.end(), delim);
        }
        return "{empty container}";
    }

} // namespace Util

#endif
