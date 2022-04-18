/**
 * @file
 * @brief This file defines python code used for the multiple inheritance shim
 * \ingroup api
 */
#ifndef R_API_PYSHIMCODE_HPP_
#define R_API_PYSHIMCODE_HPP_

#include <string>
#include <utility>

namespace API {

    /** Python path to base claricpp exception analog
     *  Every non-builtin analog exception must derived from this
     */
    extern const std::string py_cepan_mi;

    /** Python code used to locate exceptions
     *  This allows us to reference clari.xyz mid-import
     *  before clari is available to reference from
     */
    extern const std::string py_locate_exceptions;

    /** Generate python code to get a located exception
     *  This allows us to reference clari.xyz mid-import
     *  before clari is available to reference from
     *  qual_name must be fully module-qualified excluding the root module
     */
    std::string py_get_excp(const std::string &qual_name);

} // namespace API

#endif
