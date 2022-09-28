/**
 * @file
 * \ingroup api
 */
#include "py_shim_code.hpp"

#include "constants.hpp"

#include <regex>
#include <sstream>

// Constants
static const std::string cname { "__TempImportWrapper" };
static const std::string fname { "get" };

const std::string API::py_cepan_mi { "clari.py_err._internal.Base" };
std::string API::py_get_excp(const std::string &qual_name) {
    std::ostringstream s;
    s << cname << '.' << fname << "('" << API::root_mod_name << '.' << qual_name << "')";
    return s.str();
}

/** Generate the py_locate_exceptions code */
static std::string gen_locate_exceptions() {
    static const std::string err_msg { "Could not find designated base class: " };
    // Note: this function could use far less python code if we chose not
    // to namespace, provide clean error messages, and optimize via cepan_mi
    std::ostringstream gen;
    // Note: To make this much more readable we call the wrapper class 'WC'
    // All occurrences of the string WC will be replaced afterwards
    // We start by wrapping everything in a class to avoid name pollution
    gen << "class WC:\n\tpass\n"
        // We use lambdas instead of def to avoid pollution this unknown environment
        // Lambda's do not like try-catch blocks or raise statements so we roll our own
        << "WC.key_err = lambda x: (_ for _ in ()).throw(KeyError('" << err_msg << "' + x))\n"
        << "WC.try_get = lambda dct, x: dct[x] if x in dct else WC.key_err(x)\n"
        // Define a function to extract a class by name from a list of type objects
        << R"(WC.get_from = lambda cs, x: WC.try_get({ str(i).split("'")[1]:i for i in cs }, x))"
           "\n"
        // We speed things up by locating cepan_mi first
        << "WC.cepan_mi = WC.get_from(Exception.__subclasses__(), '" << API::py_cepan_mi
        << "')\n"
        // Get all descendants classes of the cepan_mi base class
        << "WC.subs = lambda lst: lst + [k for i in lst for k in WC.subs(i.__subclasses__())]\n"
        // Define a safe getter
        << "WC.get = lambda x: WC.get_from(WC.subs(WC.cepan_mi.__subclasses__()), x)\n";
    return std::regex_replace(gen.str(), std::regex { "WC" }, cname);
}
const std::string API::py_locate_exceptions { gen_locate_exceptions() };
