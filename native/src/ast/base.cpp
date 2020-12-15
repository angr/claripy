/** @file */
#include "base.hpp"

#include <cstdlib>

// For clarity
using namespace AST;

/** @todo: implement rest of repr */
std::shared_ptr<Base> Base::factory(const Ops::Operations op, const std::vector<Base> args,
                                    const std::vector<std::string> &variables, const bool symbolic,
                                    const Int length, const Simplify simplified,
                                    const std::set<BackendID> errored,
                                    const std::vector<BackendID> eager_backends,
                                    const std::set<Annotation::Base> annotations) {
    return (std::shared_ptr<Base>) 0;
}

Base::Base() : hash("") {}

// Returns a string representation of this
/** @todo: implement rest of repr */
std::string Base::repr(const bool inner, const Int max_depth, const bool explicit_length) const {
    if (std::getenv("WORKER") == nullptr) {
        return "<AST something>";
    } else {
        /* return this->shallow_repr(inner, max_depth, explicit_length); */
        return "TODO";
    }
}

// Return the name of the type this class represents
std::string Base::type_name() const {
    return "AST::Base";
}
