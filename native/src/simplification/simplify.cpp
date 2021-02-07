/** @file */
#include "simplify.hpp"

#include "../utils.hpp"


// Define the simplifications log
UTILS_LOG_DEFINE_LOG_CLASS(Simplify)


Factory::Ptr<Expression::Base>
Simplification::simplify(const Factory::Ptr<Expression::Base> &old) {
#if 0

    if (auto lookup { Pvt::op_map.find(old->op) }; lookup != Pvt::op_map.end()) {
        return lookup->second(old);
    }
    else {
        Log::verbose<Simplify>("No simplifier for operation: ", old->op);
        return old;
    }
#else
    return old;
#endif
}
