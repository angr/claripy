/** @file */
#include "simplify.hpp"

#include "private/op_map.hpp"

#include "../ast/base.hpp"
#include "../utils/log.hpp"


// For brevity
namespace Log = Utils::Log;
namespace Pvt = Simplification::Private;


// Define the simplifications log
UTILS_LOG_DEFINE_LOG_CLASS(Simplify)


AST::Base Simplifications::simplify(const AST::Base &old) {
    auto lookup = Pvt::op_map.find(old->op);
    if (lookup != Pvt::op_map.end()) {
        return lookup->second(old);
    }
    else {
        Log::verbose<Simplify>("No simplifier for operation: ", old->op);
        return old;
    }
}
