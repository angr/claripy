/** @file */
#include "simplify.hpp"

#include "private/op_map.hpp"

#include "../ast/base.hpp"
#include "../utils/log.hpp"


// For brevity
namespace Log = Utils::Log;
namespace Pvt = Simplifications::Private;

// Define the simplifications log
class SimpLog {
    constexpr static auto log_id = "Simplify";
};

AST::Base Simplifications::simplify(const AST::Base &old) {
    auto lookup = Pvt::op_map.find(old->op);
    if (lookup != Pvt::op_map.end()) {
        return lookup->second(old);
    }
    else {
        Log::verbose<SimpLog>("No simplifier for operation: ", old->op);
        return old;
    }
}
