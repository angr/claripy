/** @file */

#include "ast/base.hpp"
#include "ast/bits.hpp"
#include "ast/bool.hpp"
#include "ast/bv.hpp"
#include "ast/cast.hpp"
#include "ast/factory.hpp"
#include "ast/fp.hpp"
#include "ast/int.hpp"
#include "ast/string.hpp"
#include "ast/vs.hpp"
#include "ops/operations.hpp"

#include <set>


// For brevity
using namespace AST;


/** Each construction should have a unique pointer */
int all_diff_class_id() {

    std::set<BackendID> s;
    const auto a1 = factory<AST::FP>(std::move(s), std::move((Ops::Operation) 0));
    const auto a2 = factory<AST::VS>(std::move(s), std::move((Ops::Operation) 0));
    const auto a3 = factory<AST::BV>(std::move(s), std::move((Ops::Operation) 0));
    const auto a4 = factory<AST::Base>(std::move(s), std::move((Ops::Operation) 0));
    const auto a5 = factory<AST::Bool>(std::move(s), std::move((Ops::Operation) 0));
    const auto a6 = factory<AST::String>(std::move(s), std::move((Ops::Operation) 0));
    const auto a7 = factory<AST::Bits>(std::move(s), std::move((Ops::Operation) 0), std::move(0));

    std::set<Constants::Int> ids;
    ids.insert(a1->class_id());
    ids.insert(a2->class_id());
    ids.insert(a3->class_id());
    ids.insert(a4->class_id());
    ids.insert(a5->class_id());
    ids.insert(a6->class_id());
    ids.insert(a7->class_id());

    if (ids.size() == 7) {
        return 0;
    }
    else {
        return 1;
    }
}
