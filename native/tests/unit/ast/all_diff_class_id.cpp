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
#include "testlib.hpp"

#include <set>


// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Each construction should have a unique pointer */
int all_diff_class_id() {

    const auto a1 = construct_ast<Base>();
    const auto a2 = construct_ast<Bool>();
    const auto a3 = construct_ast<BV>();
    const auto a4 = construct_ast<FP>();
    const auto a5 = construct_ast<VS>();
    const auto a6 = construct_ast<String>();
    const auto a7 = construct_ast<Bits>(0);

    std::set<Constants::Int> ids;
    ids.insert(a1->class_id());
    ids.insert(a2->class_id());
    ids.insert(a3->class_id());
    ids.insert(a4->class_id());
    ids.insert(a5->class_id());
    ids.insert(a6->class_id());
    ids.insert(a7->class_id());

    UNITTEST_ASSERT(ids.size() == 7)
    return 0;
}
