/**
 * @file
 * \ingroup testlib
 */
#include "factory.hpp"


// For brevity
using namespace Expression;
using namespace UnitTest;


ConcreteIntLiteral TestLib::literal_int(const Constants::Int i) {
    std::vector<std::shared_ptr<Annotation::Base>> a;
    std::string s((Constants::CCSC) &i);
    return factory<ConcreteIntLiteral>(a, 64_i, s);
}
