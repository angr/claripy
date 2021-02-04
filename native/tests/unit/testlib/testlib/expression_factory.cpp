/**
 * @file
 * \ingroup testlib
 */
#include "expression_factory.hpp"


// For brevity
using namespace Expression;
using namespace UnitTest;


ConcreteIntLiteral TestLib::literal_int(const Constants::Int i) {
    std::vector<Factory::Ptr<const Annotation::Base>> a;
    Constants::CCSC cs { reinterpret_cast<Constants::CCS>(&i) }; // NOLINT
    const std::string s(cs, 8);
    return factory<ConcreteIntLiteral>(a, 64_ui, s);
}
