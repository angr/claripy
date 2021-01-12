/** @file */
#include "factory.hpp"

using namespace Expression;
using namespace UnitTest;

ConcreteIntLiteral TestLib::literal_factory(Constants::Int i) {
    std::vector<std::shared_ptr<Annotation::Base>> a;
    return factory<ConcreteIntLiteral>(a, i);
}
