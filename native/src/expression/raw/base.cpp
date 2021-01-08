/** @file */
#include "base.hpp"

#include "../../utils.hpp"


// For brevity
using namespace Expression;
using namespace Utils::Error::Unexpected;


Raw::Base::Base()
    : id(0) { EXPRESSION_RAW_ILLEGAL_CTOR("Expression::Raw::Base") }

      Raw::Base::Base(const Hash h, ::std::set<Annotation::Base> &&ans)
    : id(h), annotations(ans) {}

Raw::Base::~Base() {}
