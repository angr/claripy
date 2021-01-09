/** @file */
#include "base.hpp"


// For brevity
using namespace Expression;
using namespace Utils::Error::Unexpected;


Raw::Base::~Base() {}

std::string Raw::Base::full_type_name() const {
    std::stringstream s;
    s << (this->symbolic() ? "Symbolic" : "Concrete") << this->type() << this->op();
    return s.str();
}
