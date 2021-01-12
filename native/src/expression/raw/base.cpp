/** @file */
#include "base.hpp"

#include <memory>


// For brevity
using namespace Expression;
using namespace Utils::Error::Unexpected;


Raw::Base::~Base() {}

Raw::Base::Base(const Hash::Hash h, std::vector<std::shared_ptr<Annotation::Base>> &ans)
    : id(h), annotations(std::move(ans)) {}

std::string Raw::Base::full_type_name() const {
    std::stringstream s;
    s << (this->symbolic() ? "Symbolic" : "Concrete") << this->type() << this->op();
    return s.str();
}
