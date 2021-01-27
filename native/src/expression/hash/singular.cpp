/** @file */
#include "singular.hpp"

#include "../../annotation.hpp"

#include <sstream>


// For brevity
using namespace Expression;
template <typename T> using Ret = typename Hash::SingularRetMap<T>::RetType;


// A macro for simplicity
#define SINGULAR(T, N) template <> Ret<T> Hash::singular<T>(T const &N)


/** A specialization for T = char * */
SINGULAR(char *, c) {
    return c;
}

/** A specialization for T = std::string */
SINGULAR(std::string, s) {
    return s;
}

/** A specialization for T = Constants::Int */
SINGULAR(Constants::Int, c) {
    return c;
}

/** A specialization for T = Constants::UInt */
SINGULAR(Constants::UInt, c) {
    return c;
}

/** A specialization for T = std::vector<std::shared_ptr<Annotation::Base>> */
SINGULAR(std::vector<std::shared_ptr<Annotation::Base>>, v) {
    std::ostringstream s;
    for (const auto &ptr : v) {
        s << ptr->hash();
    }
    return s.str();
}
