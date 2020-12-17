/** @file */
#include "base.hpp"

#include <cstdlib>

// For clarity
using namespace AST;

/** @todo maybe make this work better with subclasses */
Base Cached::Base::factory(const Ops::Operation o) {

    // Check to see if the object to be constructed exists in the hash cache
    const Hash h = hash(o);
    auto lookup = hash_cache.find(h);

    // If it already exists in the hash cache
    if (lookup != hash_cache.end()) {
        ::AST::Base possible_ret = lookup->second.lock();
        // If the weak_ptr is valid, return it
        if (possible_ret) {
            return possible_ret;
        }
        // Otherwise remove it from the cache
        else {
            hash_cache.erase(lookup);
        }
    }

    // Since no cached object exists, construct one, cache it, then return it
    ::AST::Base ret = ::AST::Base(new Base(o, h));
    hash_cache[h] = std::weak_ptr<Base>(ret);
    return ret;
}

Hash Cached::Base::hash(const Ops::Operation o) {
    return Hash(o);
}

Cached::Base::Base(const Ops::Operation o, const Hash h) : op(o), id(h) {}

// Returns a string representation of this
/** @todo: implement rest of repr */
std::string Cached::Base::repr(const bool inner, const Constants::Int max_depth,
                               const bool explicit_length) const {
    if (std::getenv("WORKER") == nullptr) {
        return "<AST something>";
    }
    else {
        /* return this->shallow_repr(inner, max_depth, explicit_length); */
        return "TODO";
    }
}

// Return the name of the type this class represents
std::string Cached::Base::type_name() const {
    return "AST::Base";
}
