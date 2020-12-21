#include "inc.hpp"


Constants::Int Utils::inc() {
    static Constants::Int count = 0;
    return ++count;
}
