/**
 * @file
 * @brief This defines macros used across SOC
 */
#ifndef __SOC_MACROS_HPP__
#define __SOC_MACROS_HPP__

#include "../factory.hpp"


/** Allows factory construction of final types */
#define SOC_INIT FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(::SOC::Base)


#endif
