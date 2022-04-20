# This file configures a few important cmake settings

# Use policies of minimum supported version
cmake_policy(VERSION "${CMAKE_MINIMUM_REQUIRED_VERSION}") # Just in case

# Manually set newer policies to old to silence dependent project warnings
# This override nothing; we are only explicitly disabling new policies implicitly disabled
# We do this as otherwise dependent projects may otherwise produce 'policy not set' warnings
if ("${CMAKE_MINIMUM_REQUIRED_VERSION}" LESS 3.22)
    # This a 3.22 policy we ignore because our policy version is less
    set(CMAKE_POLICY_DEFAULT_CMP0127 OLD) # No-op, but silences pybind11 policy warnings
endif()

# Common library paths
list(APPEND CMAKE_LIBRARY_PATH
    "/usr/lib64"
    "/usr/lib"
    "/lib64"
    "/lib"
)

# Earlier versions of cmake might not do this; homebrew's default M1 root
if (APPLE AND NOT "/opt/homebrew" IN_LIST CMAKE_SYSTEM_PREFIX_PATH)
    list(APPEND CMAKE_SYSTEM_PREFIX_PATH "/opt/homebrew")
endif()