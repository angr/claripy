# Use boost
find_package(Boost 1.71 REQUIRED COMPONENTS unit_test_framework)
include_directories("${Boost_INCLUDE_DIRS}")


# Test modules
set(AST "ast")

# Create test modules
add_executable("${AST}" ast.cpp)

# Link test modules
target_link_libraries("${AST}"
	"${SHARED_LIB_NAME}"
	Boost::unit_test_framework
)

# Add modules to test target
add_test("${AST}" "${AST}")
