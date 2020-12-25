# Add tests
simple_test("identical_base_int")
simple_test("weak_ptr_invalidation_gc")
simple_test("weak_ptr_invalidation_find")
simple_test("gc")

# Other tests
add_subdirectory("same")
add_subdirectory("diff")
