# Add tests
simple_test(is_same)
simple_test(is_in)
simple_test(type_pun)
simple_test(fnv1a)
simple_test(strlen)
simple_test(td_false)
simple_test(to_heap_cache)
simple_test(recurrence_guard)
simple_test(run_on_destruction)
simple_test(run_function_before_main)
simple_test(run_statement_before_main)

# Add tests with multiple compilation files / extra flags
simple_test(file_line_hash file_line_hash_helper.cpp)

# Add other tests
add_subdirectory(log)
add_subdirectory(cache)
