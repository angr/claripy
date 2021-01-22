# Add other tests
add_subdirectory(log)

# Add tests
simple_test(recurrence_guard)
simple_test(run_on_destruction)
simple_test(run_function_before_main)
simple_test(run_statement_before_main)
