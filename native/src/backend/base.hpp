/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __BACKEND_BASE_HPP__
#define __BACKEND_BASE_HPP__

#include "../expression.hpp"

#include <memory>
#include <vector>


namespace Backend {

    /** A type-safe SolverID */
    template <typename T> struct SolverID {
        /** We actual solver ID type */
        decltype(std::vector<T>::size_type) id;
    };

    /** The base Backend type
     *  All backends must subclass this
     */
    class Base {
      public:
        // Define implicits
        SET_IMPLICITS(Base, default)

        /** Default destructor */
        virtual ~Base() = default;

        // Pure virtual functions

        /** Check whether the backend can handle the given expression */
        virtual bool handles(const Expression::BasePtr &expr) = 0;

        /** Simplify the given expression */
        virtual Expression::BasePtr simplify(const Expression::BasePtr &expr) = 0;

        /** Backend name */
        virtual Constants::CCSC name() = 0;

        // Virtual functions

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual inline void downsize() {
            clear_cache(is_true_cache);
            clear_cache(is_false_cache);
        }

        // true / false ones here
        template <bool B>
        bool is_B
            // Since B is a constant there should be no runtime overhead here
            is_b_cache = B
            ? (is_true_cache
               : is_false_cache);
        is_not_b_cache = (!B) ? (is_true_cache : is_false_cache);
        //

        // Static template functions subclasses should use for consistency

        /** Create a new solver and store it in a thread local cache
         *  Returns an interger SolverID type
         */
        template <typename T> static SolverID<T> new_solver(const std::shared_ptr<T> &solver) {
            using ID = decltype(std::vector<T>::size_type);
            static_assert(std::is_same_v<ID, decltype(std::declval<SolverID>().id)>,
                          "new_solver expects a different type for SolverID's id type");
            // Add the solver to the vector and return the size
            // Because solvers is TLS, this is thread safe without a lock
            thread_local static thread_local std::vector<std::shared_ptr<T>> solvers;
            solvers.emplace_back(solver);
            return solvers.size();
        }

      private:
        /** Convert a claricpp Expression to a backend object */
        template <typename BackendObj> BackendObj(Constants::CTSC<Expression::Base> input) {
            using BackendError = Error::Backend::Base;
            using ExprPtr = Constants::TCS<Expression::Base>;
            template <typename T> using Stack = std::stack<T, std::vector>;

            // Functionally a stack of lists of expression to be converted
            // We flatten and reverse this list for preformance reasons
            // To denote the end of a list we prefix its elements with a nullptr
            // Note prefix because we reversed the list, thus the 'end' must come first
            // Each list represents the arguments of an expression
            Stack<ExprPtr> expr_stack { nullptr, input };
            Stack<ExprPtr> op_stack;     // Expressions to give to the conversion dispatcher
            Stack<BackendObj> arg_stack; // Converted backend objects

            // For the next element in our expr_stack
            for (const auto expr = expr_stack.top(); expr_stack.size() > 0;
                 expr = expr_stack.top()) {
                expr_stack.pop()

                    // If the expression does not represent the end of a list
                    if (expr != nullptr) {

                    // Cache lookups
                    if (errored.find(expr->hash) == errored.end()) {
                        throw BackendError(name(), " cannot handle operation: ", expr->op->name());
                    }
                    else if (const auto lookup = object_cache.find(expr->hash);
                             lookup != object_cache.end()) {
                        arg_stack.emplace(lookup->second);
                    }

                    // Update stacks
                    op_stack.emplace(expr);
                    expr->add_reversed_children(expr_stack);
                }

                // If the expression represents the end of a list
                // All arguments of expr_stack.top() have been converted
                else if (expr_stack.size() != 0) {
                    expr = op_stack.top();
                    op_stack.pop();

                    // Convert the expression to a backend object
                    const auto op_id = expr->op->cuid;
                    if (auto func = ctors.find(op_id); func != ctors.end()) {
                        object_cache[op_id] = func(expr);
                    }
                    else {
                        object_cache[op_id] = conversion_dispatch(expr, arg_queue);
                    }

                    // Apply annotations
                    auto obj = object_cache[op_id];
                    for (const auto a : expr->annotations) {
                        obj = apply_annotation(obj, a);
                    }

                    // Store the result in the arg stack
                    arg_stack.emplace(obj)
                }
            }
#ifdef DEBUG
            // Sanity checks
            using UnknownErr = Utils::Error::Unexpected::Unknown;
            Utils::affirm<UnknownErr>(op_stack.size() == 0, WHOAMI "op_stack should be empty");
            Utils::affirm<UnknownErr>(expr_stack.size() == 0, WHOAMI "expr_stack should be empty");
            Utils::affirm<UnknownErr>(arg_stack.size() == 1,
                                      WHOAMI "arg_stack should be of size: 1");
#endif
            // Return result
            return arg_stack.top();
        }

        /** Clears the given thread-safe cache */
        template <typename Cache> static void clear_cache(Utils::ThreadSafe::Mutable &cache) {
            UTILS_THREADSAFE_MUTABLE_UNIQUE(c, cache)
            c.clear();
        }

        // Types

        /** A weak pointer to the expression base type */
        using WPtr = std::weak_ptr<Utils::InternalType<Expression::BasePtr>>;

        /** A weak pointer map that fundamentally maps Expressions to values
         *  weak_pointers cannot be map keys so we use the hash as a key instead
         */
        template <typename T>
        using WeapExpressionMap = std::map<Hash::Hash, const std::pair<WPtr, T>>;

        // Thread local variables

        /** object cache
         *  Map an expression hash to the result of is_true and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static Utils::ThreadSafe::Mutable<WeapExpressionMap<bool>> is_true_cache;

        /** is_false cache
         *  Map an expression hash to the result of is_true and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static Utils::ThreadSafe::Mutable<WeapExpressionMap<bool>> is_false_cache;
    };

} // namespace Backend

#endif
