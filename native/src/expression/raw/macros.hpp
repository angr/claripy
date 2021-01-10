/**
 * @file
 * @brief Macros used across expression raw
 */
#ifndef __EXPRESSION_RAW_MACROS_HPP__
#define __EXPRESSION_RAW_MACROS_HPP__

#include <memory>


/** A macro to declare a shared pointer to X in Expression */
#define EXPRESSION_RAW_DECLARE_SHARED(X, NAMESPACE)                                               \
    /** Declare a shared pointer to X in Expression */                                            \
    using X = std::shared_ptr<NAMESPACE::X>;


/** Used to initalize an instantiable expression
 *  This macro will end in a 'private' state
 */
#define EXPRESSION_RAW_INSTANTIABLE_INIT(CLASS)                                                   \
    DELETE_DEFAULTS(CLASS)                                                                        \
  public:                                                                                         \
    /** Non-virtual destructor */                                                                 \
    ~CLASS() override final;                                                                      \
    /** Allow factories friend access */                                                          \
    template <typename T, typename... Args> friend T Expression::factory(Args &&...args);         \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::Expression::Private::Cache<Hash::Hash, Base>;


/** Used to initalize an abstract expression
 *  This macro will end in a 'private' state
 */
#define EXPRESSION_RAW_ABSTRACT_INIT(CLASS)                                                       \
  public:                                                                                         \
    /** Pure virtual destructor */                                                                \
    virtual ~CLASS() = 0;                                                                         \
                                                                                                  \
  private:                                                                                        \
    /** Delete copy constructor */                                                                \
    CLASS(const CLASS &) = delete;                                                                \
    /** Delete move constructor */                                                                \
    CLASS(CLASS &&) = delete;


#endif
