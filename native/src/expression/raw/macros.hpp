/**
 * @file
 * @brief Macros used across expression raw
 */
#ifndef __EXPRESSION_RAW_MACROS_HPP__
#define __EXPRESSION_RAW_MACROS_HPP__

#include "../../macros.hpp"
#include "../../utils.hpp"

#include <memory>


/** A macro to declare a shared pointer to X in Expression */
#define EXPRESSION_RAW_DECLARE_SHARED(X, NAMESPACE)                                               \
    /** Declare a shared pointer to X in Expression */                                            \
    using X = std::shared_ptr<NAMESPACE::X>;

/** Define a unique type id for each type */
#define DEFINE_TYPEID static const constexpr Constants::UInt id = UTILS_FILE_LINE_HASH;

/** Used to initalize an instantiable expression
 *  This macro will end in a 'private' state
 */
#define EXPRESSION_RAW_INSTANTIABLE_INIT(CLASS)                                                   \
    /* Disallow construction without using the one specified constructor */                       \
    SET_IMPLICITS(CLASS, delete)                                                                  \
  public:                                                                                         \
    DEFINE_TYPEID                                                                                 \
    /** Non-virtual destructor */                                                                 \
    ~CLASS() override final;                                                                      \
                                                                                                  \
  private:                                                                                        \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::Utils::Cache<Hash::Hash, ::Expression::Raw::Base>;


/** Used to initalize an abstract expression that uses the implict constructors
 *  This macro will end in a 'private' state
 */
#define EXPRESSION_RAW_ABSTRACT_INIT_IMPLICIT_CTOR(CLASS)                                         \
  public:                                                                                         \
    DEFINE_TYPEID                                                                                 \
  protected:                                                                                      \
    /** Use the default constructor */                                                            \
    CLASS() = default;                                                                            \
                                                                                                  \
    /** Pure virtual destructor */                                                                \
    virtual ~CLASS() = 0;                                                                         \
                                                                                                  \
  private:                                                                                        \
    /* Disallow construction without using the specified constructors */                          \
    SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, delete)


/** Used to initalize an abstract expression that has a custom constructor
 *  This macro will end in a 'private' state
 */
#define EXPRESSION_RAW_ABSTRACT_INIT_CUSTOM_CTOR(CLASS)                                           \
  public:                                                                                         \
    DEFINE_TYPEID                                                                                 \
  protected:                                                                                      \
    /** Pure virtual destructor */                                                                \
    virtual ~CLASS() = 0;                                                                         \
                                                                                                  \
  private:                                                                                        \
    /* Disallow construction without using the specified constructors */                          \
    SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, delete)


#endif
