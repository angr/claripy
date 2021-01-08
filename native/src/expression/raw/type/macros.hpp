/**
:q
 * @file
 * @brief This file contains macros used across expression / types
 */
#ifndef __EXPRESSION_RAW_TYPE_MACROS_HPP__
#define __EXPRESSION_RAW_TYPE_MACROS_HPP__


/************************************************/
/*             Encompassing macros              */
/************************************************/

/** Setup a normal subclass of EXPRESSION::Base, inclusive
 *  Warning: this macro declares what is below it as private
 *  This macro uses a function from the top level macros.hpp, so it must be included to use this!
 */
#define EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BASE_SUBCLASS(CLASS)                                  \
  public:                                                                                         \
    PURE_VIRT_DESTRUCTOR(CLASS)                                                                   \
    EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_SUBBASE_TYPENAME                                       \
    EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_CLASS_IDS                                              \
  private:                                                                                        \
    EXPRESSION_RAW_TYPE_GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                     \
    DELETE_DEFAULTS(CLASS)

/** Setup a normal subclass of EXPRESSION::Bits, inclusive
 *  Warning: this macro declares what is below it as private
 *  This macro uses a function from the top level macros.hpp, so it must be included to use this!
 */
#define EXPRESSION_RAW_TYPE_INIT_EXPRESSION_BITS_SUBCLASS(CLASS)                                  \
  public:                                                                                         \
    PURE_VIRT_DESTRUCTOR(CLASS)                                                                   \
    EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_SUBBITS_TYPENAME                                       \
    EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_CLASS_IDS                                              \
  private:                                                                                        \
    EXPRESSION_RAW_TYPE_GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                     \
    DELETE_DEFAULTS(CLASS)

/************************************************/
/*             Helper Declarations              */
/************************************************/

/** Declare a pure virtual destructor */
#define PURE_VIRT_DESTRUCTOR(CLASS) virtual ~CLASS() = 0;

/** Declare the class_id function */
#define EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_CLASS_IDS                                          \
    /** The unique Expression ID of this class */                                                 \
    static const Constants::Int static_class_id;                                                  \
    /** Return the unique Expression ID of this class */                                          \
    virtual Constants::Int class_id() const;

/** Declare ID functions each Expression class must declare and define uniquely */
#define EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_SUBBASE_TYPENAME                                   \
    /** Return the name of the type this class represents */                                      \
    virtual std::string type_name() const;

/** Declare ID functions each Expression class must declare and define uniquely */
#define EXPRESSION_RAW_TYPE_DECLARE_EXPRESSION_SUBBITS_TYPENAME                                   \
    /** Return the name of the type this class represents irrespective of length */               \
    std::string fundamental_type_name() const;

/** Grant friend access as needed to permit factory construction of this Expression type */
#define EXPRESSION_RAW_TYPE_GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                 \
    /** Allow factories friend access */                                                          \
    template <typename T, typename... Args>                                                       \
    friend T Expression::factory(std::set<BackendID> &&eager_backends, Args &&...args);           \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::Expression::Private::Cache<Hash, Base>;

/************************************************/
/*                 Definitions                  */
/************************************************/

/** Define class ID function */
#define EXPRESSION_RAW_TYPE_DEFINE_CLASS_IDS(CLASS)                                               \
    const Constants::Int Expression::Raw::Type::CLASS::static_class_id = Utils::inc<Base>();      \
    Constants::Int Expression::Raw::Type::CLASS::class_id() const {                               \
        return Expression::Raw::Type::CLASS::static_class_id;                                     \
    }

/** Define Expression ID functions for Expression::Base subtypes, inclusive */
#define EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(CLASS)                         \
    std::string Expression::Raw::Type::CLASS::type_name() const { return "Expression::" #CLASS; } \
    EXPRESSION_RAW_TYPE_DEFINE_CLASS_IDS(CLASS)

/** Define EXPRESSION ID functions for EXPRESSION::Bits subtypes, inclusive */
#define EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBITS_ID_FUNCTIONS(CLASS)                         \
    std::string Expression::Raw::Type::CLASS::fundamental_type_name() const {                     \
        return "Expression::" #CLASS;                                                             \
    }                                                                                             \
    EXPRESSION_RAW_TYPE_DEFINE_CLASS_IDS(CLASS)


#endif
