/**
 * @file
 * @brief This file contains macros used across ast/raw_types
 */
#ifndef __AST_RAWTYPES_MACROS_HPP__
#define __AST_RAWTYPES_MACROS_HPP__


/************************************************/
/*             Encompassing macros              */
/************************************************/

/** Setup a normal subclass of AST::Base, inclusive
 *  Warning: this macro declares what is below it as private
 *  This macro uses a function from the top level macros.hpp, so it must be included to use this!
 */
#define AST_RAWTYPES_INIT_AST_BASE_SUBCLASS(CLASS)                                                \
  public:                                                                                         \
    AST_RAWTYPES_DECLARE_AST_SUBBASE_TYPENAME                                                     \
    AST_RAWTYPES_DECLARE_AST_CLASS_IDS                                                            \
  private:                                                                                        \
    AST_RAWTYPES_GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                            \
    DELETE_DEFAULTS(CLASS)

/** Setup a normal subclass of AST::Bits, inclusive
 *  Warning: this macro declares what is below it as private
 *  This macro uses a function from the top level macros.hpp, so it must be included to use this!
 */
#define AST_RAWTYPES_INIT_AST_BITS_SUBCLASS(CLASS)                                                \
  public:                                                                                         \
    AST_RAWTYPES_DECLARE_AST_SUBBITS_TYPENAME                                                     \
    AST_RAWTYPES_DECLARE_AST_CLASS_IDS                                                            \
  private:                                                                                        \
    AST_RAWTYPES_GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                            \
    DELETE_DEFAULTS(CLASS)

/************************************************/
/*             Helper Declarations              */
/************************************************/

/** Declare the class_id function */
#define AST_RAWTYPES_DECLARE_AST_CLASS_IDS                                                        \
    /** The unique AST ID of this class */                                                        \
    static const Constants::Int static_class_id;                                                  \
    /** Return the unique AST ID of this class */                                                 \
    virtual Constants::Int class_id() const;

/** Declare ID functions each AST class must declare and define uniquely */
#define AST_RAWTYPES_DECLARE_AST_SUBBASE_TYPENAME                                                 \
    /** Return the name of the type this class represents */                                      \
    virtual std::string type_name() const;

/** Declare ID functions each AST class must declare and define uniquely */
#define AST_RAWTYPES_DECLARE_AST_SUBBITS_TYPENAME                                                 \
    /** Return the name of the type this class represents irrespective of length */               \
    std::string fundamental_type_name() const;

/** Grant friend access as needed to permit factory construction of this AST type */
#define AST_RAWTYPES_GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                        \
    /** Allow factories friend access */                                                          \
    template <typename T, typename... Args>                                                       \
    friend T factory(std::set<BackendID> &&eager_backends, Args &&...args);                       \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::AST::Private::Cache<Hash, Base>;

/************************************************/
/*                 Definitions                  */
/************************************************/

/** Define class ID function */
#define AST_RAWTYPES_DEFINE_CLASS_IDS(CLASS)                                                      \
    const Constants::Int AST::RawTypes::CLASS::static_class_id = Utils::inc<Base>();              \
    Constants::Int AST::RawTypes::CLASS::class_id() const {                                       \
        return AST::RawTypes::CLASS::static_class_id;                                             \
    }

/** Define AST ID functions for AST::Base subtypes, inclusive */
#define AST_RAWTYPES_DEFINE_AST_SUBBASE_ID_FUNCTIONS(CLASS)                                       \
    std::string AST::RawTypes::CLASS::type_name() const { return "AST::" #CLASS; }                \
    AST_RAWTYPES_DEFINE_CLASS_IDS(CLASS)

/** Define AST ID functions for AST::Bits subtypes, inclusive */
#define AST_RAWTYPES_DEFINE_AST_SUBBITS_ID_FUNCTIONS(CLASS)                                       \
    std::string AST::RawTypes::CLASS::fundamental_type_name() const { return "AST::" #CLASS; }    \
    AST_RAWTYPES_DEFINE_CLASS_IDS(CLASS)


#endif
