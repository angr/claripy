/**
 * @file
 * @brief This file contains macros used across ast/raw_types
 */
#ifndef __AST_RAWTYPES_MACROS_HPP__
#define __AST_RAWTYPES_MACROS_HPP__

/** Declare the class_id function */
#define DECLARE_AST_CLASS_ID_FUNCTION                                                             \
    /** Return the unique AST ID of this class */                                                 \
    virtual Constants::Int class_id() const;

/** Declare ID functions each AST class must declare and define uniquely */
#define DECLARE_AST_SUBBASE_TYPENAME                                                              \
    /** Return the name of the type this class represents */                                      \
    virtual std::string type_name() const;

/** Declare ID functions each AST class must declare and define uniquely */
#define DECLARE_AST_SUBBITS_TYPENAME                                                              \
    /** Return the name of the type this class represents irrespective of length */               \
    std::string fundamental_type_name() const;

/** Define class ID function */
#define DEFINE_CLASS_ID_FUNCTION(CLASS)                                                           \
    Constants::Int AST::RawTypes::CLASS::class_id() const { return Utils::inc(); }

/** Define AST ID functions for AST::Base subtypes, inclusive */
#define DEFINE_AST_SUBBASE_ID_FUNCTIONS(CLASS)                                                    \
    std::string AST::RawTypes::CLASS::type_name() const { return "AST::" #CLASS; }                \
    DEFINE_CLASS_ID_FUNCTION(CLASS)

/** Define AST ID functions for AST::Bits subtypes, inclusive */
#define DEFINE_AST_SUBBITS_ID_FUNCTIONS(CLASS)                                                    \
    std::string AST::RawTypes::CLASS::fundamental_type_name() const { return "AST::" #CLASS; }    \
    DEFINE_CLASS_ID_FUNCTION(CLASS)

/** Grant friend access as needed to permit factory construction of this AST type */
#define GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                                     \
    /** Allow factories friend access */                                                          \
    template <typename T, typename... Args>                                                       \
    friend T factory(std::set<BackendID> &&eager_backends, Args &&...args);                       \
    /** Allow cache friend access                                                                 \
     *  We expose the constructor so that the cache may emplace new objects, which is             \
     *  faster than copying them in                                                               \
     */                                                                                           \
    friend class ::AST::Private::Cache<Hash, Base>;

/** Setup a normal subclass of AST::Base, inclusive */
#define INIT_AST_BASE_SUBCLASS(CLASS)                                                             \
    GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                                         \
    DECLARE_AST_SUBBASE_TYPENAME                                                                  \
    DECLARE_AST_CLASS_ID_FUNCTION                                                                 \
    DELETE_DEFAULTS(CLASS)

/** Setup a normal subclass of AST::Bits, inclusive */
#define INIT_AST_BITS_SUBCLASS(CLASS)                                                             \
    GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                                         \
    DECLARE_AST_SUBBITS_TYPENAME                                                                  \
    DECLARE_AST_CLASS_ID_FUNCTION                                                                 \
    DELETE_DEFAULTS(CLASS)

#endif
