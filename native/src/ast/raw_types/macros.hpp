/**
 * @file
 * @brief This file contains macros used across ast/raw_types
 */
#ifndef __AST_RAWTYPES_MACROS_HPP__
#define __AST_RAWTYPES_MACROS_HPP__

/** Declare the class_id function */
#define DECLARE_AST_CLASS_ID_FUNCTIONS                                                            \
    /** Return the unique AST ID of this class */                                                 \
    static inline Constants::Int static_class_id();                                               \
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
#define DEFINE_CLASS_ID_FUNCTIONS(CLASS)                                                          \
    Constants::Int AST::RawTypes::CLASS::static_class_id() {                                      \
        const static auto ret = Utils::inc();                                                     \
        return ret;                                                                               \
    }                                                                                             \
    Constants::Int AST::RawTypes::CLASS::class_id() const {                                       \
        return AST::RawTypes::CLASS::static_class_id();                                           \
    }

/** Define AST ID functions for AST::Base subtypes, inclusive */
#define DEFINE_AST_SUBBASE_ID_FUNCTIONS(CLASS)                                                    \
    std::string AST::RawTypes::CLASS::type_name() const { return "AST::" #CLASS; }                \
    DEFINE_CLASS_ID_FUNCTIONS(CLASS)

/** Define AST ID functions for AST::Bits subtypes, inclusive */
#define DEFINE_AST_SUBBITS_ID_FUNCTIONS(CLASS)                                                    \
    std::string AST::RawTypes::CLASS::fundamental_type_name() const { return "AST::" #CLASS; }    \
    DEFINE_CLASS_ID_FUNCTIONS(CLASS)

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

/** Setup a normal subclass of AST::Base, inclusive
 *  Warning: this macro declares what is below it as private
 */
#define INIT_AST_BASE_SUBCLASS(CLASS)                                                             \
  public:                                                                                         \
    DECLARE_AST_SUBBASE_TYPENAME                                                                  \
    DECLARE_AST_CLASS_ID_FUNCTIONS                                                                \
  private:                                                                                        \
    GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                                         \
    DELETE_DEFAULTS(CLASS)

/** Setup a normal subclass of AST::Bits, inclusive
 *  Warning: this macro declares what is below it as private
 */
#define INIT_AST_BITS_SUBCLASS(CLASS)                                                             \
  public:                                                                                         \
    DECLARE_AST_SUBBITS_TYPENAME                                                                  \
    DECLARE_AST_CLASS_ID_FUNCTIONS                                                                \
  private:                                                                                        \
    GRANT_FACTORY_AND_CACHE_FRIEND_ACCESS                                                         \
    DELETE_DEFAULTS(CLASS)

#endif
