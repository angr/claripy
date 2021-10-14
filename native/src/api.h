/**
 * @file
 * @brief This header exposes the C API for claricpp
 */
#ifndef R_API_H_
#define R_API_H_

/********************************************************************/
/*                    Forward Type Declarations                     */
/********************************************************************/

/** Holds an Annotation::BasePtr reference */
struct ClaricppAnnotation;

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

/** Return a new Annotation::Base */
ClaricppAnnotation * claricpp_annotation_new_base();

/** Return a new Annotation::SimplificationAvoidance */
ClaricppAnnotation * claricpp_annotation_new_simplification_avoicance();

/********************************************************************/
/*                            Expression                            */
/********************************************************************/

/********************************************************************/
/*                              Create                              */
/********************************************************************/

/********************************************************************/
/*                             Backend                              */
/********************************************************************/



#endif