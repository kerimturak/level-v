/*
 ****************************************************************************
 *
 *                   "DHRYSTONE" Benchmark Program
 *                   -----------------------------
 *
 *  Version:    C, Version 2.1
 *
 *  File:       dhry.h
 *
 *  Date:       May 25, 1988
 *
 *  Author:     Reinhold P. Weicker
 *
 ****************************************************************************
 */

#ifndef DHRY_H
#define DHRY_H

#include <stddef.h>

/* Minimal printf/string support */
extern int printf(const char *format, ...);
extern char *strcpy(char *dest, const char *src);
extern int strcmp(const char *s1, const char *s2);

/* General definitions */

#define Null    0
#define true    1
#define false   0

typedef int     One_Thirty;
typedef int     One_Fifty;
typedef char    Capital_Letter;
typedef int     Boolean;
typedef char    Str_30[31];
typedef int     Arr_1_Dim[50];
typedef int     Arr_2_Dim[50][50];

typedef enum {
    Ident_1,
    Ident_2,
    Ident_3,
    Ident_4,
    Ident_5
} Enumeration;

typedef struct record {
    struct record  *Ptr_Comp;
    Enumeration     Discr;
    union {
        struct {
            Enumeration Enum_Comp;
            int         Int_Comp;
            char        Str_Comp[31];
        } var_1;
        struct {
            Enumeration E_Comp_2;
            char        Str_2_Comp[31];
        } var_2;
        struct {
            char        Ch_1_Comp;
            char        Ch_2_Comp;
        } var_3;
    } variant;
} Rec_Type, *Rec_Pointer;

/* Structure assignment macro */
#define structassign(d, s)  (d) = (s)

/* Global variables */
extern int             Int_Glob;
extern Boolean         Bool_Glob;
extern char            Ch_1_Glob;
extern char            Ch_2_Glob;
extern int             Arr_1_Glob[50];
extern int             Arr_2_Glob[50][50];
extern Rec_Pointer     Ptr_Glob;
extern Rec_Pointer     Next_Ptr_Glob;

/* Function prototypes */
void Proc_1 (Rec_Pointer Ptr_Val_Par);
void Proc_2 (One_Fifty *Int_Par_Ref);
void Proc_3 (Rec_Pointer *Ptr_Ref_Par);
void Proc_4 (void);
void Proc_5 (void);
void Proc_6 (Enumeration Enum_Val_Par, Enumeration *Enum_Ref_Par);
void Proc_7 (One_Fifty Int_1_Par_Val, One_Fifty Int_2_Par_Val,
             One_Fifty *Int_Par_Ref);
void Proc_8 (Arr_1_Dim Arr_1_Par_Ref, Arr_2_Dim Arr_2_Par_Ref,
             int Int_1_Par_Val, int Int_2_Par_Val);

Enumeration Func_1 (Capital_Letter Ch_1_Par_Val, Capital_Letter Ch_2_Par_Val);
Boolean Func_2 (Str_30 Str_1_Par_Ref, Str_30 Str_2_Par_Ref);
Boolean Func_3 (Enumeration Enum_Par_Val);

#endif /* DHRY_H */
