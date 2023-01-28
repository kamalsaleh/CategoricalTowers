# SPDX-License-Identifier: GPL-2.0-or-later
# SubcategoriesForCAP: Subcategory and other related constructors for CAP categories
#
# Declarations
#

#! @Chapter Full subcategories

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of a full subcategory.
DeclareCategory( "IsCapFullSubcategory",
        IsCapSubcategory );

#! @Description
#!  The &GAP; category of a full subcategory generated by finite number of objects.
DeclareCategory( "IsCapFullSubcategoryGeneratedByFiniteNumberOfObjects",
        IsCapFullSubcategory );

#! @Description
#!  The &GAP; category of a full subcategory defined by an object-membership function.
DeclareCategory( "IsCapFullSubcategoryDefinedByObjectMembershipFunction",
        IsCapFullSubcategory );

#! @Description
#!  The &GAP; category of cells in a full subcategory.
DeclareCategory( "IsCapCategoryCellInAFullSubcategory",
        IsCapCategoryCellInASubcategory );

#! @Description
#!  The &GAP; category of objects in a full subcategory.
DeclareCategory( "IsCapCategoryObjectInAFullSubcategory",
        IsCapCategoryCellInAFullSubcategory and IsCapCategoryObjectInASubcategory );

#! @Description
#!  The &GAP; category of morphisms in a full subcategory.
DeclareCategory( "IsCapCategoryMorphismInAFullSubcategory",
        IsCapCategoryCellInAFullSubcategory and IsCapCategoryMorphismInASubcategory );

####################################
#
#! @Section Global variables
#
####################################

#!
DeclareGlobalVariable( "CAP_INTERNAL_METHOD_NAME_LIST_FOR_FULL_SUBCATEGORY" );

#!
DeclareGlobalVariable( "CAP_INTERNAL_METHOD_NAME_LIST_FOR_ADDITIVE_FULL_SUBCATEGORY" );

####################################
#
#! @Section Constructors
#
####################################

#! @Arguments C, name
DeclareOperation( "FullSubcategory",
                  [ IsCapCategory, IsString ] );

#! @Description
#!  The input is a list of objects <A>L</A> in the same category. The output is the full subcategory generated by <A>L</A>.
#! @Arguments L
#! @Returns CapFullSubcategory
DeclareGlobalFunction( "FullSubcategoryGeneratedByListOfObjects" );

DeclareOperation( "\[\]",
          [ IsCapFullSubcategoryGeneratedByFiniteNumberOfObjects, IsInt ] );

#! @Description
#!  The input is a category <A>C</A> in which the operation <C>IndecomposableProjectiveObjects</C> is computable.
#!  The output is the full subcategory of <A>C</A> generated by the output of <C>IndecomposableProjectiveObjects</C>(<A>C</A>).
#! @Arguments C
#! @Returns CapFullSubcategory
DeclareAttribute( "FullSubcategoryOfIndecomposableProjectiveObjects", IsCapCategory );

#! @Description
#!  The input is a category <A>C</A> in which the operation <C>IndecomposableInjectiveObjects</C> is computable.
#!  The output is the full subcategory of <A>C</A> generated by the output of <C>IndecomposableInjectiveObjects</C>(<A>C</A>).
#! @Arguments C
#! @Returns CapFullSubcategory
DeclareAttribute( "FullSubcategoryOfIndecomposableInjectiveObjects", IsCapCategory );

#! @Description
#!  The input is a category <A>C</A> and an object membership function <A>membership_func</A>.
#!  The output is the full subcategory of <A>C</A> determined by <A>membership_func</A>.
#! @Arguments C, membership_func
#! @Returns CapFullSubcategory
DeclareGlobalFunction( "FullSubcategoryByObjectMembershipFunction" );

#! @Description
#!  The input is an abelian category <A>C</A> with enough projective objects.
#!  The output is the full subcategory of <A>C</A> generated by the projective objects in <A>C</A>.
#! @Arguments C
#! @Returns CapFullSubcategory
DeclareAttribute( "FullSubcategoryOfProjectiveObjects", IsCapCategory );

#! @Description
#!  The input is an abelian category <A>C</A> with enough injective objects.
#!  The output is the full subcategory of <A>C</A> generated by the injective objects in <A>C</A>.
#! @Arguments C
#! @Returns CapFullSubcategory
DeclareAttribute( "FullSubcategoryOfInjectiveObjects", IsCapCategory );
