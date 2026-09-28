# SPDX-License-Identifier: GPL-2.0-or-later
# SliceCategories: Slice categories
#
# Declarations
#

#! @Chapter Slice categories (lazy data structure)

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of an eager slice category.
DeclareCategory( "IsLazySliceCategory",
        IsSliceCategory );

#! @Description
#!  The &GAP; category of cells in an eager slice category.
DeclareCategory( "IsCellInALazySliceCategory",
        IsCellInASliceCategory );

#! @Description
#!  The &GAP; category of objects in an eager slice category.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsObjectInALazySliceCategory",
        IsObjectInASliceCategory and IsCellInALazySliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsObjectInALazySliceCategory", FilterIntersection( IsObjectInASliceCategory, IsCellInALazySliceCategory ) );

#! @Description
#!  The &GAP; category of morphisms in an eager slice category.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsMorphismInALazySliceCategory",
        IsMorphismInASliceCategory and IsCellInALazySliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsMorphismInALazySliceCategory", FilterIntersection( IsMorphismInASliceCategory, IsCellInALazySliceCategory ) );

#! @Description
#!  The &GAP; category of an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsLazySliceCategoryOverTensorUnit",
        IsSliceCategoryOverTensorUnit and IsLazySliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsLazySliceCategoryOverTensorUnit", FilterIntersection( IsSliceCategoryOverTensorUnit, IsLazySliceCategory ) );

#! @Description
#!  The &GAP; category of cells in an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsCellInALazySliceCategoryOverTensorUnit",
        IsCellInSliceCategoryOverTensorUnit and IsCellInALazySliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsCellInALazySliceCategoryOverTensorUnit", FilterIntersection( IsCellInSliceCategoryOverTensorUnit, IsCellInALazySliceCategory ) );

#! @Description
#!  The &GAP; category of objects in an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsObjectInALazySliceCategoryOverTensorUnit",
        IsObjectInSliceCategoryOverTensorUnit and IsObjectInALazySliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsObjectInALazySliceCategoryOverTensorUnit", FilterIntersection( IsObjectInSliceCategoryOverTensorUnit, IsObjectInALazySliceCategory ) );

#! @Description
#!  The &GAP; category of morphisms in an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsMorphismInALazySliceCategoryOverTensorUnit",
        IsMorphismInSliceCategoryOverTensorUnit and IsMorphismInALazySliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsMorphismInALazySliceCategoryOverTensorUnit", FilterIntersection( IsMorphismInSliceCategoryOverTensorUnit, IsMorphismInALazySliceCategory ) );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The list of morphisms in the ambient category underlying <A>object</A>.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "UnderlyingMorphismList",
        IsObjectInALazySliceCategory );

####################################
#
#! @Section Constructors
#
####################################

#! @Arguments B
DeclareAttribute( "LazySliceCategory",
        IsCapCategoryObject );

#! @Arguments M
DeclareAttribute( "LazySliceCategoryOverTensorUnit",
        IsCapCategory );

#! @Arguments L
DeclareAttribute( "AsSliceCategoryCell",
        IsList );
