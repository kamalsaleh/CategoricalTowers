# SPDX-License-Identifier: GPL-2.0-or-later
# SliceCategories: Slice categories
#
# Declarations
#

#! @Chapter Slice categories (eager data structure)

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of an eager slice category.
DeclareCategory( "IsEagerSliceCategory",
        IsSliceCategory );

#! @Description
#!  The &GAP; category of cells in an eager slice category.
DeclareCategory( "IsCellInAnEagerSliceCategory",
        IsCellInASliceCategory );

#! @Description
#!  The &GAP; category of objects in an eager slice category.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsObjectInAnEagerSliceCategory",
        IsObjectInASliceCategory and IsCellInAnEagerSliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsObjectInAnEagerSliceCategory", FilterIntersection( IsObjectInASliceCategory, IsCellInAnEagerSliceCategory ) );

#! @Description
#!  The &GAP; category of morphisms in an eager slice category.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsMorphismInAnEagerSliceCategory",
        IsMorphismInASliceCategory and IsCellInAnEagerSliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsMorphismInAnEagerSliceCategory", FilterIntersection( IsMorphismInASliceCategory, IsCellInAnEagerSliceCategory ) );

#! @Description
#!  The &GAP; category of an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsEagerSliceCategoryOverTensorUnit",
        IsSliceCategoryOverTensorUnit and IsEagerSliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsEagerSliceCategoryOverTensorUnit", FilterIntersection( IsSliceCategoryOverTensorUnit, IsEagerSliceCategory ) );

#! @Description
#!  The &GAP; category of cells in an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsCellInAnEagerSliceCategoryOverTensorUnit",
        IsCellInSliceCategoryOverTensorUnit and IsCellInAnEagerSliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsCellInAnEagerSliceCategoryOverTensorUnit", FilterIntersection( IsCellInSliceCategoryOverTensorUnit, IsCellInAnEagerSliceCategory ) );

#! @Description
#!  The &GAP; category of objects in an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsObjectInAnEagerSliceCategoryOverTensorUnit",
        IsObjectInSliceCategoryOverTensorUnit and IsObjectInAnEagerSliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsObjectInAnEagerSliceCategoryOverTensorUnit", FilterIntersection( IsObjectInSliceCategoryOverTensorUnit, IsObjectInAnEagerSliceCategory ) );

#! @Description
#!  The &GAP; category of morphisms in an eager slice category over the tensor unit.
#= CAP's Julia filter declaration requires FilterIntersection rather than &&.
DeclareCategory( "IsMorphismInAnEagerSliceCategoryOverTensorUnit",
        IsMorphismInSliceCategoryOverTensorUnit and IsMorphismInAnEagerSliceCategory );
# =#
#% G2J:julia-only @DeclareFilter( "IsMorphismInAnEagerSliceCategoryOverTensorUnit", FilterIntersection( IsMorphismInSliceCategoryOverTensorUnit, IsMorphismInAnEagerSliceCategory ) );

####################################
#
#! @Section Constructors
#
####################################

#! @Arguments B
DeclareAttribute( "SliceCategory",
        IsCapCategoryObject );

#! @Arguments M
DeclareAttribute( "SliceCategoryOverTensorUnit",
        IsCapCategory );

#! @Arguments mor
DeclareAttribute( "AsSliceCategoryCell",
        IsCapCategoryMorphism );
