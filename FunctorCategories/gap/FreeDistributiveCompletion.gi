# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#

##
InstallMethodWithCache( FreeDistributiveCompletion,
        "for a CAP category",
        [ IsCapCategory, IsCapCategory ],
        
  function( fp_category, range_category_of_hom_structure )
    local name, category_filter, category_object_filter, category_morphism_filter,
          finite_completion, finite_cocompletion,
          free_distributive_completion;
    
    ##
    name := Concatenation( "FreeDistributiveCompletion( ", Name( fp_category ), " )" );
    
    ##
    category_filter := IsFreeDistributiveCompletion;
    category_object_filter := IsObjectInFreeDistributiveCompletion;
    category_morphism_filter := IsMorphismInFreeDistributiveCompletion;
    
    ## building the categorical tower:
    
    finite_completion := FiniteCompletion( fp_category, range_category_of_hom_structure
                            #= comment for julia (Temporarily)
                            : overhead := false
                            # =#
                            );
    
    finite_cocompletion := FiniteCocompletion( finite_completion, range_category_of_hom_structure
                            #= comment for julia (Temporarily)
                            : overhead := false
                            # =#
                            );
    
    ##
    free_distributive_completion :=
      WrapperCategory( finite_cocompletion,
              rec( name := name,
                   category_filter := category_filter,
                   category_object_filter := category_object_filter,
                   category_morphism_filter := category_morphism_filter,
                   only_primitive_operations := true )
              );
    
    SetUnderlyingCategory( free_distributive_completion, fp_category );

    ## Required for Julia, which does not support all forms of InstallTrueMethod with conjunctions.
    ## FiniteStrictCoproductCompletion.gi sets IsDistributiveCategory when its source is Cartesian; Julia does not propagate it through the wrapper tower.
    if HasIsCartesianCategory( finite_completion ) and IsCartesianCategory( finite_completion ) then
      SetIsDistributiveCategory( free_distributive_completion, true );
    fi;

    ## Lattice.gi: InstallTrueMethod( IsCartesianProset, IsThinCategory and IsCartesianCategory );
    if HasIsThinCategory( free_distributive_completion ) and IsThinCategory( free_distributive_completion ) and
       HasIsCartesianCategory( free_distributive_completion ) and IsCartesianCategory( free_distributive_completion ) then
      SetIsCartesianProset( free_distributive_completion, true );
    fi;

    ## Lattice.gi: InstallTrueMethod( IsCocartesianProset, IsThinCategory and IsCocartesianCategory );
    if HasIsThinCategory( free_distributive_completion ) and IsThinCategory( free_distributive_completion ) and
       HasIsCocartesianCategory( free_distributive_completion ) and IsCocartesianCategory( free_distributive_completion ) then
      SetIsCocartesianProset( free_distributive_completion, true );
    fi;

    ## Lattice.gi: InstallTrueMethod( IsBicartesianProset, IsCartesianProset and IsCocartesianProset );
    if HasIsCartesianProset( free_distributive_completion ) and IsCartesianProset( free_distributive_completion ) and
       HasIsCocartesianProset( free_distributive_completion ) and IsCocartesianProset( free_distributive_completion ) then
      SetIsBicartesianProset( free_distributive_completion, true );
    fi;

    ## Lattice.gi: InstallTrueMethod( IsDistributiveBicartesianProset, IsBicartesianProset and IsDistributiveCategory );
    if HasIsBicartesianProset( free_distributive_completion ) and IsBicartesianProset( free_distributive_completion ) and
       HasIsDistributiveCategory( free_distributive_completion ) and IsDistributiveCategory( free_distributive_completion ) then
      SetIsDistributiveBicartesianProset( free_distributive_completion, true );
    fi;

    ## Lattice.gi: InstallTrueMethod( IsBiHeytingAlgebroid, IsDistributiveBicartesianProset and IsEquivalentToFiniteCategory );
    if HasIsDistributiveBicartesianProset( free_distributive_completion ) and IsDistributiveBicartesianProset( free_distributive_completion ) and
       HasIsEquivalentToFiniteCategory( free_distributive_completion ) and IsEquivalentToFiniteCategory( free_distributive_completion ) then
      SetIsBiHeytingAlgebroid( free_distributive_completion, true );
    fi;

    ## BooleanAlgebra.gi: InstallTrueMethod( IsBiHeytingAlgebra, IsBiHeytingAlgebroid and IsSkeletalCategory );
    if HasIsBiHeytingAlgebroid( free_distributive_completion ) and IsBiHeytingAlgebroid( free_distributive_completion ) and
       HasIsSkeletalCategory( free_distributive_completion ) and IsSkeletalCategory( free_distributive_completion ) then
      SetIsBiHeytingAlgebra( free_distributive_completion, true );
    fi;

    ## HeytingAlgebra.gi: InstallTrueMethod( IsHeytingAlgebra, IsHeytingAlgebroid and IsSkeletalCategory );
    if HasIsHeytingAlgebroid( free_distributive_completion ) and IsHeytingAlgebroid( free_distributive_completion ) and
       HasIsSkeletalCategory( free_distributive_completion ) and IsSkeletalCategory( free_distributive_completion ) then
      SetIsHeytingAlgebra( free_distributive_completion, true );
    fi;

    ## CoHeytingAlgebra.gi: InstallTrueMethod( IsCoHeytingAlgebra, IsCoHeytingAlgebroid and IsSkeletalCategory );
    if HasIsCoHeytingAlgebroid( free_distributive_completion ) and IsCoHeytingAlgebroid( free_distributive_completion ) and
       HasIsSkeletalCategory( free_distributive_completion ) and IsSkeletalCategory( free_distributive_completion ) then
      SetIsCoHeytingAlgebra( free_distributive_completion, true );
    fi;

    ## BicartesianCategories.gi: InstallTrueMethod( IsFiniteBicompleteCategory, IsFiniteCompleteCategory and IsFiniteCocompleteCategory );
    if HasIsFiniteCompleteCategory( free_distributive_completion ) and IsFiniteCompleteCategory( free_distributive_completion ) and
       HasIsFiniteCocompleteCategory( free_distributive_completion ) and IsFiniteCocompleteCategory( free_distributive_completion ) then
      SetIsFiniteBicompleteCategory( free_distributive_completion, true );
    fi;
    
    if HasIsInitialCategory( fp_category ) and IsInitialCategory( fp_category ) then
        Assert( 0, [ ] = MissingOperationsForConstructivenessOfCategory( free_distributive_completion, "IsEquippedWithHomomorphismStructure" ) );
    fi;
    
    return free_distributive_completion;
    
end );

##
InstallMethod( FreeDistributiveCompletion,
        "for a CAP category",
        [ IsCapCategory ],
        
  function( fp_category )
    
    Assert( 0, HasRangeCategoryOfHomomorphismStructure( fp_category ) );
    
    return FreeDistributiveCompletion( fp_category, RangeCategoryOfHomomorphismStructure( fp_category ) );
    
end );

##
InstallMethod( EmbeddingOfUnderlyingCategory,
        "for a free distributive completion category",
        [ IsFreeDistributiveCompletion ],
        
  function( free_distributive_completion )
    local D, Y;
    
    D := ModelingCategory( free_distributive_completion );
    
    Y := PreCompose(
                 EmbeddingOfUnderlyingCategory( UnderlyingCategory( D ) ),
                 EmbeddingOfUnderlyingCategory( D ) );
    
    return PreCompose( Y, WrappingFunctor( free_distributive_completion ) );
    
end );

##
InstallOtherMethod( \/,
        "for a string and a free distributive completion category",
        [ IsString, IsFreeDistributiveCompletion ],
        
  function( name, free_distributive_completion )
    local F, Y, Yc;
    
    F := UnderlyingCategory( free_distributive_completion );
    
    Y := EmbeddingOfUnderlyingCategory( free_distributive_completion );
    
    Yc := CallFuncListAtRuntime( ApplyFunctor, [ Y,  name / F  ] );
    
    if IsObjectInFreeDistributiveCompletion( Yc ) then
        
        SetIsProjective( Yc, true );
        
    elif IsMorphismInFreeDistributiveCompletion( Yc ) then
        
        #if CanCompute( free_distributive_completion, "IsMonomorphism" ) then
        #    IsMonomorphism( Yc );
        #fi;
        
        #if CanCompute( free_distributive_completion, "IsSplitMonomorphism" ) then
        #    IsSplitMonomorphism( Yc );
        #fi;
        
        #if CanCompute( free_distributive_completion, "IsEpimorphism" ) then
        #    IsEpimorphism( Yc );
        #fi;
        
        #if CanCompute( free_distributive_completion, "IsSplitEpimorphism" ) then
        #    IsSplitEpimorphism( Yc );
        #fi;
        
        ## IsIsomorphism = IsSplitMonomorphism and IsSplitEpimorphism
        ## we add this here in case the logic is deactivated
        #if CanCompute( free_distributive_completion, "IsIsomorphism" ) then
        #    IsIsomorphism( Yc );
        #fi;
        
    fi;
    
    return Yc;
    
end );

##
InstallOtherMethod( \/,
        "for a string and an object in a free distributive completion category",
        [ IsString, IsObjectInFreeDistributiveCompletion ],
        
  function( name, object )
    
    return UnderlyingCell( object ).( name );
    
end );

##
InstallOtherMethod( \/,
        "for a string and a morphism in a free distributive completion category",
        [ IsString, IsMorphismInFreeDistributiveCompletion ],
        
  function( name, morphism )
    
    return UnderlyingCell( morphism ).( name );
    
end );

#=
INSTALL_DOT_METHOD( IsFreeDistributiveCompletion );
INSTALL_DOT_METHOD( IsObjectInFreeDistributiveCompletion );
INSTALL_DOT_METHOD( IsMorphismInFreeDistributiveCompletion );
# =#

##
InstallMethodForCompilerForCAP( SetOfObjects,
        "for a free distributive completion category",
        [ IsFreeDistributiveCompletion ],
        
  function( free_distributive_completion )
    
    return SetOfObjectsOfCategory( free_distributive_completion );
    
end );

##
InstallMethodForCompilerForCAP( SetOfGeneratingMorphisms,
        "for a free distributive completion category",
        [ IsFreeDistributiveCompletion ],
        
  function( free_distributive_completion )
    
    return SetOfGeneratingMorphismsOfCategory( free_distributive_completion );
    
end );
