# SPDX-License-Identifier: GPL-2.0-or-later
# CategoryConstructor: Construct categories out of given ones
#
# Implementations
#

InstallValue( CATEGORY_CONSTRUCTOR_METHOD_NAME_RECORD, rec(

PreInverse := rec(
  filter_list := [ "category", "morphism" ],
  io_type := [ [ "alpha" ], [ "alpha_range", "alpha_source" ] ],
  return_type := "morphism",
  dual_operation := "PostInverse",
  is_merely_set_theoretic := true
),

PostInverse := rec(
  filter_list := [ "category", "morphism" ],
  io_type := [ [ "alpha" ], [ "alpha_range", "alpha_source" ] ],
  return_type := "morphism",
  dual_operation := "PreInverse",
  is_merely_set_theoretic := true
),

IsWeakTerminal := rec(
  filter_list := [ "category", "object" ],
  well_defined_todo := false,
  return_type := "bool",
  dual_operation := "IsWeakInitial",
  property_of := "object" ),

IsWeakInitial := rec(
  filter_list := [ "category", "object" ],
  well_defined_todo := false,
  return_type := "bool",
  dual_operation := "IsWeakTerminal",
  property_of := "object" ),

MorphismOntoSumOfImagesOfAllMorphisms := rec(
  filter_list := [ "category", "object", "object" ],
  io_type := [ [ "a", "b" ], [ "d", "b" ] ],
  return_type := "morphism",
  is_merely_set_theoretic := true
),

EmbeddingOfSumOfImagesOfAllMorphisms := rec(
  filter_list := [ "category", "object", "object" ],
  io_type := [ [ "a", "b" ], [ "s", "b" ] ],
  return_type := "morphism",
  is_merely_set_theoretic := true
),

SumOfImagesOfAllMorphisms := rec(
  filter_list := [ "category", "object", "object" ],
  return_type := "object",
  is_merely_set_theoretic := true
),

MereExistenceOfUniqueSolutionOfLinearSystemInAbCategory := rec(
  filter_list := [ "category", IsList, IsList, "list_of_morphisms" ],
  return_type := "bool"
),

MereExistenceOfUniqueSolutionOfHomogeneousLinearSystemInAbCategory := rec(
  filter_list := [ "category", IsList, IsList ],
  return_type := "bool"
),

BasisOfSolutionsOfHomogeneousLinearSystemInLinearCategory := rec(
  filter_list := [ "category", IsList, IsList ],
  return_type := IsList
),

BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory := rec(
  filter_list := [ "category", IsList, IsList, IsList, IsList ],
  return_type := IsList
),

) );

CAP_INTERNAL_ENHANCE_NAME_RECORD( CATEGORY_CONSTRUCTOR_METHOD_NAME_RECORD );

CAP_INTERNAL_GENERATE_DOCUMENTATION_FROM_METHOD_NAME_RECORD(
    CATEGORY_CONSTRUCTOR_METHOD_NAME_RECORD,
    "CategoryConstructor",
    "Tools.autogen.gd",
    "Futher CAP operations",
    "Add-methods"
);

CAP_INTERNAL_INSTALL_ADDS_FROM_RECORD( CATEGORY_CONSTRUCTOR_METHOD_NAME_RECORD );

####################################
#
# methods for operations:
#
####################################


##
InstallOtherMethod( \*,
        "for two CAP morphism",
        [ IsCapCategoryMorphism, IsCapCategoryMorphism ],

  function( mor1, mor2 )
    
    return PreCompose( mor1, mor2 );
    
end );

##
InstallOtherMethod( OneMutable,
        "for a CAP morphism",
        [ IsCapCategoryMorphism ],
        
  function( mor )
    
    if not IsEndomorphism( mor ) then
        return fail;
    fi;
    
    return IdentityMorphism( Source( mor ) );
    
end );

##
InstallOtherMethod( POW,
        "for a CAP morphism and an integer",
        [ IsCapCategoryMorphism, IsInt ],

  function( mor, power )
    
    if power = 0 then
        return OneMutable( mor );
    fi;
    
    if power < 0 then
        mor := Inverse( mor );
        if mor = fail then
            return mor;
        fi;
        power := -power;
    fi;
    
    if power > 1 then
        if not IsEndomorphism( mor ) then
            return fail;
        fi;
    fi;
    
    return Product( ListWithIdenticalEntries( power, mor ) );
    
end );

##
InstallMethod( BasisOfSolutionsOfHomogeneousLinearSystemInLinearCategory,
               [ IsList, IsList ],
               
  function( left_coeffs, right_coeffs )
    
    return BasisOfSolutionsOfHomogeneousLinearSystemInLinearCategory( CapCategory( right_coeffs[1, 1] ), left_coeffs, right_coeffs );
    
end );

##
InstallMethod( BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory,
               [ IsList, IsList, IsList, IsList ],
               
  function( alpha, beta, gamma, delta )
    
    return BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory(
                    CapCategory( delta[1, 1] ), alpha, beta, gamma, delta
                  );
    
end );

##
InstallMethod( BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory,
               [ IsList, IsList ],
               
  function( alpha, delta )
    local cat, beta, gamma, i;
    
    cat := CapCategory( alpha[1][1] );
    
    if not CanCompute( cat, "BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory" ) then
      TryNextMethod( );
    fi;
    
    beta := [ ];
    
    gamma := [ ];
    
    for i in [ 1 .. Length( alpha ) ] do
      
      Add( beta, List( [ 1 .. Length( delta[i] ) ],
        function( j )
           local alpha_ij, delta_ij;
           
           alpha_ij := alpha[i][j];
           delta_ij := delta[i][j];
           
          if IsEndomorphism( delta_ij ) and not IsIdenticalToZeroMorphism( alpha_ij ) then
              return IdentityMorphism( Source( delta_ij ) );
          fi;
          
          return ZeroMorphism( Source( delta_ij ), Range( delta_ij ) );
          
        end ) );
        
      Add( gamma, List( [ 1 .. Length( alpha[i] ) ],
        function( j )
          local alpha_ij, delta_ij;
          
          alpha_ij := alpha[i][j];
          delta_ij := delta[i][j];
          
          if IsEndomorphism( alpha_ij ) and not IsIdenticalToZeroMorphism( delta_ij ) then
              return IdentityMorphism( Source( alpha_ij ) );
          fi;
          
          return ZeroMorphism( Source( alpha_ij ), Range( alpha_ij ) );
          
        end ) );
        
    od;
    
    return BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory( alpha, beta, gamma, delta );
    
end );

##
InstallMethod( MereExistenceOfUniqueSolutionOfHomogeneousLinearSystemInAbCategory,
               [ IsList, IsList ],
               
  function( left_coeffs, right_coeffs )
    
    return MereExistenceOfUniqueSolutionOfLinearSystemInAbCategory( CapCategory( right_coeffs[1,1] ), left_coeffs, right_coeffs );
    
end );

####################################
#
# categorical methods derivations:
#
####################################

##
AddDerivationToCAP( PreInverse,
        [ [ IdentityMorphism, 1 ],
          [ Lift, 1 ],
          ],
        
  function( cat, alpha )
    
    return Lift( cat, IdentityMorphism( cat, Range( alpha ) ), alpha );
    
end : Description := "PreInverse using IdentityMorphism of Range and Lift" );

##
AddDerivationToCAP( PostInverse,
        [ [ IdentityMorphism, 1 ],
          [ Colift, 1 ],
          ],
        
  function( cat, alpha )
    
    return Colift( cat, alpha, IdentityMorphism( cat, Source( alpha ) ) );
    
end : Description := "PostInverse using IdentityMorphism of Source and Colift" );

##
AddDerivationToCAP( MorphismOntoSumOfImagesOfAllMorphisms,
        [ [ BasisOfExternalHom, 1 ],
          [ UniversalMorphismFromZeroObject, 1 ],
          [ UniversalMorphismFromDirectSum, 1 ]
          ],
        
  function( cat, a, b )
    local hom;
    
    hom := BasisOfExternalHom( cat, a, b );
    
    if hom = [ ] then
        return UniversalMorphismFromZeroObject( cat, b );
    fi;
    
    return UniversalMorphismFromDirectSum( cat, hom );
    
end : Description := "MorphismOntoSumOfImagesOfAllMorphisms using BasisOfExternalHom and UniversalMorphismFromDirectSum",
      CategoryFilter := IsAbelianCategory );

##
AddDerivationToCAP( EmbeddingOfSumOfImagesOfAllMorphisms,
        [ [ MorphismOntoSumOfImagesOfAllMorphisms, 1 ],
          [ ImageEmbedding, 1 ],
          ],
        
  function( cat, a, b )
    
    return ImageEmbedding( cat, MorphismOntoSumOfImagesOfAllMorphisms( cat, a, b ) );
    
end : Description := "EmbeddingOfSumOfImagesOfAllMorphisms using MorphismOntoSumOfImagesOfAllMorphisms and ImageEmbedding",
      CategoryFilter := IsAbelianCategory );

##
AddDerivationToCAP( SumOfImagesOfAllMorphisms,
        [ [ EmbeddingOfSumOfImagesOfAllMorphisms, 1 ],
          ],
        
  function( cat, a, b )
    
    return Source( EmbeddingOfSumOfImagesOfAllMorphisms( cat, a, b ) );
    
end : Description := "SumOfImagesOfAllMorphisms as Source of EmbeddingOfSumOfImagesOfAllMorphisms",
      CategoryFilter := IsAbelianCategory );

##
AddDerivationToCAP( BasisOfSolutionsOfHomogeneousLinearSystemInLinearCategory,
                    [ [ InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure, 1 ],
                      [ HomomorphismStructureOnMorphismsWithGivenObjects, 1 ],
                      [ HomomorphismStructureOnObjects, 1 ],
                      [ InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism, 1 ] ],
  function( cat, left_coefficients, right_coefficients )
    local m, n, list, H, B, summands;
    
    m := Size( left_coefficients );
    
    n := Size( left_coefficients[1] );
    
    list :=
      List( [ 1 .. n ],
      j -> List( [ 1 .. m ], i -> HomomorphismStructureOnMorphisms( cat, left_coefficients[i][j], right_coefficients[i][j] ) )
    );
    
    H := MorphismBetweenDirectSums( list );
    
    H := KernelEmbedding( RangeCategoryOfHomomorphismStructure( cat ), H );
    
    B := BasisOfExternalHom( RangeCategoryOfHomomorphismStructure( cat ), DistinguishedObjectOfHomomorphismStructure( cat ), Source( H ) );
    
    B := List( B, m -> PreCompose( RangeCategoryOfHomomorphismStructure( cat ), m, H ) );
    
    summands := List( [ 1 .. n ],
                  j -> HomomorphismStructureOnObjects( cat,
                          Range( left_coefficients[1][j] ),
                          Source( right_coefficients[1][j] )
                        )
                    );
                     
    return
      List( B, m ->
        List( [ 1 .. n ], j ->
          InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
            Range( left_coefficients[1][j] ),
            Source( right_coefficients[1][j] ),
            PreCompose( RangeCategoryOfHomomorphismStructure( cat ), m, ProjectionInFactorOfDirectSum( RangeCategoryOfHomomorphismStructure( cat ), summands, j ) )
          )
        )
      );
      
  end :
  ConditionsListComplete := true,
  CategoryFilter := function( cat )
    local B, conditions;
    
    if HasIsLinearCategoryOverCommutativeRing( cat ) and
        IsLinearCategoryOverCommutativeRing( cat ) and
          HasRangeCategoryOfHomomorphismStructure( cat ) then
        
        B := RangeCategoryOfHomomorphismStructure( cat );
        
        conditions := [
          "UniversalMorphismIntoDirectSum",
          "MorphismBetweenDirectSumsWithGivenDirectSums",
          "PreCompose",
          "KernelEmbedding",
          "BasisOfExternalHom"
        ];
        
        if ForAll( conditions, c -> CanCompute( B, c ) ) then
            
            return true;
            
        fi;
        
    fi;
    
    return false;
    
  end,
  Description := "BasisOfSolutionsOfHomogeneousLinearSystemInLinearCategory using the homomorphism structure"
);

##
AddDerivationToCAP( BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory,
                    [ [ InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure, 1 ],
                      [ HomomorphismStructureOnMorphismsWithGivenObjects, 1 ],
                      [ HomomorphismStructureOnObjects, 1 ],
                      [ InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism, 1 ],
                      [ DistinguishedObjectOfHomomorphismStructure, 1 ]
                    ],
  function( cat, alpha, beta, gamma, delta )
    local m, n, list_1, H_1, list_2, H_2, H, B, summands;
    
    m := Size( alpha );
    
    n := Size( alpha[1] );
    
    list_1 :=
      List( [ 1 .. n ],
      j -> List( [ 1 .. m ], i -> HomomorphismStructureOnMorphisms( cat, alpha[i][j], beta[i][j] ) )
    );
    
    H_1 := MorphismBetweenDirectSums( list_1 );
    
    list_2 :=
      List( [ 1 .. n ],
      j -> List( [ 1 .. m ], i -> HomomorphismStructureOnMorphisms( cat, gamma[i][j], delta[i][j] ) )
    );
    
    H_2 := MorphismBetweenDirectSums( list_2 );
    
    H := KernelEmbedding( RangeCategoryOfHomomorphismStructure( cat ), H_1 - H_2 );
    
    B := BasisOfExternalHom( RangeCategoryOfHomomorphismStructure( cat ), DistinguishedObjectOfHomomorphismStructure( cat ), Source( H ) );
    
    B := List( B, m -> PreCompose( RangeCategoryOfHomomorphismStructure( cat ), m, H ) );
    
    summands := List( [ 1 .. n ],
                  j -> HomomorphismStructureOnObjects( cat,
                          Range( alpha[1][j] ),
                          Source( beta[1][j] )
                        )
                    );
                    
    return
      List( B, m ->
        List( [ 1 .. n ], j ->
          InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
            Range( alpha[1][j] ),
            Source( beta[1][j] ),
            PreCompose( RangeCategoryOfHomomorphismStructure( cat ), m, ProjectionInFactorOfDirectSum( RangeCategoryOfHomomorphismStructure( cat ), summands, j ) )
          )
        )
      );
      
  end :
  ConditionsListComplete := true,
  CategoryFilter := function( cat )
    local B, conditions;
    
    if HasIsLinearCategoryOverCommutativeRing( cat ) and
        IsLinearCategoryOverCommutativeRing( cat ) and
          HasRangeCategoryOfHomomorphismStructure( cat ) then
        
        B := RangeCategoryOfHomomorphismStructure( cat );
        
        conditions := [
          "UniversalMorphismIntoDirectSum",
          "MorphismBetweenDirectSumsWithGivenDirectSums",
          "PreCompose",
          "KernelEmbedding",
          "BasisOfExternalHom"
        ];
        
        if ForAll( conditions, c -> CanCompute( B, c ) ) then
            
            return true;
            
        fi;
        
    fi;
    
    return false;
    
  end,
  Description := "BasisOfSolutionsOfHomogeneousDoubleLinearSystemInLinearCategory using the homomorphism structure"
);

##
AddDerivationToCAP( MereExistenceOfUniqueSolutionOfLinearSystemInAbCategory,
                    [ [ InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure, 1 ],
                      [ HomomorphismStructureOnMorphismsWithGivenObjects, 1 ],
                      [ HomomorphismStructureOnObjects, 1 ],
                      [ InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism, 1 ] ],
  function( cat, left_coefficients, right_coefficients, right_side )
    local m, n, nu, list, H;
    
    m := Size( left_coefficients );
    
    n := Size( left_coefficients[1] );
    
    ## create lift diagram
    
    nu :=
      UniversalMorphismIntoDirectSum( RangeCategoryOfHomomorphismStructure( cat ),
        List( [ 1 .. m ],
        i -> InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( cat, right_side[i] ) )
    );
    
    list :=
      List( [ 1 .. n ],
      j -> List( [ 1 .. m ], i -> HomomorphismStructureOnMorphisms( cat, left_coefficients[i][j], right_coefficients[i][j] ) )
    );
    
    H := MorphismBetweenDirectSums( list );
    
    return IsLiftable( RangeCategoryOfHomomorphismStructure( cat ), nu, H ) and IsMonomorphism( RangeCategoryOfHomomorphismStructure( cat ), H );
    
  end :
  ConditionsListComplete := true,
  CategoryFilter := function( cat )
    local B, conditions;
    
    if HasIsAbCategory( cat ) and IsAbCategory( cat ) and HasRangeCategoryOfHomomorphismStructure( cat ) then
        
        B := RangeCategoryOfHomomorphismStructure( cat );
        
        conditions := [
          "UniversalMorphismIntoDirectSum",
          "MorphismBetweenDirectSumsWithGivenDirectSums",
          "IsLiftable",
          "IsMonomorphism"
        ];
        
        if ForAll( conditions, c -> CanCompute( B, c ) ) then
            
            return true;
            
        fi;
        
    fi;
    
    return false;
    
  end,
  Description := "MereExistenceOfUniqueSolutionOfLinearSystemInAbCategory using the homomorphism structure"
);

##
AddDerivationToCAP( MereExistenceOfUniqueSolutionOfHomogeneousLinearSystemInAbCategory,
                    [ [ HomomorphismStructureOnMorphismsWithGivenObjects, 1 ] ],
  function( cat, left_coefficients, right_coefficients )
    local m, n, list, H;
    
    m := Size( left_coefficients );
    
    n := Size( left_coefficients[1] );
    
    list :=
      List( [ 1 .. n ],
      j -> List( [ 1 .. m ], i -> HomomorphismStructureOnMorphisms( cat, left_coefficients[i][j], right_coefficients[i][j] ) )
    );
    
    H := MorphismBetweenDirectSums( list );
    
    return IsMonomorphism( RangeCategoryOfHomomorphismStructure( cat ), H );
    
  end :
  ConditionsListComplete := true,
  CategoryFilter := function( cat )
    local B, conditions;
    
    if HasIsAbCategory( cat ) and IsAbCategory( cat ) and HasRangeCategoryOfHomomorphismStructure( cat ) then
        
        B := RangeCategoryOfHomomorphismStructure( cat );
        
        conditions := [
          "MorphismBetweenDirectSumsWithGivenDirectSums",
          "IsMonomorphism"
        ];
        
        if ForAll( conditions, c -> CanCompute( B, c ) ) then
            
            return true;
            
        fi;
        
    fi;
    
    return false;
    
  end,
  Description := "MereExistenceOfUniqueSolutionOfHomogeneousLinearSystemInAbCategory using the homomorphism structure"
);
