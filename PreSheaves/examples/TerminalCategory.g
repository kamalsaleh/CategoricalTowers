#! @Chunk TerminalCategory

#! @Example
LoadPackage( "PreSheaves" );
#! true
LoadPackage( "Toposes", ">= 2023.11-02", fail );
#! true
T := PreSheaves( InitialCategory( ) );
#! PreSheaves( InitialCategory( ), InitialCategory( ) )
IsTerminalCategory( T );
#! true
Display( T );
#! A CAP category with name PreSheaves( InitialCategory( ), InitialCategory( ) ):
#! 
#! 93 primitive operations were used to derive 515 operations for this category
#! which algorithmically
#! * IsCategoryWithDecidableColifts
#! * IsCategoryWithDecidableLifts
#! * IsEquippedWithHomomorphismStructure
#! * IsLinearCategoryOverCommutativeRing
#! * IsBicartesianCoclosedCategory
#! * IsAbelianCategoryWithEnoughInjectives
#! * IsAbelianCategoryWithEnoughProjectives
#! * IsElementaryTopos
#! * IsRigidSymmetricClosedMonoidalCategory
#! * IsRigidSymmetricCoclosedMonoidalCategory
#! and furthermore mathematically
#! * IsLocallyOfFiniteInjectiveDimension
#! * IsLocallyOfFiniteProjectiveDimension
#! * IsSkeletalCategory
#! * IsStrictCartesianCategory
#! * IsStrictCocartesianCategory
#! * IsStrictMonoidalCategory
#! * IsTerminalCategory
i := InitialObject( T );
#! <An object in PreSheaves( InitialCategory( ), InitialCategory( ) )>
t := TerminalObject( T );
#! <An object in PreSheaves( InitialCategory( ), InitialCategory( ) )>
z := ZeroObject( T );
#! <A zero object in PreSheaves( InitialCategory( ), InitialCategory( ) )>
Display( i );
#! An object in PreSheaves( InitialCategory( ), InitialCategory( ) ).
Display( t );
#! An object in PreSheaves( InitialCategory( ), InitialCategory( ) ).
Display( z );
#! A zero object in PreSheaves( InitialCategory( ), InitialCategory( ) ).
IsIdenticalObj( i, z );
#! false
IsIdenticalObj( t, z );
#! false
IsEqualForObjects( i, z );
#! true
IsEqualForObjects( t, z );
#! true
IsWellDefined( z );
#! true
id_z := IdentityMorphism( z );
#! <A zero, identity morphism in
#!  PreSheaves( InitialCategory( ), InitialCategory( ) )>
fn_z := ZeroObjectFunctorial( T );
#! <A zero, isomorphism in PreSheaves( InitialCategory( ), InitialCategory( ) )>
IsWellDefined( fn_z );
#! true
IsEqualForMorphisms( id_z, fn_z );
#! true
IsCongruentForMorphisms( id_z, fn_z );
#! true
#! @EndExample
