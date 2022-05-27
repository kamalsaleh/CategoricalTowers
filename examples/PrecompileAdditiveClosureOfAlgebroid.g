#! @BeginChunk PrecompileAdditiveClosureOfAlgebroid

#! @Example

LoadPackage( "Algebroids", false );
#! true
LoadPackage( "CompilerForCAP", false );
#! true

QQ := HomalgFieldOfRationals( );;
snake_quiver := RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" );;
A := PathAlgebra( QQ, snake_quiver );;
A_bar := QuotientOfPathAlgebra( A, [ A.abc ] );;

ReadPackage( "Algebroids", "gap/CompilerLogic.gi" );
#! true

# only valid for the construction above
# FIXME: IsInt should be IsRat, but specializations of types are not yet supported by CompilerForCAP
CapJitAddTypeSignature( "CoefficientsOfPaths", [ IsList, IsPathAlgebraElement ], rec( filter := IsList, element_type := rec( filter := IsInt ) ) );
CapJitAddTypeSignature( "CoefficientsOfPaths", [ IsList, IsQuotientOfPathAlgebraElement ], rec( filter := IsList, element_type := rec( filter := IsInt ) ) );

precompile_AdditiveClosureOfAlgebroid :=
  function( Rq, over_Z, path_algebra, ring )
    CapJitPrecompileCategoryAndCompareResult(
        EvalString( ReplacedString( """Rq -> AdditiveClosure( Algebroid(
            Rq, over_Z : FinalizeCategory := true
        ) )""", "over_Z", String( over_Z ) ) ),
        [ Rq ],
        "Algebroids",
        Concatenation(
            "AdditiveClosureOfAlgebroidOfFiniteDimensional",
            path_algebra,
            "OfRightQuiverOver",
            ring,
            "Precompiled"
        ) :
        operations := "primitive"
    ); end;;

precompile_AdditiveClosureOfAlgebroid(
        A, false, "PathAlgebra", "Field" );
precompile_AdditiveClosureOfAlgebroid(
        A_bar, false, "QuotientOfPathAlgebra", "Field" );
precompile_AdditiveClosureOfAlgebroid(
        A, true, "PathAlgebra", "Z" );
precompile_AdditiveClosureOfAlgebroid(
        A_bar, true, "QuotientOfPathAlgebra", "Z" );

AdditiveClosureOfAlgebroidOfFiniteDimensionalPathAlgebraOfRightQuiverOverFieldPrecompiled( A );
#! Additive closure( Algebroid( Q, FreeCategory( RightQuiver(
#! "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) )

#! @EndExample

#! Check that the compiled code is loaded automatically
#! for this, we use the name of the argument of `ZeroObject`:
#! for non-compiled code it is "cat", while for compiled code it is "cat_1"

#! @Example

cat := AdditiveClosure( Algebroid( A, false ) );;
argument_name := NamesLocalVariablesFunction(
                         Last( cat!.added_functions.ZeroObject )[1] )[1];;

( ValueOption( "no_precompiled_code" ) = true and argument_name = "cat" ) or
  ( ValueOption( "no_precompiled_code" ) = fail and argument_name = "cat_1" );
#! true

cat := AdditiveClosure( Algebroid( A_bar, false ) );;
argument_name := NamesLocalVariablesFunction(
                         Last( cat!.added_functions.ZeroObject )[1] )[1];;

( ValueOption( "no_precompiled_code" ) = true and argument_name = "cat" ) or
  ( ValueOption( "no_precompiled_code" ) = fail and argument_name = "cat_1" );
#! true

cat := AdditiveClosure( Algebroid( A, true ) );;
argument_name := NamesLocalVariablesFunction(
                         Last( cat!.added_functions.ZeroObject )[1] )[1];;

( ValueOption( "no_precompiled_code" ) = true and argument_name = "cat" ) or
  ( ValueOption( "no_precompiled_code" ) = fail and argument_name = "cat_1" );
#! true

cat := AdditiveClosure( Algebroid( A_bar, true ) );;
argument_name := NamesLocalVariablesFunction(
                         Last( cat!.added_functions.ZeroObject )[1] )[1];;

( ValueOption( "no_precompiled_code" ) = true and argument_name = "cat" ) or
  ( ValueOption( "no_precompiled_code" ) = fail and argument_name = "cat_1" );
#! true

#! @EndExample

#! @EndChunk
