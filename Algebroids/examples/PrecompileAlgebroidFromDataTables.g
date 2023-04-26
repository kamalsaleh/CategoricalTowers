#! @BeginChunk PrecompileAlgebroidFromDataTables

#! @Example

#! #@if ValueOption( "no_precompiled_code" ) <> true

LoadPackage( "Algebroids", false );
#! true
LoadPackage( "CompilerForCAP", false );
#! true
ReadPackageOnce( "Algebroids", "gap/CompilerLogic.gi" );
#! true

category_constructor := data_tables -> AlgebroidFromDataTables( ShallowCopy( data_tables ) );;

Q := HomalgFieldOfRationals();;

given_arguments := [ rec( bases_elms_comps := [ [ 1 ], [ 2 ], [ 2, 2 ] ], coefficients_ring := Q, hom_structure_gmors_objs := [ [ [ [ 0, 1, 0 ], [ 0, 0, 1 ], [ 0, 0, 0 ] ] ] ],
  hom_structure_objs_gmors := [ [ [ [ 0, 1, 0 ], [ 0, 0, 1 ], [ 0, 0, 0 ] ] ] ], indices_gmors := [ 2 ], indices_objs := [ 1 ], indices_of_bases_elms := [ [ [ 1, 2, 3 ] ] ], labels_gmors := [ "x" ],
  labels_objs := [ "*" ], nr_bases_elms := 3, nr_gmors := 1, nr_objs := 1, ranges_gmors := [ 1 ], sources_gmors := [ 1 ], colors := true ) ];;

compiled_category_name := "AlgebroidFromDataTablesPrecompiled";;

package_name := "Algebroids";;

CapJitPrecompileCategoryAndCompareResult(
    category_constructor,
    given_arguments,
    package_name,
    compiled_category_name
        : operations := "primitive" );;

A := AlgebroidFromDataTablesPrecompiled( given_arguments[1] );;
funs := A!.precompiled_functions_added;;

#! true

#! #@fi

#! @EndExample

#! @EndChunk
