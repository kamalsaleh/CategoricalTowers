# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_FinBouquetsPrecompiled", function ( cat )
    
    ##
    AddInitialObject( cat,
        
########
function ( cat_1 )
    local deduped_1_1;
    deduped_1_1 := BigInt( 0 );
    return CreateCapCategoryObjectWithAttributes( cat_1, DefiningTripleOfBouquetEnrichedOverSkeletalFinSets, NTuple( 3, deduped_1_1, deduped_1_1, [  ] ) );
end
########
        
    , 100 );
    
    ##
    AddCoproduct( cat,
        
########
function ( cat_1, objects_1 )
    local deduped_3_1, deduped_4_1;
    deduped_4_1 := List( objects_1, function ( x_2 )
            return DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( x_2 )[2];
        end );
    deduped_3_1 := List( objects_1, function ( x_2 )
            return DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( x_2 )[1];
        end );
    return CreateCapCategoryObjectWithAttributes( cat_1, DefiningTripleOfBouquetEnrichedOverSkeletalFinSets, NTuple( 3, Sum( deduped_3_1 ), Sum( deduped_4_1 ), Concatenation( List( [ 1 .. Length( objects_1 ) ], function ( i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2;
                  deduped_3_2 := Sum( deduped_3_1{[ 1 .. i_2 - 1 ]} );
                  hoisted_2_2 := [ deduped_3_2 .. deduped_3_2 + deduped_3_1[i_2] - 1 ];
                  hoisted_1_2 := CAP_JIT_INCOMPLETE_LOGIC( DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( CAP_JIT_INCOMPLETE_LOGIC( objects_1[i_2] ) )[3] );
                  return List( [ 0 .. deduped_4_1[i_2] - 1 ], function ( i_3 )
                          return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      end );
              end ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddInjectionOfCofactorOfCoproductWithGivenCoproduct( cat,
        
########
function ( cat_1, objects_1, k_1, P_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1, deduped_5_1;
    deduped_5_1 := [ 1 .. k_1 - 1 ];
    deduped_4_1 := List( objects_1, function ( x_2 )
            return DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( x_2 )[2];
        end );
    deduped_3_1 := List( objects_1, function ( x_2 )
            return DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( x_2 )[1];
        end );
    deduped_2_1 := Sum( deduped_4_1{deduped_5_1} );
    deduped_1_1 := Sum( deduped_3_1{deduped_5_1} );
    return CreateCapCategoryMorphismWithAttributes( cat_1, objects_1[k_1], P_1, DefiningPairOfBouquetMorphismEnrichedOverSkeletalFinSets, NTuple( 2, [ deduped_1_1 .. deduped_1_1 + deduped_3_1[k_1] - 1 ], [ deduped_2_1 .. deduped_2_1 + deduped_4_1[k_1] - 1 ] ) );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismFromCoproductWithGivenCoproduct( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, DefiningPairOfBouquetMorphismEnrichedOverSkeletalFinSets, NTuple( 2, Concatenation( List( tau_1, function ( x_2 )
                  return DefiningPairOfBouquetMorphismEnrichedOverSkeletalFinSets( x_2 )[1];
              end ) ), Concatenation( List( tau_1, function ( x_2 )
                  return DefiningPairOfBouquetMorphismEnrichedOverSkeletalFinSets( x_2 )[2];
              end ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( RangeCategoryOfHomomorphismStructure( cat_1 ), Length, BigInt( 1 ) );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, hoisted_9_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, deduped_15_1, hoisted_17_1, hoisted_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1;
    deduped_32_1 := DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( arg3_1 );
    deduped_31_1 := DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( arg2_1 );
    deduped_30_1 := deduped_32_1[3];
    deduped_29_1 := deduped_31_1[2];
    deduped_28_1 := deduped_31_1[1];
    deduped_27_1 := Source( ModelingCategory( ModelingCategory( cat_1 ) ) );
    deduped_26_1 := [ 0 .. deduped_29_1 - 1 ];
    deduped_25_1 := CreateCapCategoryObjectWithAttributes( deduped_27_1, IndexOfObject, 1 );
    deduped_24_1 := CreateCapCategoryObjectWithAttributes( deduped_27_1, IndexOfObject, 0 );
    deduped_23_1 := ListWithIdenticalEntries( deduped_29_1, deduped_25_1 );
    deduped_22_1 := ListWithIdenticalEntries( deduped_28_1, deduped_24_1 );
    deduped_2_1 := [ deduped_32_1[1], deduped_32_1[2] ];
    deduped_1_1 := [ deduped_24_1, deduped_25_1 ];
    deduped_21_1 := Concatenation( List( deduped_22_1, function ( objB_2 )
              return deduped_2_1[SafePosition( deduped_1_1, objB_2 )];
          end ), List( deduped_23_1, function ( objB_2 )
              return deduped_2_1[SafePosition( deduped_1_1, objB_2 )];
          end ) );
    deduped_20_1 := [ 0 .. Product( deduped_21_1 ) - 1 ];
    deduped_8_1 := [ 0, 1, 2 ];
    deduped_7_1 := [ 0, 1, 1 ];
    deduped_6_1 := [ 0, 0, 1 ];
    deduped_5_1 := [ 0, 2 ];
    hoisted_17_1 := List( ListWithIdenticalEntries( deduped_29_1, CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_24_1, deduped_25_1, IndexOfMorphism, 1 ) ), function ( morB_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := Source( morB_2 );
            deduped_2_2 := IndexOfObject( deduped_3_2 );
            deduped_1_2 := 1 + deduped_5_1[(1 + deduped_2_2)];
            if IdFunc( function (  )
                        if deduped_2_2 = deduped_6_1[deduped_1_2] and IndexOfObject( Range( morB_2 ) ) = deduped_7_1[deduped_1_2] then
                            return IndexOfMorphism( morB_2 ) = deduped_8_1[deduped_1_2];
                        else
                            return false;
                        fi;
                        return;
                    end )(  ) then
                return [ 0 .. deduped_2_1[SafePosition( deduped_1_1, deduped_3_2 )] - 1 ];
            else
                return deduped_30_1;
            fi;
            return;
        end );
    hoisted_19_1 := List( deduped_26_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2;
            deduped_4_2 := 1 + (CAP_JIT_INCOMPLETE_LOGIC( i_2 ) + deduped_28_1);
            hoisted_3_2 := hoisted_17_1[1 + i_2];
            hoisted_2_2 := deduped_21_1[deduped_4_2];
            hoisted_1_2 := Product( deduped_21_1{[ 1 .. deduped_4_2 - 1 ]} );
            return List( deduped_20_1, function ( i_3 )
                    return hoisted_3_2[1 + CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( CAP_JIT_INCOMPLETE_LOGIC( i_3 ), hoisted_1_2 ), hoisted_2_2 ) )];
                end );
        end );
    hoisted_13_1 := Concatenation( deduped_22_1, deduped_23_1 );
    deduped_3_1 := deduped_31_1[3];
    hoisted_14_1 := List( deduped_26_1, function ( i_2 )
            return deduped_2_1[SafePosition( deduped_1_1, hoisted_13_1[1 + deduped_3_1[(1 + i_2)]] )];
        end );
    deduped_15_1 := List( deduped_26_1, function ( j_2 )
            return Product( hoisted_14_1{[ 1 .. j_2 ]} );
        end );
    hoisted_9_1 := [ deduped_24_1, deduped_24_1, deduped_25_1 ];
    hoisted_4_1 := Concatenation( List( deduped_22_1, IndexOfObject ), List( deduped_23_1, IndexOfObject ) );
    hoisted_12_1 := List( deduped_26_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2, deduped_6_2, deduped_7_2;
            deduped_7_2 := 1 + deduped_3_1[(1 + CAP_JIT_INCOMPLETE_LOGIC( i_2 ))];
            deduped_6_2 := 1 + deduped_5_1[(1 + hoisted_4_1[deduped_7_2])];
            deduped_5_2 := deduped_6_1[deduped_6_2];
            deduped_4_2 := 1 + deduped_5_1[(1 + deduped_5_2)];
            hoisted_3_2 := CAP_JIT_INCOMPLETE_LOGIC( IdFunc( function (  )
                        if IdFunc( function (  )
                                    if deduped_5_2 = deduped_6_1[deduped_4_2] and deduped_7_1[deduped_6_2] = deduped_7_1[deduped_4_2] then
                                        return deduped_8_1[deduped_6_2] = deduped_8_1[deduped_4_2];
                                    else
                                        return false;
                                    fi;
                                    return;
                                end )(  ) then
                            return [ 0 .. deduped_2_1[SafePosition( deduped_1_1, hoisted_9_1[deduped_6_2] )] - 1 ];
                        else
                            return deduped_30_1;
                        fi;
                        return;
                    end )(  ) );
            hoisted_2_2 := deduped_21_1[deduped_7_2];
            hoisted_1_2 := Product( deduped_21_1{[ 1 .. deduped_7_2 - 1 ]} );
            return List( deduped_20_1, function ( i_3 )
                    return hoisted_3_2[1 + CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( CAP_JIT_INCOMPLETE_LOGIC( i_3 ), hoisted_1_2 ), hoisted_2_2 ) )];
                end );
        end );
    return CreateCapCategoryObjectWithAttributes( RangeCategoryOfHomomorphismStructure( cat_1 ), Length, Length( Filtered( deduped_20_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
                return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_26_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_12_1[deduped_1_3][deduped_1_2] * deduped_15_1[deduped_1_3];
                        end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_26_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_19_1[deduped_1_3][deduped_1_2] * deduped_15_1[deduped_1_3];
                        end ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, hoisted_9_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, deduped_15_1, hoisted_17_1, hoisted_19_1, hoisted_21_1, hoisted_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1, deduped_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1;
    deduped_43_1 := DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( range_1 );
    deduped_42_1 := DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( source_1 );
    deduped_41_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
    deduped_40_1 := deduped_43_1[3];
    deduped_39_1 := deduped_43_1[2];
    deduped_38_1 := deduped_43_1[1];
    deduped_37_1 := deduped_42_1[2];
    deduped_36_1 := deduped_42_1[1];
    deduped_35_1 := Source( ModelingCategory( ModelingCategory( cat_1 ) ) );
    deduped_34_1 := [ 0 .. deduped_37_1 - 1 ];
    deduped_33_1 := CreateCapCategoryObjectWithAttributes( deduped_35_1, IndexOfObject, 1 );
    deduped_32_1 := CreateCapCategoryObjectWithAttributes( deduped_35_1, IndexOfObject, 0 );
    deduped_31_1 := ListWithIdenticalEntries( deduped_37_1, deduped_33_1 );
    deduped_30_1 := ListWithIdenticalEntries( deduped_36_1, deduped_32_1 );
    deduped_29_1 := List( ListOfValues( [ CreateCapCategoryObjectWithAttributes( deduped_41_1, Length, deduped_36_1 ), CreateCapCategoryObjectWithAttributes( deduped_41_1, Length, deduped_37_1 ) ] ), Length );
    deduped_2_1 := [ deduped_38_1, deduped_39_1 ];
    deduped_1_1 := [ deduped_32_1, deduped_33_1 ];
    deduped_28_1 := Concatenation( List( deduped_30_1, function ( objB_2 )
              return deduped_2_1[SafePosition( deduped_1_1, objB_2 )];
          end ), List( deduped_31_1, function ( objB_2 )
              return deduped_2_1[SafePosition( deduped_1_1, objB_2 )];
          end ) );
    deduped_27_1 := deduped_29_1[1];
    deduped_26_1 := [ 0 .. Product( deduped_28_1 ) - 1 ];
    deduped_25_1 := Product( deduped_28_1{[ 1 .. deduped_27_1 ]} );
    deduped_8_1 := [ 0, 1, 2 ];
    deduped_7_1 := [ 0, 1, 1 ];
    deduped_6_1 := [ 0, 0, 1 ];
    deduped_5_1 := [ 0, 2 ];
    hoisted_17_1 := List( ListWithIdenticalEntries( deduped_37_1, CreateCapCategoryMorphismWithAttributes( deduped_35_1, deduped_32_1, deduped_33_1, IndexOfMorphism, 1 ) ), function ( morB_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := Source( morB_2 );
            deduped_2_2 := IndexOfObject( deduped_3_2 );
            deduped_1_2 := 1 + deduped_5_1[(1 + deduped_2_2)];
            if IdFunc( function (  )
                        if deduped_2_2 = deduped_6_1[deduped_1_2] and IndexOfObject( Range( morB_2 ) ) = deduped_7_1[deduped_1_2] then
                            return IndexOfMorphism( morB_2 ) = deduped_8_1[deduped_1_2];
                        else
                            return false;
                        fi;
                        return;
                    end )(  ) then
                return [ 0 .. deduped_2_1[SafePosition( deduped_1_1, deduped_3_2 )] - 1 ];
            else
                return deduped_40_1;
            fi;
            return;
        end );
    hoisted_19_1 := List( deduped_34_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2;
            deduped_4_2 := 1 + (CAP_JIT_INCOMPLETE_LOGIC( i_2 ) + deduped_36_1);
            hoisted_3_2 := hoisted_17_1[1 + i_2];
            hoisted_2_2 := deduped_28_1[deduped_4_2];
            hoisted_1_2 := Product( deduped_28_1{[ 1 .. deduped_4_2 - 1 ]} );
            return List( deduped_26_1, function ( i_3 )
                    return hoisted_3_2[1 + CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( CAP_JIT_INCOMPLETE_LOGIC( i_3 ), hoisted_1_2 ), hoisted_2_2 ) )];
                end );
        end );
    hoisted_13_1 := Concatenation( deduped_30_1, deduped_31_1 );
    deduped_3_1 := deduped_42_1[3];
    hoisted_14_1 := List( deduped_34_1, function ( i_2 )
            return deduped_2_1[SafePosition( deduped_1_1, hoisted_13_1[1 + deduped_3_1[(1 + i_2)]] )];
        end );
    deduped_15_1 := List( deduped_34_1, function ( j_2 )
            return Product( hoisted_14_1{[ 1 .. j_2 ]} );
        end );
    hoisted_9_1 := [ deduped_32_1, deduped_32_1, deduped_33_1 ];
    hoisted_4_1 := Concatenation( List( deduped_30_1, IndexOfObject ), List( deduped_31_1, IndexOfObject ) );
    hoisted_12_1 := List( deduped_34_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2, deduped_6_2, deduped_7_2;
            deduped_7_2 := 1 + deduped_3_1[(1 + CAP_JIT_INCOMPLETE_LOGIC( i_2 ))];
            deduped_6_2 := 1 + deduped_5_1[(1 + hoisted_4_1[deduped_7_2])];
            deduped_5_2 := deduped_6_1[deduped_6_2];
            deduped_4_2 := 1 + deduped_5_1[(1 + deduped_5_2)];
            hoisted_3_2 := CAP_JIT_INCOMPLETE_LOGIC( IdFunc( function (  )
                        if IdFunc( function (  )
                                    if deduped_5_2 = deduped_6_1[deduped_4_2] and deduped_7_1[deduped_6_2] = deduped_7_1[deduped_4_2] then
                                        return deduped_8_1[deduped_6_2] = deduped_8_1[deduped_4_2];
                                    else
                                        return false;
                                    fi;
                                    return;
                                end )(  ) then
                            return [ 0 .. deduped_2_1[SafePosition( deduped_1_1, hoisted_9_1[deduped_6_2] )] - 1 ];
                        else
                            return deduped_40_1;
                        fi;
                        return;
                    end )(  ) );
            hoisted_2_2 := deduped_28_1[deduped_7_2];
            hoisted_1_2 := Product( deduped_28_1{[ 1 .. deduped_7_2 - 1 ]} );
            return List( deduped_26_1, function ( i_3 )
                    return hoisted_3_2[1 + CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( CAP_JIT_INCOMPLETE_LOGIC( i_3 ), hoisted_1_2 ), hoisted_2_2 ) )];
                end );
        end );
    deduped_24_1 := CAP_JIT_INCOMPLETE_LOGIC( Filtered( deduped_26_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
                return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_34_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_12_1[deduped_1_3][deduped_1_2] * deduped_15_1[deduped_1_3];
                        end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_34_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_19_1[deduped_1_3][deduped_1_2] * deduped_15_1[deduped_1_3];
                        end ) );
            end )[1 + AsList( alpha_1 )[(1 + CAP_JIT_INCOMPLETE_LOGIC( [ 0 .. (Length( Source( alpha_1 ) ) - 1) ][1] ))]] );
    hoisted_23_1 := CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( deduped_24_1, deduped_25_1 ), Product( deduped_28_1{[ 1 + deduped_27_1 .. Sum( deduped_29_1{[ 1, 2 ]} ) ]} ) ) );
    hoisted_21_1 := CAP_JIT_INCOMPLETE_LOGIC( REM_INT( deduped_24_1, deduped_25_1 ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, DefiningPairOfBouquetMorphismEnrichedOverSkeletalFinSets, NTuple( 2, List( [ 0 .. deduped_27_1 - 1 ], function ( i_2 )
                return REM_INT( QUO_INT( hoisted_21_1, deduped_38_1 ^ i_2 ), deduped_38_1 );
            end ), List( [ 0 .. deduped_29_1[2] - 1 ], function ( i_2 )
                return REM_INT( QUO_INT( hoisted_23_1, deduped_39_1 ^ i_2 ), deduped_39_1 );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddMorphismsOfExternalHom( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, hoisted_9_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, deduped_15_1, hoisted_17_1, hoisted_19_1, deduped_22_1, hoisted_24_1, hoisted_25_1, hoisted_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1, deduped_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1, deduped_44_1, deduped_45_1, deduped_46_1, deduped_47_1;
    deduped_47_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
    deduped_46_1 := DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( arg3_1 );
    deduped_45_1 := DefiningTripleOfBouquetEnrichedOverSkeletalFinSets( arg2_1 );
    deduped_44_1 := deduped_46_1[3];
    deduped_43_1 := deduped_46_1[2];
    deduped_42_1 := deduped_46_1[1];
    deduped_41_1 := deduped_45_1[2];
    deduped_40_1 := deduped_45_1[1];
    deduped_39_1 := Source( ModelingCategory( ModelingCategory( cat_1 ) ) );
    deduped_38_1 := [ 0 .. deduped_41_1 - 1 ];
    deduped_37_1 := CreateCapCategoryObjectWithAttributes( deduped_39_1, IndexOfObject, 1 );
    deduped_36_1 := CreateCapCategoryObjectWithAttributes( deduped_39_1, IndexOfObject, 0 );
    deduped_35_1 := ListWithIdenticalEntries( deduped_41_1, deduped_37_1 );
    deduped_34_1 := ListWithIdenticalEntries( deduped_40_1, deduped_36_1 );
    deduped_33_1 := List( ListOfValues( [ CreateCapCategoryObjectWithAttributes( deduped_47_1, Length, deduped_40_1 ), CreateCapCategoryObjectWithAttributes( deduped_47_1, Length, deduped_41_1 ) ] ), Length );
    deduped_32_1 := deduped_33_1[1];
    deduped_2_1 := [ deduped_42_1, deduped_43_1 ];
    deduped_1_1 := [ deduped_36_1, deduped_37_1 ];
    deduped_31_1 := Concatenation( List( deduped_34_1, function ( objB_2 )
              return deduped_2_1[SafePosition( deduped_1_1, objB_2 )];
          end ), List( deduped_35_1, function ( objB_2 )
              return deduped_2_1[SafePosition( deduped_1_1, objB_2 )];
          end ) );
    deduped_30_1 := [ 0 .. Product( deduped_31_1 ) - 1 ];
    deduped_8_1 := [ 0, 1, 2 ];
    deduped_7_1 := [ 0, 1, 1 ];
    deduped_6_1 := [ 0, 0, 1 ];
    deduped_5_1 := [ 0, 2 ];
    hoisted_17_1 := List( ListWithIdenticalEntries( deduped_41_1, CreateCapCategoryMorphismWithAttributes( deduped_39_1, deduped_36_1, deduped_37_1, IndexOfMorphism, 1 ) ), function ( morB_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := Source( morB_2 );
            deduped_2_2 := IndexOfObject( deduped_3_2 );
            deduped_1_2 := 1 + deduped_5_1[(1 + deduped_2_2)];
            if IdFunc( function (  )
                        if deduped_2_2 = deduped_6_1[deduped_1_2] and IndexOfObject( Range( morB_2 ) ) = deduped_7_1[deduped_1_2] then
                            return IndexOfMorphism( morB_2 ) = deduped_8_1[deduped_1_2];
                        else
                            return false;
                        fi;
                        return;
                    end )(  ) then
                return [ 0 .. deduped_2_1[SafePosition( deduped_1_1, deduped_3_2 )] - 1 ];
            else
                return deduped_44_1;
            fi;
            return;
        end );
    hoisted_19_1 := List( deduped_38_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2;
            deduped_4_2 := 1 + (CAP_JIT_INCOMPLETE_LOGIC( i_2 ) + deduped_40_1);
            hoisted_3_2 := hoisted_17_1[1 + i_2];
            hoisted_2_2 := deduped_31_1[deduped_4_2];
            hoisted_1_2 := Product( deduped_31_1{[ 1 .. deduped_4_2 - 1 ]} );
            return List( deduped_30_1, function ( i_3 )
                    return hoisted_3_2[1 + CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( CAP_JIT_INCOMPLETE_LOGIC( i_3 ), hoisted_1_2 ), hoisted_2_2 ) )];
                end );
        end );
    hoisted_13_1 := Concatenation( deduped_34_1, deduped_35_1 );
    deduped_3_1 := deduped_45_1[3];
    hoisted_14_1 := List( deduped_38_1, function ( i_2 )
            return deduped_2_1[SafePosition( deduped_1_1, hoisted_13_1[1 + deduped_3_1[(1 + i_2)]] )];
        end );
    deduped_15_1 := List( deduped_38_1, function ( j_2 )
            return Product( hoisted_14_1{[ 1 .. j_2 ]} );
        end );
    hoisted_9_1 := [ deduped_36_1, deduped_36_1, deduped_37_1 ];
    hoisted_4_1 := Concatenation( List( deduped_34_1, IndexOfObject ), List( deduped_35_1, IndexOfObject ) );
    hoisted_12_1 := List( deduped_38_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2, deduped_6_2, deduped_7_2;
            deduped_7_2 := 1 + deduped_3_1[(1 + CAP_JIT_INCOMPLETE_LOGIC( i_2 ))];
            deduped_6_2 := 1 + deduped_5_1[(1 + hoisted_4_1[deduped_7_2])];
            deduped_5_2 := deduped_6_1[deduped_6_2];
            deduped_4_2 := 1 + deduped_5_1[(1 + deduped_5_2)];
            hoisted_3_2 := CAP_JIT_INCOMPLETE_LOGIC( IdFunc( function (  )
                        if IdFunc( function (  )
                                    if deduped_5_2 = deduped_6_1[deduped_4_2] and deduped_7_1[deduped_6_2] = deduped_7_1[deduped_4_2] then
                                        return deduped_8_1[deduped_6_2] = deduped_8_1[deduped_4_2];
                                    else
                                        return false;
                                    fi;
                                    return;
                                end )(  ) then
                            return [ 0 .. deduped_2_1[SafePosition( deduped_1_1, hoisted_9_1[deduped_6_2] )] - 1 ];
                        else
                            return deduped_44_1;
                        fi;
                        return;
                    end )(  ) );
            hoisted_2_2 := deduped_31_1[deduped_7_2];
            hoisted_1_2 := Product( deduped_31_1{[ 1 .. deduped_7_2 - 1 ]} );
            return List( deduped_30_1, function ( i_3 )
                    return hoisted_3_2[1 + CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( CAP_JIT_INCOMPLETE_LOGIC( i_3 ), hoisted_1_2 ), hoisted_2_2 ) )];
                end );
        end );
    deduped_29_1 := Filtered( deduped_30_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_38_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_12_1[deduped_1_3][deduped_1_2] * deduped_15_1[deduped_1_3];
                    end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_38_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_19_1[deduped_1_3][deduped_1_2] * deduped_15_1[deduped_1_3];
                    end ) );
        end );
    deduped_28_1 := Length( deduped_29_1 );
    hoisted_27_1 := [ 0 .. deduped_33_1[2] - 1 ];
    hoisted_25_1 := Product( deduped_31_1{[ 1 + deduped_32_1 .. Sum( deduped_33_1{[ 1, 2 ]} ) ]} );
    hoisted_24_1 := [ 0 .. deduped_32_1 - 1 ];
    deduped_22_1 := Product( deduped_31_1{[ 1 .. deduped_32_1 ]} );
    return List( [ 0 .. deduped_28_1 - 1 ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := CAP_JIT_INCOMPLETE_LOGIC( deduped_29_1[1 + REM_INT( i_2, deduped_28_1 )] );
            hoisted_2_2 := CAP_JIT_INCOMPLETE_LOGIC( REM_INT( QUO_INT( deduped_3_2, deduped_22_1 ), hoisted_25_1 ) );
            hoisted_1_2 := CAP_JIT_INCOMPLETE_LOGIC( REM_INT( deduped_3_2, deduped_22_1 ) );
            return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg3_1, DefiningPairOfBouquetMorphismEnrichedOverSkeletalFinSets, NTuple( 2, List( hoisted_24_1, function ( i_3 )
                        return REM_INT( QUO_INT( hoisted_1_2, deduped_42_1 ^ i_3 ), deduped_42_1 );
                    end ), List( hoisted_27_1, function ( i_3 )
                        return REM_INT( QUO_INT( hoisted_2_2, deduped_43_1 ^ i_3 ), deduped_43_1 );
                    end ) ) );
        end );
end
########
        
    , 802 : IsPrecompiledDerivation := true );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "FinBouquetsPrecompiled", function (  )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function (  )
    return CategoryOfBouquetsEnrichedOver( CategoryOfSkeletalFinSets(  : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor(  : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_FinBouquetsPrecompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
