# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_PreSheavesOfCategoryFromDataTablesInSkeletalFinSetsPrecompiled", function ( cat )
    
    ##
    AddInitialObject( cat,
        
########
function ( cat_1 )
    local hoisted_2_1, deduped_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Target( cat_1 );
    deduped_5_1 := Source( cat_1 );
    deduped_4_1 := CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, BigInt( 0 ) );
    deduped_3_1 := DefiningTripleOfUnderlyingQuiver( deduped_5_1 );
    hoisted_2_1 := CreateCapCategoryMorphismWithAttributes( deduped_6_1, deduped_4_1, deduped_4_1, AsList, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsInt ) );
          end ) );
    return CreateCapCategoryObjectWithAttributes( cat_1, Source, deduped_5_1, Target, deduped_6_1, ValuesOfPreSheaf, NTuple( 2, LazyHList( [ 1 .. deduped_3_1[1] ], function ( o_2 )
                return deduped_4_1;
            end ), LazyHList( [ 1 .. deduped_3_1[2] ], function ( m_2 )
                return hoisted_2_1;
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddCoproduct( cat,
        
########
function ( cat_1, objects_1 )
    local hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Target( cat_1 );
    deduped_5_1 := Source( cat_1 );
    deduped_4_1 := DefiningTripleOfUnderlyingQuiver( deduped_5_1 );
    hoisted_3_1 := [ 1 .. Length( objects_1 ) ];
    hoisted_2_1 := deduped_4_1[3];
    return CreateCapCategoryObjectWithAttributes( cat_1, Source, deduped_5_1, Target, deduped_6_1, ValuesOfPreSheaf, NTuple( 2, LazyHList( [ 1 .. deduped_4_1[1] ], function ( o_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, Sum( List( objects_1, function ( F_3 )
                            return CAP_JIT_INCOMPLETE_LOGIC( Cardinality( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][o_2] ) ) );
                        end ) ) );
            end ), LazyHList( [ 1 .. deduped_4_1[2] ], function ( m_2 )
                local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                deduped_4_2 := hoisted_2_1[m_2];
                deduped_3_2 := List( objects_1, function ( F_3 )
                        return CAP_JIT_INCOMPLETE_LOGIC( Cardinality( Range( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[2][m_2] ) ) ) );
                    end );
                hoisted_2_2 := 1 + deduped_4_2[1];
                hoisted_1_2 := 1 + deduped_4_2[2];
                return CreateCapCategoryMorphismWithAttributes( deduped_6_1, CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, Sum( List( objects_1, function ( F_3 )
                              return CAP_JIT_INCOMPLETE_LOGIC( Cardinality( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][hoisted_1_2] ) ) );
                          end ) ) ), CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, Sum( List( objects_1, function ( F_3 )
                              return CAP_JIT_INCOMPLETE_LOGIC( Cardinality( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][hoisted_2_2] ) ) );
                          end ) ) ), AsList, Concatenation( List( hoisted_3_1, function ( i_3 )
                            local hoisted_1_3, hoisted_2_3, deduped_3_3, deduped_4_3;
                            deduped_4_3 := Sum( deduped_3_2{[ 1 .. i_3 - 1 ]} );
                            deduped_3_3 := CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( CAP_JIT_INCOMPLETE_LOGIC( objects_1[i_3] ) )[2][m_2] );
                            hoisted_2_3 := [ deduped_4_3 .. deduped_4_3 + deduped_3_2[i_3] - 1 ];
                            hoisted_1_3 := CAP_JIT_INCOMPLETE_LOGIC( AsList( deduped_3_3 ) );
                            return List( [ 0 .. CAP_JIT_INCOMPLETE_LOGIC( Cardinality( Source( deduped_3_3 ) ) ) - 1 ], function ( i_4 )
                                    return hoisted_2_3[1 + hoisted_1_3[1 + i_4]];
                                end );
                        end ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.Coproduct :=
        
########
function ( cat_1, objects_1 )
    local hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Target( cat_1 );
    deduped_5_1 := Source( cat_1 );
    deduped_4_1 := DefiningTripleOfUnderlyingQuiver( deduped_5_1 );
    hoisted_3_1 := [ 1 .. Length( objects_1 ) ];
    hoisted_2_1 := deduped_4_1[3];
    return CreateCapCategoryObjectWithAttributes( cat_1, Source, deduped_5_1, Target, deduped_6_1, ValuesOfPreSheaf, NTuple( 2, LazyHList( [ 1 .. deduped_4_1[1] ], function ( o_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, Sum( List( objects_1, function ( F_3 )
                            return List( ValuesOfPreSheaf( F_3 )[1], Cardinality )[o_2];
                        end ) ) );
            end ), LazyHList( [ 1 .. deduped_4_1[2] ], function ( m_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, hoisted_5_2, deduped_6_2;
                deduped_6_2 := hoisted_2_1[m_2];
                hoisted_5_2 := List( objects_1, function ( F_3 )
                        return List( ValuesOfPreSheaf( F_3 )[2], AsList )[m_2];
                    end );
                deduped_4_2 := List( objects_1, function ( F_3 )
                        return List( ValuesOfPreSheaf( F_3 )[2], function ( logic_new_func_x_4 )
                                  return Cardinality( Range( logic_new_func_x_4 ) );
                              end )[m_2];
                    end );
                hoisted_3_2 := List( objects_1, function ( F_3 )
                        return List( ValuesOfPreSheaf( F_3 )[2], function ( logic_new_func_x_4 )
                                  return Cardinality( Source( logic_new_func_x_4 ) );
                              end )[m_2];
                    end );
                hoisted_2_2 := 1 + deduped_6_2[1];
                hoisted_1_2 := 1 + deduped_6_2[2];
                return CreateCapCategoryMorphismWithAttributes( deduped_6_1, CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, Sum( List( objects_1, function ( F_3 )
                              return List( ValuesOfPreSheaf( F_3 )[1], Cardinality )[hoisted_1_2];
                          end ) ) ), CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, Sum( List( objects_1, function ( F_3 )
                              return List( ValuesOfPreSheaf( F_3 )[1], Cardinality )[hoisted_2_2];
                          end ) ) ), AsList, Concatenation( List( hoisted_3_1, function ( i_3 )
                            local hoisted_1_3, hoisted_2_3, deduped_3_3;
                            deduped_3_3 := Sum( deduped_4_2{[ 1 .. i_3 - 1 ]} );
                            hoisted_2_3 := [ deduped_3_3 .. deduped_3_3 + deduped_4_2[i_3] - 1 ];
                            hoisted_1_3 := hoisted_5_2[i_3];
                            return List( [ 0 .. hoisted_3_2[i_3] - 1 ], function ( i_4 )
                                    return hoisted_2_3[1 + hoisted_1_3[1 + i_4]];
                                end );
                        end ) ) );
            end ) ) );
end
########
        
    ;
    
    ##
    AddInjectionOfCofactorOfCoproductWithGivenCoproduct( cat,
        
########
function ( cat_1, objects_1, k_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1;
    deduped_5_1 := objects_1[k_1];
    hoisted_4_1 := Target( cat_1 );
    hoisted_3_1 := [ 1 .. k_1 - 1 ];
    hoisted_2_1 := ValuesOfPreSheaf( P_1 )[1];
    hoisted_1_1 := ValuesOfPreSheaf( CAP_JIT_INCOMPLETE_LOGIC( deduped_5_1 ) )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_5_1, P_1, ValuesOnAllObjects, LazyHList( [ 1 .. DefiningTripleOfUnderlyingQuiver( Source( cat_1 ) )[1] ], function ( o_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := List( objects_1, function ( F_3 )
                      return CAP_JIT_INCOMPLETE_LOGIC( Cardinality( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][o_2] ) ) );
                  end );
              deduped_1_2 := Sum( deduped_2_2{hoisted_3_1} );
              return CreateCapCategoryMorphismWithAttributes( hoisted_4_1, CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[o_2] ), hoisted_2_1[o_2], AsList, [ deduped_1_2 .. deduped_1_2 + deduped_2_2[k_1] - 1 ] );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.InjectionOfCofactorOfCoproductWithGivenCoproduct :=
        
########
function ( cat_1, objects_1, k_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1;
    hoisted_3_1 := Target( cat_1 );
    hoisted_2_1 := [ 1 .. k_1 - 1 ];
    hoisted_1_1 := ValuesOfPreSheaf( P_1 )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, objects_1[k_1], P_1, ValuesOnAllObjects, LazyHList( [ 1 .. DefiningTripleOfUnderlyingQuiver( Source( cat_1 ) )[1] ], function ( o_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := List( objects_1, function ( F_3 )
                      return List( ValuesOfPreSheaf( F_3 )[1], Cardinality )[o_2];
                  end );
              deduped_1_2 := Sum( deduped_2_2{hoisted_2_1} );
              return CreateCapCategoryMorphismWithAttributes( hoisted_3_1, List( objects_1, function ( F_3 )
                          return ValuesOfPreSheaf( F_3 )[1][o_2];
                      end )[k_1], hoisted_1_1[o_2], AsList, [ deduped_1_2 .. deduped_1_2 + deduped_2_2[k_1] - 1 ] );
          end ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismFromCoproductWithGivenCoproduct( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1;
    hoisted_3_1 := Target( cat_1 );
    hoisted_2_1 := ValuesOfPreSheaf( T_1 )[1];
    hoisted_1_1 := ValuesOfPreSheaf( P_1 )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ValuesOnAllObjects, LazyHList( [ 1 .. DefiningTripleOfUnderlyingQuiver( Source( cat_1 ) )[1] ], function ( o_2 )
              return CreateCapCategoryMorphismWithAttributes( hoisted_3_1, hoisted_1_1[o_2], hoisted_2_1[o_2], AsList, Concatenation( List( tau_1, function ( eta_3 )
                          return CAP_JIT_INCOMPLETE_LOGIC( AsList( CAP_JIT_INCOMPLETE_LOGIC( ValuesOnAllObjects( eta_3 )[o_2] ) ) );
                      end ) ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromCoproductWithGivenCoproduct :=
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1;
    hoisted_3_1 := Target( cat_1 );
    hoisted_2_1 := ValuesOfPreSheaf( T_1 )[1];
    hoisted_1_1 := ValuesOfPreSheaf( P_1 )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ValuesOnAllObjects, LazyHList( [ 1 .. DefiningTripleOfUnderlyingQuiver( Source( cat_1 ) )[1] ], function ( o_2 )
              return CreateCapCategoryMorphismWithAttributes( hoisted_3_1, hoisted_1_1[o_2], hoisted_2_1[o_2], AsList, Concatenation( List( tau_1, function ( eta_3 )
                          return List( ValuesOnAllObjects( eta_3 ), AsList )[o_2];
                      end ) ) );
          end ) );
end
########
        
    ;
    
    ##
    AddHomomorphismStructureOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, hoisted_11_1, deduped_12_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_25_1, deduped_28_1, hoisted_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, hoisted_37_1, hoisted_38_1, hoisted_39_1, deduped_40_1, hoisted_42_1, deduped_43_1, deduped_44_1, hoisted_45_1, hoisted_46_1, hoisted_47_1, hoisted_48_1, deduped_49_1, deduped_50_1, deduped_51_1, deduped_52_1, deduped_53_1, deduped_54_1, deduped_55_1, deduped_56_1, deduped_57_1, deduped_58_1, deduped_59_1, deduped_60_1, deduped_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1;
    deduped_67_1 := ValuesOfPreSheaf( arg3_1 );
    deduped_66_1 := ValuesOfPreSheaf( arg2_1 );
    deduped_65_1 := Source( cat_1 );
    deduped_64_1 := Target( cat_1 );
    deduped_63_1 := DataTables( deduped_65_1 );
    deduped_62_1 := DefiningTripleOfUnderlyingQuiver( deduped_65_1 );
    deduped_61_1 := deduped_63_1[2];
    deduped_60_1 := deduped_63_1[1];
    deduped_59_1 := [ 0 .. deduped_62_1[1] - 1 ];
    deduped_58_1 := [ 0 .. deduped_62_1[2] - 1 ];
    deduped_57_1 := [ 0 .. deduped_62_1[1] - 1 ];
    deduped_56_1 := [ 0 .. deduped_60_1[2] - 1 ];
    deduped_55_1 := [ 0 .. deduped_60_1[1] - 1 ];
    deduped_4_1 := deduped_66_1[1];
    deduped_54_1 := List( deduped_59_1, function ( o_2 )
            return Cardinality( deduped_4_1[1 + o_2] );
        end );
    hoisted_11_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_8_1 := deduped_62_1[3];
    deduped_10_1 := List( deduped_58_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][1] );
        end );
    deduped_9_1 := List( deduped_58_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][2] );
        end );
    deduped_6_1 := List( deduped_55_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_65_1, IndexOfObject, i_2 );
        end );
    deduped_12_1 := List( deduped_58_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( m_2 );
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return PairOfIntAndList( CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( hoisted_11_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[1 + deduped_10_1[deduped_2_2]] ) ) ) ) );
        end );
    deduped_53_1 := [ 0 .. Sum( List( deduped_58_1, function ( i_2 )
                    return deduped_12_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_52_1 := [ 1 .. Sum( List( deduped_58_1, function ( m_2 )
                  return Cardinality( deduped_4_1[1 + deduped_9_1[1 + m_2]] );
              end ) ) ];
    deduped_7_1 := deduped_67_1[1];
    deduped_51_1 := Concatenation( List( deduped_59_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] ) );
          end ) );
    deduped_50_1 := Product( deduped_51_1 );
    deduped_49_1 := [ 0 .. deduped_50_1 - 1 ];
    deduped_16_1 := deduped_61_1[3];
    deduped_15_1 := deduped_61_1[2];
    deduped_18_1 := List( deduped_56_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_65_1, CreateCapCategoryObjectWithAttributes( deduped_65_1, IndexOfObject, deduped_15_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_65_1, IndexOfObject, deduped_16_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_35_1 := List( IndicesOfGeneratingMorphisms( deduped_65_1 ), function ( i_2 )
            return deduped_18_1[1 + i_2];
        end );
    deduped_44_1 := List( deduped_58_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_35_1[deduped_2_2] ) );
        end );
    deduped_17_1 := deduped_61_1[1];
    deduped_14_1 := List( deduped_59_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_4_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[deduped_2_2] ) );
        end );
    deduped_43_1 := List( deduped_58_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_54_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_54_1[deduped_2_2] - 1 ], List( deduped_14_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_36_1 := deduped_67_1[2];
    deduped_34_1 := List( deduped_56_1, function ( i_2 )
            return deduped_16_1[1 + i_2];
        end );
    deduped_33_1 := List( deduped_56_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_65_1, IndexOfObject, deduped_16_1[1 + i_2] );
        end );
    deduped_32_1 := List( deduped_56_1, function ( i_2 )
            return deduped_15_1[1 + i_2];
        end );
    deduped_31_1 := List( deduped_56_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_65_1, IndexOfObject, deduped_15_1[1 + i_2] );
        end );
    deduped_30_1 := deduped_61_1[4];
    hoisted_46_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_44_1[deduped_5_2];
              hoisted_3_2 := List( deduped_43_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_12_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_64_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_36_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_3_1 := List( ValuesOfPreSheaf( arg3_1 )[1], Cardinality );
    deduped_1_1 := List( ValuesOfPreSheaf( arg2_1 )[1], Cardinality );
    deduped_28_1 := CreateCapCategoryObjectWithAttributes( deduped_64_1, Cardinality, Product( Concatenation( List( deduped_57_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_3_1[deduped_1_2] );
              end ) ) ) );
    deduped_25_1 := Sum( deduped_54_1 );
    deduped_22_1 := Concatenation( List( deduped_59_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] );
          end ) );
    hoisted_45_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_43_1[deduped_3_2][1];
              hoisted_1_2 := deduped_44_1[deduped_3_2][1];
              return List( [ 0 .. deduped_12_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_51_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_51_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_50_1, deduped_4_3, deduped_5_3 * Product( deduped_51_1{[ deduped_6_3 + 1 .. deduped_25_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_64_1, deduped_28_1, deduped_22_1[deduped_6_3], AsList, List( deduped_49_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_50_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_47_1 := List( deduped_53_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_45_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_46_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_39_1 := Concatenation( List( deduped_58_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[1 + deduped_9_1[deduped_1_2]] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_1_2]] )] ) );
          end ) );
    deduped_40_1 := List( deduped_52_1, function ( j_2 )
            return Product( hoisted_39_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_48_1 := List( deduped_49_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_52_1, function ( j_3 )
                    return hoisted_47_1[j_3][hoisted_1_2] * deduped_40_1[j_3];
                end );
        end );
    hoisted_20_1 := deduped_66_1[2];
    deduped_21_1 := List( deduped_58_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_20_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_2_2]] )]] ) );
        end );
    deduped_19_1 := List( deduped_58_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_10_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_54_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_54_1[deduped_2_2] - 1 ], List( deduped_14_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_37_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_21_1[deduped_5_2];
              hoisted_3_2 := List( deduped_19_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_12_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_64_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_36_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_29_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_19_1[deduped_3_2][1];
              hoisted_1_2 := deduped_21_1[deduped_3_2][1];
              return List( [ 0 .. deduped_12_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_51_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_51_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_50_1, deduped_4_3, deduped_5_3 * Product( deduped_51_1{[ deduped_6_3 + 1 .. deduped_25_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_64_1, deduped_28_1, deduped_22_1[deduped_6_3], AsList, List( deduped_49_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_50_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_38_1 := List( deduped_53_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_29_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_37_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_42_1 := List( deduped_49_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_52_1, function ( j_3 )
                    return hoisted_38_1[j_3][hoisted_1_2] * deduped_40_1[j_3];
                end );
        end );
    return CreateCapCategoryObjectWithAttributes( deduped_64_1, Cardinality, BigInt( Length( Filtered( [ 0 .. Product( Concatenation( List( deduped_57_1, function ( o_2 )
                              local deduped_1_2;
                              deduped_1_2 := 1 + o_2;
                              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_3_1[1 + deduped_55_1[deduped_1_2]] );
                          end ) ) ) - 1 ], function ( x_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + x_2;
                  return hoisted_42_1[deduped_1_2] = hoisted_48_1[deduped_1_2];
              end ) ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.HomomorphismStructureOnObjects :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, hoisted_11_1, hoisted_12_1, deduped_13_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, hoisted_23_1, deduped_24_1, deduped_25_1, deduped_28_1, deduped_31_1, hoisted_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1, deduped_39_1, hoisted_40_1, hoisted_41_1, hoisted_42_1, deduped_43_1, hoisted_45_1, deduped_46_1, deduped_47_1, hoisted_48_1, hoisted_49_1, hoisted_50_1, hoisted_51_1, deduped_52_1, deduped_53_1, deduped_54_1, deduped_55_1, deduped_56_1, deduped_57_1, deduped_58_1, deduped_59_1, deduped_60_1, deduped_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1, deduped_69_1, deduped_70_1, deduped_71_1, deduped_72_1;
    deduped_72_1 := ValuesOfPreSheaf( arg3_1 );
    deduped_71_1 := ValuesOfPreSheaf( arg2_1 );
    deduped_70_1 := Source( cat_1 );
    deduped_69_1 := Target( cat_1 );
    deduped_68_1 := DataTables( deduped_70_1 );
    deduped_67_1 := DefiningTripleOfUnderlyingQuiver( deduped_70_1 );
    deduped_66_1 := deduped_68_1[2];
    deduped_65_1 := List( ValuesOfPreSheaf( arg3_1 )[1], Cardinality );
    deduped_64_1 := deduped_68_1[1];
    deduped_63_1 := List( ValuesOfPreSheaf( arg2_1 )[1], Cardinality );
    deduped_62_1 := [ 0 .. deduped_67_1[1] - 1 ];
    deduped_61_1 := [ 0 .. deduped_67_1[2] - 1 ];
    deduped_60_1 := [ 0 .. deduped_67_1[1] - 1 ];
    deduped_59_1 := [ 0 .. deduped_64_1[2] - 1 ];
    deduped_58_1 := [ 0 .. deduped_64_1[1] - 1 ];
    deduped_4_1 := deduped_71_1[1];
    deduped_57_1 := List( deduped_62_1, function ( o_2 )
            return Cardinality( deduped_4_1[1 + o_2] );
        end );
    hoisted_11_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_8_1 := deduped_67_1[3];
    deduped_10_1 := List( deduped_61_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][1] );
        end );
    deduped_9_1 := List( deduped_61_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][2] );
        end );
    deduped_6_1 := List( deduped_58_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_70_1, IndexOfObject, i_2 );
        end );
    hoisted_12_1 := List( deduped_61_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return CreateCapCategoryObjectWithAttributes( hoisted_11_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[1 + deduped_10_1[deduped_2_2]] ) ) );
        end );
    deduped_13_1 := List( deduped_61_1, function ( m_2 )
            return PairOfIntAndList( hoisted_12_1[1 + m_2] );
        end );
    deduped_56_1 := [ 0 .. Sum( List( deduped_61_1, function ( i_2 )
                    return deduped_13_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_55_1 := [ 1 .. Sum( List( deduped_61_1, function ( m_2 )
                  return Cardinality( deduped_4_1[1 + deduped_9_1[1 + m_2]] );
              end ) ) ];
    deduped_7_1 := deduped_72_1[1];
    deduped_54_1 := Concatenation( List( deduped_62_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] ) );
          end ) );
    deduped_53_1 := Product( deduped_54_1 );
    deduped_52_1 := [ 0 .. deduped_53_1 - 1 ];
    deduped_19_1 := deduped_66_1[3];
    deduped_18_1 := deduped_66_1[2];
    deduped_21_1 := List( deduped_59_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_70_1, CreateCapCategoryObjectWithAttributes( deduped_70_1, IndexOfObject, deduped_18_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_70_1, IndexOfObject, deduped_19_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_38_1 := List( IndicesOfGeneratingMorphisms( deduped_70_1 ), function ( i_2 )
            return deduped_21_1[1 + i_2];
        end );
    deduped_47_1 := List( deduped_61_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_38_1[deduped_2_2] ) );
        end );
    deduped_20_1 := deduped_66_1[1];
    deduped_17_1 := List( deduped_62_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_4_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[deduped_2_2] ) );
        end );
    deduped_46_1 := List( deduped_61_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_57_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_57_1[deduped_2_2] - 1 ], List( deduped_17_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_21_1[1 + deduped_20_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_39_1 := deduped_72_1[2];
    deduped_37_1 := List( deduped_59_1, function ( i_2 )
            return deduped_19_1[1 + i_2];
        end );
    deduped_36_1 := List( deduped_59_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_70_1, IndexOfObject, deduped_19_1[1 + i_2] );
        end );
    deduped_35_1 := List( deduped_59_1, function ( i_2 )
            return deduped_18_1[1 + i_2];
        end );
    deduped_34_1 := List( deduped_59_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_70_1, IndexOfObject, deduped_18_1[1 + i_2] );
        end );
    deduped_33_1 := deduped_66_1[4];
    hoisted_49_1 := Concatenation( List( deduped_61_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_47_1[deduped_5_2];
              hoisted_3_2 := List( deduped_46_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_13_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_33_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_36_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_34_1[deduped_9_3] );
                      deduped_6_3 := deduped_20_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_35_1[deduped_4_3] and deduped_8_3 = deduped_37_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_21_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_69_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_39_1[SafeUniquePositionProperty( deduped_38_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_31_1 := CreateCapCategoryObjectWithAttributes( deduped_69_1, Cardinality, Product( Concatenation( List( deduped_60_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_63_1[deduped_1_2], deduped_65_1[deduped_1_2] );
              end ) ) ) );
    deduped_28_1 := Sum( deduped_57_1 );
    deduped_25_1 := Concatenation( List( deduped_62_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] );
          end ) );
    hoisted_48_1 := Concatenation( List( deduped_61_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_46_1[deduped_3_2][1];
              hoisted_1_2 := deduped_47_1[deduped_3_2][1];
              return List( [ 0 .. deduped_13_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_54_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_54_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_53_1, deduped_4_3, deduped_5_3 * Product( deduped_54_1{[ deduped_6_3 + 1 .. deduped_28_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_69_1, deduped_31_1, deduped_25_1[deduped_6_3], AsList, List( deduped_52_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_53_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_50_1 := List( deduped_56_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_48_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_49_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_42_1 := Concatenation( List( deduped_61_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[1 + deduped_9_1[deduped_1_2]] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_1_2]] )] ) );
          end ) );
    deduped_43_1 := List( deduped_55_1, function ( j_2 )
            return Product( hoisted_42_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_51_1 := List( deduped_52_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_55_1, function ( j_3 )
                    return hoisted_50_1[j_3][hoisted_1_2] * deduped_43_1[j_3];
                end );
        end );
    hoisted_23_1 := deduped_71_1[2];
    deduped_24_1 := List( deduped_61_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_23_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_21_1[1 + deduped_20_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_2_2]] )]] ) );
        end );
    deduped_22_1 := List( deduped_61_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_10_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_57_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_57_1[deduped_2_2] - 1 ], List( deduped_17_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_21_1[1 + deduped_20_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_40_1 := Concatenation( List( deduped_61_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_24_1[deduped_5_2];
              hoisted_3_2 := List( deduped_22_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_13_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_33_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_36_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_34_1[deduped_9_3] );
                      deduped_6_3 := deduped_20_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_35_1[deduped_4_3] and deduped_8_3 = deduped_37_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_21_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_69_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_39_1[SafeUniquePositionProperty( deduped_38_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_32_1 := Concatenation( List( deduped_61_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_22_1[deduped_3_2][1];
              hoisted_1_2 := deduped_24_1[deduped_3_2][1];
              return List( [ 0 .. deduped_13_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_54_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_54_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_53_1, deduped_4_3, deduped_5_3 * Product( deduped_54_1{[ deduped_6_3 + 1 .. deduped_28_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_69_1, deduped_31_1, deduped_25_1[deduped_6_3], AsList, List( deduped_52_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_53_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_41_1 := List( deduped_56_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_32_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_40_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_45_1 := List( deduped_52_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_55_1, function ( j_3 )
                    return hoisted_41_1[j_3][hoisted_1_2] * deduped_43_1[j_3];
                end );
        end );
    return CreateCapCategoryObjectWithAttributes( deduped_69_1, Cardinality, BigInt( Length( Filtered( [ 0 .. Product( Concatenation( List( deduped_60_1, function ( o_2 )
                              local deduped_1_2;
                              deduped_1_2 := 1 + o_2;
                              return ListWithIdenticalEntries( deduped_63_1[deduped_1_2], deduped_65_1[1 + deduped_58_1[deduped_1_2]] );
                          end ) ) ) - 1 ], function ( x_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + x_2;
                  return hoisted_45_1[deduped_1_2] = hoisted_51_1[deduped_1_2];
              end ) ) ) );
end
########
        
    ;
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, beta_1, range_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, hoisted_19_1, deduped_20_1, deduped_21_1, deduped_24_1, deduped_27_1, hoisted_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, hoisted_36_1, hoisted_37_1, hoisted_38_1, deduped_39_1, hoisted_41_1, deduped_42_1, deduped_43_1, hoisted_44_1, hoisted_45_1, hoisted_46_1, hoisted_47_1, deduped_48_1, deduped_49_1, hoisted_50_1, hoisted_51_1, hoisted_56_1, hoisted_57_1, hoisted_58_1, deduped_60_1, deduped_61_1, hoisted_62_1, hoisted_63_1, hoisted_64_1, deduped_65_1, hoisted_66_1, hoisted_67_1, hoisted_68_1, hoisted_72_1, hoisted_74_1, hoisted_75_1, hoisted_76_1, hoisted_77_1, deduped_78_1, deduped_79_1, deduped_80_1, deduped_82_1, deduped_83_1, hoisted_84_1, deduped_85_1, deduped_86_1, deduped_89_1, hoisted_91_1, deduped_92_1, hoisted_93_1, hoisted_94_1, hoisted_95_1, deduped_96_1, hoisted_98_1, deduped_99_1, deduped_100_1, hoisted_101_1, hoisted_102_1, hoisted_103_1, hoisted_104_1, hoisted_105_1, hoisted_106_1, hoisted_107_1, deduped_108_1, deduped_109_1, deduped_110_1, deduped_111_1, deduped_112_1, deduped_113_1, deduped_114_1, deduped_115_1, deduped_116_1, deduped_117_1, deduped_118_1, deduped_119_1, deduped_120_1, deduped_121_1, deduped_122_1, deduped_123_1, deduped_124_1, deduped_125_1, deduped_126_1, deduped_127_1, deduped_128_1, deduped_129_1, deduped_130_1, deduped_131_1, deduped_132_1, deduped_133_1, deduped_134_1, deduped_135_1, deduped_136_1, deduped_137_1, deduped_138_1, deduped_139_1, deduped_140_1, deduped_141_1, deduped_142_1, deduped_143_1, deduped_144_1, deduped_145_1, deduped_146_1;
    deduped_146_1 := Source( cat_1 );
    deduped_145_1 := Target( cat_1 );
    deduped_144_1 := ValuesOfPreSheaf( Source( beta_1 ) );
    deduped_143_1 := ValuesOfPreSheaf( Target( alpha_1 ) );
    deduped_142_1 := ListOfValues( ValuesOnAllObjects( alpha_1 ) );
    deduped_141_1 := ValuesOfPreSheaf( Source( beta_1 ) );
    deduped_140_1 := DefiningTripleOfUnderlyingQuiver( deduped_146_1 );
    deduped_139_1 := ValuesOfPreSheaf( Target( beta_1 ) );
    deduped_138_1 := DataTables( deduped_146_1 );
    deduped_137_1 := ValuesOfPreSheaf( Source( alpha_1 ) );
    deduped_136_1 := deduped_138_1[2];
    deduped_135_1 := deduped_140_1[1];
    deduped_134_1 := deduped_138_1[1];
    deduped_133_1 := [ 1 .. deduped_135_1 ];
    deduped_132_1 := [ 0 .. deduped_135_1 - 1 ];
    deduped_131_1 := [ 0 .. deduped_140_1[2] - 1 ];
    deduped_130_1 := [ 0 .. deduped_134_1[2] - 1 ];
    deduped_78_1 := deduped_143_1[1];
    deduped_129_1 := List( deduped_132_1, function ( o_2 )
            return Cardinality( deduped_78_1[1 + o_2] );
        end );
    deduped_48_1 := List( ValuesOfPreSheaf( Target( alpha_1 ) )[1], Cardinality );
    deduped_128_1 := List( deduped_132_1, function ( o_2 )
            return deduped_48_1[1 + o_2];
        end );
    deduped_3_1 := deduped_137_1[1];
    deduped_127_1 := List( deduped_132_1, function ( o_2 )
            return Cardinality( deduped_3_1[1 + o_2] );
        end );
    deduped_49_1 := List( deduped_141_1[1], Cardinality );
    deduped_126_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_48_1[deduped_1_2], deduped_49_1[deduped_1_2] );
          end ) );
    deduped_1_1 := List( ValuesOfPreSheaf( Source( alpha_1 ) )[1], Cardinality );
    deduped_125_1 := Sum( List( deduped_132_1, function ( o_2 )
              return deduped_1_1[1 + o_2];
          end ) );
    deduped_124_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_49_1[deduped_1_2] );
          end ) );
    deduped_123_1 := [ 1 .. deduped_125_1 ];
    deduped_122_1 := Product( deduped_126_1 );
    deduped_121_1 := Product( deduped_124_1 );
    deduped_2_1 := List( ValuesOfPreSheaf( Target( beta_1 ) )[1], Cardinality );
    deduped_120_1 := Product( Concatenation( List( deduped_132_1, function ( o_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + o_2;
                return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
            end ) ) );
    deduped_10_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_7_1 := deduped_140_1[3];
    deduped_9_1 := List( deduped_131_1, function ( m_2 )
            return Int( deduped_7_1[1 + m_2][1] );
        end );
    deduped_8_1 := List( deduped_131_1, function ( m_2 )
            return Int( deduped_7_1[1 + m_2][2] );
        end );
    deduped_5_1 := List( [ 0 .. deduped_134_1[1] - 1 ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_146_1, IndexOfObject, i_2 );
        end );
    deduped_80_1 := List( deduped_131_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( m_2 );
            deduped_1_2 := Cardinality( deduped_78_1[1 + deduped_8_1[deduped_2_2]] );
            return PairOfIntAndList( CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( deduped_10_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[1 + deduped_9_1[deduped_2_2]] ) ) ) ) );
        end );
    deduped_119_1 := [ 0 .. Sum( List( deduped_131_1, function ( i_2 )
                    return deduped_80_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_11_1 := List( deduped_131_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( m_2 );
            deduped_1_2 := Cardinality( deduped_3_1[1 + deduped_8_1[deduped_2_2]] );
            return PairOfIntAndList( CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( deduped_10_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[1 + deduped_9_1[deduped_2_2]] ) ) ) ) );
        end );
    deduped_118_1 := [ 0 .. Sum( List( deduped_131_1, function ( i_2 )
                    return deduped_11_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_117_1 := [ 1 .. Sum( List( deduped_131_1, function ( m_2 )
                  return Cardinality( deduped_78_1[1 + deduped_8_1[1 + m_2]] );
              end ) ) ];
    deduped_116_1 := [ 1 .. Sum( List( deduped_131_1, function ( m_2 )
                  return Cardinality( deduped_3_1[1 + deduped_8_1[1 + m_2]] );
              end ) ) ];
    deduped_115_1 := [ 0 .. deduped_122_1 - 1 ];
    deduped_114_1 := [ 0 .. deduped_121_1 - 1 ];
    deduped_79_1 := deduped_144_1[1];
    deduped_113_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_78_1[deduped_1_2] ), Cardinality( deduped_79_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] ) );
          end ) );
    deduped_6_1 := deduped_139_1[1];
    deduped_112_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_3_1[deduped_1_2] ), Cardinality( deduped_6_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] ) );
          end ) );
    deduped_111_1 := Product( deduped_113_1 );
    deduped_110_1 := Product( deduped_112_1 );
    deduped_109_1 := [ 0 .. deduped_111_1 - 1 ];
    deduped_108_1 := [ 0 .. deduped_110_1 - 1 ];
    deduped_15_1 := deduped_136_1[3];
    deduped_14_1 := deduped_136_1[2];
    deduped_17_1 := List( deduped_130_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_146_1, CreateCapCategoryObjectWithAttributes( deduped_146_1, IndexOfObject, deduped_14_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_146_1, IndexOfObject, deduped_15_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_34_1 := List( IndicesOfGeneratingMorphisms( deduped_146_1 ), function ( i_2 )
            return deduped_17_1[1 + i_2];
        end );
    deduped_43_1 := List( deduped_131_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_3_1[1 + deduped_8_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_34_1[deduped_2_2] ) );
        end );
    deduped_16_1 := deduped_136_1[1];
    deduped_13_1 := List( deduped_132_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_3_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    deduped_42_1 := List( deduped_131_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_8_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_127_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_127_1[deduped_2_2] - 1 ], List( deduped_13_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_17_1[1 + deduped_16_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_35_1 := deduped_139_1[2];
    deduped_33_1 := List( deduped_130_1, function ( i_2 )
            return deduped_15_1[1 + i_2];
        end );
    deduped_32_1 := List( deduped_130_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_146_1, IndexOfObject, deduped_15_1[1 + i_2] );
        end );
    deduped_31_1 := List( deduped_130_1, function ( i_2 )
            return deduped_14_1[1 + i_2];
        end );
    deduped_30_1 := List( deduped_130_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_146_1, IndexOfObject, deduped_14_1[1 + i_2] );
        end );
    deduped_29_1 := deduped_136_1[4];
    hoisted_45_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_43_1[deduped_5_2];
              hoisted_3_2 := List( deduped_42_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_11_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_29_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_32_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_30_1[deduped_9_3] );
                      deduped_6_3 := deduped_16_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_31_1[deduped_4_3] and deduped_8_3 = deduped_33_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_6_1[1 + IndexOfObject( Source( deduped_17_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_35_1[SafeUniquePositionProperty( deduped_34_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_27_1 := CreateCapCategoryObjectWithAttributes( deduped_145_1, Cardinality, deduped_120_1 );
    deduped_24_1 := Sum( deduped_127_1 );
    deduped_21_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_3_1[deduped_1_2] ), deduped_6_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] );
          end ) );
    hoisted_44_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_42_1[deduped_3_2][1];
              hoisted_1_2 := deduped_43_1[deduped_3_2][1];
              return List( [ 0 .. deduped_11_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_112_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_112_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_110_1, deduped_4_3, deduped_5_3 * Product( deduped_112_1{[ deduped_6_3 + 1 .. deduped_24_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_27_1, deduped_21_1[deduped_6_3], AsList, List( deduped_108_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_110_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_46_1 := List( deduped_118_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_44_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_45_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_38_1 := Concatenation( List( deduped_131_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_3_1[1 + deduped_8_1[deduped_1_2]] ), Cardinality( deduped_6_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_1_2]] )] ) );
          end ) );
    deduped_39_1 := List( deduped_116_1, function ( j_2 )
            return Product( hoisted_38_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_47_1 := List( deduped_108_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_116_1, function ( j_3 )
                    return hoisted_46_1[j_3][hoisted_1_2] * deduped_39_1[j_3];
                end );
        end );
    hoisted_19_1 := deduped_137_1[2];
    deduped_20_1 := List( deduped_131_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_19_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_17_1[1 + deduped_16_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_2_2]] )]] ) );
        end );
    deduped_18_1 := List( deduped_131_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_127_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_127_1[deduped_2_2] - 1 ], List( deduped_13_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_17_1[1 + deduped_16_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_36_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_20_1[deduped_5_2];
              hoisted_3_2 := List( deduped_18_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_11_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_29_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_32_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_30_1[deduped_9_3] );
                      deduped_6_3 := deduped_16_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_31_1[deduped_4_3] and deduped_8_3 = deduped_33_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_6_1[1 + IndexOfObject( Source( deduped_17_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_35_1[SafeUniquePositionProperty( deduped_34_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_28_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_18_1[deduped_3_2][1];
              hoisted_1_2 := deduped_20_1[deduped_3_2][1];
              return List( [ 0 .. deduped_11_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_112_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_112_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_110_1, deduped_4_3, deduped_5_3 * Product( deduped_112_1{[ deduped_6_3 + 1 .. deduped_24_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_27_1, deduped_21_1[deduped_6_3], AsList, List( deduped_108_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_110_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_37_1 := List( deduped_118_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_28_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_36_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_41_1 := List( deduped_108_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_116_1, function ( j_3 )
                    return hoisted_37_1[j_3][hoisted_1_2] * deduped_39_1[j_3];
                end );
        end );
    hoisted_107_1 := Filtered( [ 0 .. deduped_120_1 - 1 ], function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return hoisted_41_1[deduped_1_2] = hoisted_47_1[deduped_1_2];
        end );
    hoisted_57_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
          end ) );
    hoisted_58_1 := List( deduped_123_1, function ( j_2 )
            return Product( hoisted_57_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_50_1 := List( ValuesOnAllObjects( beta_1 ), AsList );
    hoisted_51_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], hoisted_50_1[deduped_1_2] );
          end ) );
    hoisted_56_1 := List( deduped_123_1, function ( i_2 )
            local hoisted_3_2, hoisted_4_2, deduped_5_2, deduped_6_2;
            deduped_6_2 := deduped_124_1[i_2];
            deduped_5_2 := Product( deduped_124_1{[ 1 .. i_2 - 1 ]} );
            hoisted_4_2 := hoisted_51_1[i_2];
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_121_1, deduped_5_2, deduped_6_2 * Product( deduped_124_1{[ i_2 + 1 .. deduped_125_1 ]} ) );
            return List( deduped_114_1, function ( i_3 )
                    return hoisted_4_2[1 + RemIntWithDomain( QuoIntWithDomain( i_3, deduped_5_2, deduped_121_1 ), deduped_6_2, hoisted_3_2 )];
                end );
        end );
    hoisted_77_1 := List( deduped_114_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_123_1, function ( j_3 )
                    return hoisted_56_1[j_3][hoisted_1_2] * hoisted_58_1[j_3];
                end );
        end );
    hoisted_76_1 := List( deduped_123_1, function ( j_2 )
            return Product( deduped_124_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_72_1 := Sum( deduped_128_1 );
    hoisted_64_1 := List( deduped_142_1, Source );
    hoisted_63_1 := List( deduped_142_1, AsList );
    deduped_65_1 := List( deduped_132_1, function ( o_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + o_2;
            return NTuple( 2, hoisted_63_1[deduped_1_2], ListWithIdenticalEntries( Cardinality( hoisted_64_1[deduped_1_2] ), deduped_17_1[1 + deduped_16_1[deduped_1_2]] ) );
        end );
    deduped_60_1 := List( deduped_132_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_1_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    hoisted_74_1 := Concatenation( List( deduped_133_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := Sum( deduped_128_1{[ 1 .. i_2 - 1 ]} );
              hoisted_2_2 := [ deduped_3_2 .. deduped_3_2 + deduped_128_1[i_2] - 1 ];
              hoisted_1_2 := deduped_65_1[i_2][1];
              return List( [ 0 .. deduped_60_1[i_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_126_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_126_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_122_1, deduped_4_3, deduped_5_3 * Product( deduped_126_1{[ deduped_6_3 + 1 .. hoisted_72_1 ]} ) );
                      return List( deduped_115_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_122_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_67_1 := List( deduped_141_1[2], AsList );
    hoisted_66_1 := List( deduped_132_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_48_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    hoisted_68_1 := Concatenation( List( deduped_133_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2;
              deduped_4_2 := deduped_65_1[i_2];
              hoisted_3_2 := List( hoisted_66_1[i_2][2], function ( objC_3 )
                      return deduped_16_1[1 + IndexOfObject( objC_3 )];
                  end );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_60_1[i_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3;
                      deduped_10_3 := 1 + i_3;
                      deduped_9_3 := deduped_29_1[1 + hoisted_1_2[deduped_10_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_10_3]]];
                      deduped_8_3 := 1 + deduped_9_3;
                      deduped_7_3 := deduped_33_1[deduped_8_3];
                      deduped_6_3 := deduped_31_1[deduped_8_3];
                      deduped_5_3 := deduped_16_1[1 + deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_6_3 = deduped_31_1[deduped_4_3] and deduped_7_3 = deduped_33_1[deduped_4_3] then
                                      return deduped_9_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_49_1[1 + IndexOfObject( deduped_30_1[deduped_8_3] )] - 1 ];
                      else
                          return hoisted_67_1[SafeUniquePositionProperty( deduped_34_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_6_3 and IndexOfObject( Range( mor_4 ) ) = deduped_7_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_9_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_61_1 := CreateCapCategoryObjectWithAttributes( deduped_145_1, Cardinality, Product( Concatenation( List( deduped_132_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_48_1[deduped_1_2], deduped_49_1[deduped_1_2] );
              end ) ) ) );
    hoisted_62_1 := Concatenation( List( deduped_133_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_60_1[i_2][1], deduped_61_1 );
          end ) );
    hoisted_75_1 := List( [ 0 .. Sum( List( deduped_133_1, function ( i_2 )
                      return deduped_60_1[i_2][1];
                  end ) ) - 1 ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_68_1[deduped_3_2];
            hoisted_1_2 := hoisted_74_1[deduped_3_2];
            return List( [ 0 .. Cardinality( hoisted_62_1[deduped_3_2] ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_106_1 := List( deduped_115_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return hoisted_77_1[1 + Sum( deduped_123_1, function ( j_3 )
                       return hoisted_75_1[j_3][hoisted_1_2] * hoisted_76_1[j_3];
                   end )];
        end );
    deduped_100_1 := List( deduped_131_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_78_1[1 + deduped_8_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_34_1[deduped_2_2] ) );
        end );
    deduped_82_1 := List( deduped_132_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_78_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    deduped_99_1 := List( deduped_131_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_8_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_129_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_129_1[deduped_2_2] - 1 ], List( deduped_82_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_17_1[1 + deduped_16_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_92_1 := deduped_144_1[2];
    hoisted_102_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_100_1[deduped_5_2];
              hoisted_3_2 := List( deduped_99_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_80_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_29_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_32_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_30_1[deduped_9_3] );
                      deduped_6_3 := deduped_16_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_31_1[deduped_4_3] and deduped_8_3 = deduped_33_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_79_1[1 + IndexOfObject( Source( deduped_17_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_92_1[SafeUniquePositionProperty( deduped_34_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_89_1 := Sum( deduped_129_1 );
    deduped_86_1 := Concatenation( List( deduped_132_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_78_1[deduped_1_2] ), deduped_79_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] );
          end ) );
    hoisted_101_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_99_1[deduped_3_2][1];
              hoisted_1_2 := deduped_100_1[deduped_3_2][1];
              return List( [ 0 .. deduped_80_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_113_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_113_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_111_1, deduped_4_3, deduped_5_3 * Product( deduped_113_1{[ deduped_6_3 + 1 .. deduped_89_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_61_1, deduped_86_1[deduped_6_3], AsList, List( deduped_109_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_111_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_103_1 := List( deduped_119_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_101_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_102_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_95_1 := Concatenation( List( deduped_131_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_78_1[1 + deduped_8_1[deduped_1_2]] ), Cardinality( deduped_79_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_1_2]] )] ) );
          end ) );
    deduped_96_1 := List( deduped_117_1, function ( j_2 )
            return Product( hoisted_95_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_104_1 := List( deduped_109_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_117_1, function ( j_3 )
                    return hoisted_103_1[j_3][hoisted_1_2] * deduped_96_1[j_3];
                end );
        end );
    hoisted_84_1 := deduped_143_1[2];
    deduped_85_1 := List( deduped_131_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_84_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_17_1[1 + deduped_16_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_2_2]] )]] ) );
        end );
    deduped_83_1 := List( deduped_131_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_129_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_129_1[deduped_2_2] - 1 ], List( deduped_82_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_17_1[1 + deduped_16_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_93_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_85_1[deduped_5_2];
              hoisted_3_2 := List( deduped_83_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_80_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_29_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_32_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_30_1[deduped_9_3] );
                      deduped_6_3 := deduped_16_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_31_1[deduped_4_3] and deduped_8_3 = deduped_33_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_79_1[1 + IndexOfObject( Source( deduped_17_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_92_1[SafeUniquePositionProperty( deduped_34_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_91_1 := Concatenation( List( deduped_131_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_83_1[deduped_3_2][1];
              hoisted_1_2 := deduped_85_1[deduped_3_2][1];
              return List( [ 0 .. deduped_80_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_113_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_113_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_111_1, deduped_4_3, deduped_5_3 * Product( deduped_113_1{[ deduped_6_3 + 1 .. deduped_89_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_145_1, deduped_61_1, deduped_86_1[deduped_6_3], AsList, List( deduped_109_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_111_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_94_1 := List( deduped_119_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_91_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_93_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_98_1 := List( deduped_109_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_117_1, function ( j_3 )
                    return hoisted_94_1[j_3][hoisted_1_2] * deduped_96_1[j_3];
                end );
        end );
    hoisted_105_1 := Filtered( deduped_115_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return hoisted_98_1[deduped_1_2] = hoisted_104_1[deduped_1_2];
        end );
    return CreateCapCategoryMorphismWithAttributes( deduped_145_1, source_1, range_1, AsList, List( [ 0 .. Cardinality( source_1 ) - 1 ], function ( x_2 )
              return -1 + BigInt( SafePosition( hoisted_107_1, CAP_JIT_INCOMPLETE_LOGIC( hoisted_106_1[1 + hoisted_105_1[1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 )]] ) ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.HomomorphismStructureOnMorphismsWithGivenObjects :=
        
########
function ( cat_1, source_1, alpha_1, beta_1, range_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, hoisted_11_1, deduped_12_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_25_1, deduped_28_1, hoisted_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, hoisted_37_1, hoisted_38_1, hoisted_39_1, deduped_40_1, hoisted_42_1, deduped_43_1, deduped_44_1, hoisted_45_1, hoisted_46_1, hoisted_47_1, hoisted_48_1, hoisted_51_1, hoisted_52_1, hoisted_57_1, hoisted_58_1, hoisted_59_1, deduped_61_1, deduped_64_1, hoisted_65_1, hoisted_66_1, hoisted_67_1, deduped_68_1, hoisted_69_1, hoisted_70_1, hoisted_71_1, hoisted_75_1, hoisted_77_1, hoisted_78_1, hoisted_79_1, hoisted_80_1, deduped_81_1, deduped_82_1, hoisted_83_1, deduped_84_1, deduped_86_1, deduped_87_1, hoisted_88_1, deduped_89_1, deduped_90_1, deduped_93_1, hoisted_95_1, deduped_96_1, hoisted_97_1, hoisted_98_1, hoisted_99_1, deduped_100_1, hoisted_102_1, deduped_103_1, deduped_104_1, hoisted_105_1, hoisted_106_1, hoisted_107_1, hoisted_108_1, hoisted_109_1, hoisted_110_1, hoisted_111_1, hoisted_112_1, deduped_113_1, deduped_114_1, deduped_115_1, deduped_116_1, deduped_117_1, deduped_118_1, deduped_119_1, deduped_120_1, deduped_121_1, deduped_122_1, deduped_123_1, deduped_124_1, deduped_125_1, deduped_126_1, deduped_127_1, deduped_128_1, deduped_129_1, deduped_130_1, deduped_131_1, deduped_132_1, deduped_133_1, deduped_134_1, deduped_135_1, deduped_136_1, deduped_137_1, deduped_138_1, deduped_139_1, deduped_140_1, deduped_141_1, deduped_142_1, deduped_143_1, deduped_144_1, deduped_145_1, deduped_146_1, deduped_147_1, deduped_148_1, deduped_149_1, deduped_150_1, deduped_151_1, deduped_152_1, deduped_153_1, deduped_154_1, deduped_155_1;
    deduped_155_1 := Source( cat_1 );
    deduped_154_1 := Target( cat_1 );
    deduped_153_1 := ValuesOfPreSheaf( Source( beta_1 ) );
    deduped_152_1 := ValuesOfPreSheaf( Target( alpha_1 ) );
    deduped_151_1 := ListOfValues( ValuesOnAllObjects( alpha_1 ) );
    deduped_150_1 := ValuesOfPreSheaf( Source( beta_1 ) );
    deduped_149_1 := DefiningTripleOfUnderlyingQuiver( deduped_155_1 );
    deduped_148_1 := ValuesOfPreSheaf( Target( beta_1 ) );
    deduped_147_1 := DataTables( deduped_155_1 );
    deduped_146_1 := ValuesOfPreSheaf( Source( alpha_1 ) );
    deduped_145_1 := [ 0 .. Cardinality( source_1 ) - 1 ];
    deduped_144_1 := deduped_147_1[2];
    deduped_143_1 := deduped_149_1[1];
    deduped_142_1 := deduped_147_1[1];
    deduped_141_1 := [ 1 .. deduped_143_1 ];
    deduped_140_1 := List( deduped_150_1[1], Cardinality );
    deduped_139_1 := List( ValuesOfPreSheaf( Target( alpha_1 ) )[1], Cardinality );
    deduped_138_1 := [ 0 .. deduped_143_1 - 1 ];
    deduped_137_1 := [ 0 .. deduped_149_1[2] - 1 ];
    deduped_136_1 := [ 0 .. deduped_142_1[2] - 1 ];
    deduped_81_1 := deduped_152_1[1];
    deduped_135_1 := List( deduped_138_1, function ( o_2 )
            return Cardinality( deduped_81_1[1 + o_2] );
        end );
    deduped_134_1 := List( deduped_138_1, function ( o_2 )
            return deduped_139_1[1 + o_2];
        end );
    deduped_3_1 := deduped_146_1[1];
    deduped_133_1 := List( deduped_138_1, function ( o_2 )
            return Cardinality( deduped_3_1[1 + o_2] );
        end );
    deduped_132_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_139_1[deduped_1_2], deduped_140_1[deduped_1_2] );
          end ) );
    deduped_1_1 := List( ValuesOfPreSheaf( Source( alpha_1 ) )[1], Cardinality );
    deduped_131_1 := Sum( List( deduped_138_1, function ( o_2 )
              return deduped_1_1[1 + o_2];
          end ) );
    deduped_130_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_140_1[deduped_1_2] );
          end ) );
    deduped_129_1 := [ 1 .. deduped_131_1 ];
    deduped_128_1 := Product( deduped_132_1 );
    deduped_127_1 := Product( Concatenation( List( deduped_138_1, function ( o_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + o_2;
                return ListWithIdenticalEntries( deduped_139_1[deduped_1_2], deduped_140_1[deduped_1_2] );
            end ) ) );
    deduped_126_1 := Product( deduped_130_1 );
    deduped_2_1 := List( ValuesOfPreSheaf( Target( beta_1 ) )[1], Cardinality );
    deduped_125_1 := Product( Concatenation( List( deduped_138_1, function ( o_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + o_2;
                return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
            end ) ) );
    deduped_10_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_7_1 := deduped_149_1[3];
    deduped_9_1 := List( deduped_137_1, function ( m_2 )
            return Int( deduped_7_1[1 + m_2][1] );
        end );
    deduped_8_1 := List( deduped_137_1, function ( m_2 )
            return Int( deduped_7_1[1 + m_2][2] );
        end );
    deduped_5_1 := List( [ 0 .. deduped_142_1[1] - 1 ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_155_1, IndexOfObject, i_2 );
        end );
    hoisted_83_1 := List( deduped_137_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_81_1[1 + deduped_8_1[deduped_2_2]] );
            return CreateCapCategoryObjectWithAttributes( deduped_10_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[1 + deduped_9_1[deduped_2_2]] ) ) );
        end );
    deduped_84_1 := List( deduped_137_1, function ( m_2 )
            return PairOfIntAndList( hoisted_83_1[1 + m_2] );
        end );
    deduped_124_1 := [ 0 .. Sum( List( deduped_137_1, function ( i_2 )
                    return deduped_84_1[1 + i_2][1];
                end ) ) - 1 ];
    hoisted_11_1 := List( deduped_137_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_3_1[1 + deduped_8_1[deduped_2_2]] );
            return CreateCapCategoryObjectWithAttributes( deduped_10_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[1 + deduped_9_1[deduped_2_2]] ) ) );
        end );
    deduped_12_1 := List( deduped_137_1, function ( m_2 )
            return PairOfIntAndList( hoisted_11_1[1 + m_2] );
        end );
    deduped_123_1 := [ 0 .. Sum( List( deduped_137_1, function ( i_2 )
                    return deduped_12_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_122_1 := [ 1 .. Sum( List( deduped_137_1, function ( m_2 )
                  return Cardinality( deduped_81_1[1 + deduped_8_1[1 + m_2]] );
              end ) ) ];
    deduped_121_1 := [ 1 .. Sum( List( deduped_137_1, function ( m_2 )
                  return Cardinality( deduped_3_1[1 + deduped_8_1[1 + m_2]] );
              end ) ) ];
    deduped_120_1 := [ 0 .. deduped_128_1 - 1 ];
    deduped_119_1 := [ 0 .. deduped_126_1 - 1 ];
    deduped_82_1 := deduped_153_1[1];
    deduped_118_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_81_1[deduped_1_2] ), Cardinality( deduped_82_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] ) );
          end ) );
    deduped_6_1 := deduped_148_1[1];
    deduped_117_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_3_1[deduped_1_2] ), Cardinality( deduped_6_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] ) );
          end ) );
    deduped_116_1 := Product( deduped_118_1 );
    deduped_115_1 := Product( deduped_117_1 );
    deduped_114_1 := [ 0 .. deduped_116_1 - 1 ];
    deduped_113_1 := [ 0 .. deduped_115_1 - 1 ];
    deduped_16_1 := deduped_144_1[3];
    deduped_15_1 := deduped_144_1[2];
    deduped_18_1 := List( deduped_136_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_155_1, CreateCapCategoryObjectWithAttributes( deduped_155_1, IndexOfObject, deduped_15_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_155_1, IndexOfObject, deduped_16_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_35_1 := List( IndicesOfGeneratingMorphisms( deduped_155_1 ), function ( i_2 )
            return deduped_18_1[1 + i_2];
        end );
    deduped_44_1 := List( deduped_137_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_3_1[1 + deduped_8_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_35_1[deduped_2_2] ) );
        end );
    deduped_17_1 := deduped_144_1[1];
    deduped_14_1 := List( deduped_138_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_3_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    deduped_43_1 := List( deduped_137_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_8_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_133_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_133_1[deduped_2_2] - 1 ], List( deduped_14_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_36_1 := deduped_148_1[2];
    deduped_34_1 := List( deduped_136_1, function ( i_2 )
            return deduped_16_1[1 + i_2];
        end );
    deduped_33_1 := List( deduped_136_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_155_1, IndexOfObject, deduped_16_1[1 + i_2] );
        end );
    deduped_32_1 := List( deduped_136_1, function ( i_2 )
            return deduped_15_1[1 + i_2];
        end );
    deduped_31_1 := List( deduped_136_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_155_1, IndexOfObject, deduped_15_1[1 + i_2] );
        end );
    deduped_30_1 := deduped_144_1[4];
    hoisted_46_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_44_1[deduped_5_2];
              hoisted_3_2 := List( deduped_43_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_12_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_6_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_36_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_28_1 := CreateCapCategoryObjectWithAttributes( deduped_154_1, Cardinality, deduped_125_1 );
    deduped_25_1 := Sum( deduped_133_1 );
    deduped_22_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_3_1[deduped_1_2] ), deduped_6_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] );
          end ) );
    hoisted_45_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_43_1[deduped_3_2][1];
              hoisted_1_2 := deduped_44_1[deduped_3_2][1];
              return List( [ 0 .. deduped_12_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_117_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_117_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_115_1, deduped_4_3, deduped_5_3 * Product( deduped_117_1{[ deduped_6_3 + 1 .. deduped_25_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_28_1, deduped_22_1[deduped_6_3], AsList, List( deduped_113_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_115_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_47_1 := List( deduped_123_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_45_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_46_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_39_1 := Concatenation( List( deduped_137_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_3_1[1 + deduped_8_1[deduped_1_2]] ), Cardinality( deduped_6_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_1_2]] )] ) );
          end ) );
    deduped_40_1 := List( deduped_121_1, function ( j_2 )
            return Product( hoisted_39_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_48_1 := List( deduped_113_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_121_1, function ( j_3 )
                    return hoisted_47_1[j_3][hoisted_1_2] * deduped_40_1[j_3];
                end );
        end );
    hoisted_20_1 := deduped_146_1[2];
    deduped_21_1 := List( deduped_137_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_20_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_2_2]] )]] ) );
        end );
    deduped_19_1 := List( deduped_137_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_133_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_133_1[deduped_2_2] - 1 ], List( deduped_14_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_37_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_21_1[deduped_5_2];
              hoisted_3_2 := List( deduped_19_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_12_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_6_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_36_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_29_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_19_1[deduped_3_2][1];
              hoisted_1_2 := deduped_21_1[deduped_3_2][1];
              return List( [ 0 .. deduped_12_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_117_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_117_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_115_1, deduped_4_3, deduped_5_3 * Product( deduped_117_1{[ deduped_6_3 + 1 .. deduped_25_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_28_1, deduped_22_1[deduped_6_3], AsList, List( deduped_113_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_115_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_38_1 := List( deduped_123_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_29_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_37_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_42_1 := List( deduped_113_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_121_1, function ( j_3 )
                    return hoisted_38_1[j_3][hoisted_1_2] * deduped_40_1[j_3];
                end );
        end );
    hoisted_112_1 := Filtered( [ 0 .. deduped_125_1 - 1 ], function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return hoisted_42_1[deduped_1_2] = hoisted_48_1[deduped_1_2];
        end );
    hoisted_58_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
          end ) );
    hoisted_59_1 := List( deduped_129_1, function ( j_2 )
            return Product( hoisted_58_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_51_1 := List( ValuesOnAllObjects( beta_1 ), AsList );
    hoisted_52_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], hoisted_51_1[deduped_1_2] );
          end ) );
    hoisted_57_1 := List( deduped_129_1, function ( i_2 )
            local hoisted_3_2, hoisted_4_2, deduped_5_2, deduped_6_2;
            deduped_6_2 := deduped_130_1[i_2];
            deduped_5_2 := Product( deduped_130_1{[ 1 .. i_2 - 1 ]} );
            hoisted_4_2 := hoisted_52_1[i_2];
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_126_1, deduped_5_2, deduped_6_2 * Product( deduped_130_1{[ i_2 + 1 .. deduped_131_1 ]} ) );
            return List( deduped_119_1, function ( i_3 )
                    return hoisted_4_2[1 + RemIntWithDomain( QuoIntWithDomain( i_3, deduped_5_2, deduped_126_1 ), deduped_6_2, hoisted_3_2 )];
                end );
        end );
    hoisted_80_1 := List( deduped_119_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_129_1, function ( j_3 )
                    return hoisted_57_1[j_3][hoisted_1_2] * hoisted_59_1[j_3];
                end );
        end );
    hoisted_79_1 := List( deduped_129_1, function ( j_2 )
            return Product( deduped_130_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_75_1 := Sum( deduped_134_1 );
    hoisted_67_1 := List( deduped_151_1, Source );
    hoisted_66_1 := List( deduped_151_1, AsList );
    deduped_68_1 := List( deduped_138_1, function ( o_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + o_2;
            return NTuple( 2, hoisted_66_1[deduped_1_2], ListWithIdenticalEntries( Cardinality( hoisted_67_1[deduped_1_2] ), deduped_18_1[1 + deduped_17_1[deduped_1_2]] ) );
        end );
    deduped_61_1 := List( deduped_138_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_1_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    hoisted_77_1 := Concatenation( List( deduped_141_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := Sum( deduped_134_1{[ 1 .. i_2 - 1 ]} );
              hoisted_2_2 := [ deduped_3_2 .. deduped_3_2 + deduped_134_1[i_2] - 1 ];
              hoisted_1_2 := deduped_68_1[i_2][1];
              return List( [ 0 .. deduped_61_1[i_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_132_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_132_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_128_1, deduped_4_3, deduped_5_3 * Product( deduped_132_1{[ deduped_6_3 + 1 .. hoisted_75_1 ]} ) );
                      return List( deduped_120_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_128_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_70_1 := List( deduped_150_1[2], AsList );
    hoisted_69_1 := List( deduped_138_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_139_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    hoisted_71_1 := Concatenation( List( deduped_141_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2;
              deduped_4_2 := deduped_68_1[i_2];
              hoisted_3_2 := List( hoisted_69_1[i_2][2], function ( objC_3 )
                      return deduped_17_1[1 + IndexOfObject( objC_3 )];
                  end );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_61_1[i_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3;
                      deduped_10_3 := 1 + i_3;
                      deduped_9_3 := deduped_30_1[1 + hoisted_1_2[deduped_10_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_10_3]]];
                      deduped_8_3 := 1 + deduped_9_3;
                      deduped_7_3 := deduped_34_1[deduped_8_3];
                      deduped_6_3 := deduped_32_1[deduped_8_3];
                      deduped_5_3 := deduped_17_1[1 + deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_6_3 = deduped_32_1[deduped_4_3] and deduped_7_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_9_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_140_1[1 + IndexOfObject( deduped_31_1[deduped_8_3] )] - 1 ];
                      else
                          return hoisted_70_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_6_3 and IndexOfObject( Range( mor_4 ) ) = deduped_7_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_9_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_64_1 := CreateCapCategoryObjectWithAttributes( deduped_154_1, Cardinality, deduped_127_1 );
    hoisted_65_1 := Concatenation( List( deduped_141_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_61_1[i_2][1], deduped_64_1 );
          end ) );
    hoisted_78_1 := List( [ 0 .. Sum( List( deduped_141_1, function ( i_2 )
                      return deduped_61_1[i_2][1];
                  end ) ) - 1 ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_71_1[deduped_3_2];
            hoisted_1_2 := hoisted_77_1[deduped_3_2];
            return List( [ 0 .. Cardinality( hoisted_65_1[deduped_3_2] ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_110_1 := List( deduped_120_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return hoisted_80_1[1 + Sum( deduped_129_1, function ( j_3 )
                       return hoisted_78_1[j_3][hoisted_1_2] * hoisted_79_1[j_3];
                   end )];
        end );
    deduped_104_1 := List( deduped_137_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_81_1[1 + deduped_8_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_35_1[deduped_2_2] ) );
        end );
    deduped_86_1 := List( deduped_138_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_81_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_5_1[deduped_2_2] ) );
        end );
    deduped_103_1 := List( deduped_137_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_8_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_135_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_135_1[deduped_2_2] - 1 ], List( deduped_86_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_96_1 := deduped_153_1[2];
    hoisted_106_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_104_1[deduped_5_2];
              hoisted_3_2 := List( deduped_103_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_84_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_82_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_96_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_93_1 := Sum( deduped_135_1 );
    deduped_90_1 := Concatenation( List( deduped_138_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_81_1[deduped_1_2] ), deduped_82_1[1 + IndexOfObject( deduped_5_1[deduped_1_2] )] );
          end ) );
    hoisted_105_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_103_1[deduped_3_2][1];
              hoisted_1_2 := deduped_104_1[deduped_3_2][1];
              return List( [ 0 .. deduped_84_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_118_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_118_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_116_1, deduped_4_3, deduped_5_3 * Product( deduped_118_1{[ deduped_6_3 + 1 .. deduped_93_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_64_1, deduped_90_1[deduped_6_3], AsList, List( deduped_114_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_116_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_107_1 := List( deduped_124_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_105_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_106_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_99_1 := Concatenation( List( deduped_137_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_81_1[1 + deduped_8_1[deduped_1_2]] ), Cardinality( deduped_82_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_1_2]] )] ) );
          end ) );
    deduped_100_1 := List( deduped_122_1, function ( j_2 )
            return Product( hoisted_99_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_108_1 := List( deduped_114_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_122_1, function ( j_3 )
                    return hoisted_107_1[j_3][hoisted_1_2] * deduped_100_1[j_3];
                end );
        end );
    hoisted_88_1 := deduped_152_1[2];
    deduped_89_1 := List( deduped_137_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_88_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( deduped_5_1[1 + deduped_9_1[deduped_2_2]] )]] ) );
        end );
    deduped_87_1 := List( deduped_137_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_135_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_135_1[deduped_2_2] - 1 ], List( deduped_86_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_97_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_89_1[deduped_5_2];
              hoisted_3_2 := List( deduped_87_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_84_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_82_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_96_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_95_1 := Concatenation( List( deduped_137_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_87_1[deduped_3_2][1];
              hoisted_1_2 := deduped_89_1[deduped_3_2][1];
              return List( [ 0 .. deduped_84_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_118_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_118_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_116_1, deduped_4_3, deduped_5_3 * Product( deduped_118_1{[ deduped_6_3 + 1 .. deduped_93_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_154_1, deduped_64_1, deduped_90_1[deduped_6_3], AsList, List( deduped_114_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_116_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_98_1 := List( deduped_124_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_95_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_97_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_102_1 := List( deduped_114_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_122_1, function ( j_3 )
                    return hoisted_98_1[j_3][hoisted_1_2] * deduped_100_1[j_3];
                end );
        end );
    hoisted_109_1 := Filtered( [ 0 .. deduped_127_1 - 1 ], function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return hoisted_102_1[deduped_1_2] = hoisted_108_1[deduped_1_2];
        end );
    hoisted_111_1 := List( deduped_145_1, function ( i_2 )
            return hoisted_110_1[1 + hoisted_109_1[1 + i_2]];
        end );
    return CreateCapCategoryMorphismWithAttributes( deduped_154_1, source_1, range_1, AsList, List( deduped_145_1, function ( x_2 )
              return -1 + BigInt( SafePosition( hoisted_112_1, hoisted_111_1[1 + x_2] ) );
          end ) );
end
########
        
    ;
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local deduped_3_1, deduped_4_1, deduped_6_1, deduped_9_1, deduped_13_1, deduped_14_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, hoisted_20_1, deduped_21_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, hoisted_29_1, deduped_30_1, deduped_31_1, deduped_34_1, hoisted_36_1, deduped_37_1, deduped_38_1, deduped_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1, hoisted_44_1, hoisted_45_1, hoisted_46_1, deduped_47_1, hoisted_49_1, deduped_50_1, deduped_51_1, hoisted_52_1, hoisted_53_1, hoisted_54_1, hoisted_55_1, hoisted_56_1, deduped_57_1, deduped_58_1, deduped_59_1, deduped_60_1, deduped_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1, deduped_69_1, deduped_70_1, deduped_71_1, deduped_72_1, deduped_73_1, deduped_74_1, deduped_75_1, deduped_76_1, deduped_77_1, deduped_78_1, deduped_79_1, deduped_80_1, deduped_81_1, deduped_82_1;
    deduped_82_1 := ValuesOfPreSheaf( source_1 );
    deduped_81_1 := Target( cat_1 );
    deduped_80_1 := Source( cat_1 );
    deduped_79_1 := DataTables( deduped_80_1 );
    deduped_78_1 := ValuesOfPreSheaf( range_1 )[1];
    deduped_77_1 := ValuesOfPreSheaf( source_1 )[1];
    deduped_76_1 := DefiningTripleOfUnderlyingQuiver( deduped_80_1 );
    deduped_75_1 := deduped_79_1[2];
    deduped_74_1 := deduped_79_1[1];
    deduped_73_1 := ListOfValues( deduped_77_1 );
    deduped_72_1 := deduped_76_1[1];
    deduped_71_1 := [ 1 .. deduped_72_1 ];
    deduped_70_1 := [ 0 .. deduped_76_1[1] - 1 ];
    deduped_69_1 := [ 0 .. deduped_76_1[2] - 1 ];
    deduped_68_1 := [ 0 .. deduped_72_1 - 1 ];
    deduped_67_1 := [ 0 .. deduped_74_1[2] - 1 ];
    deduped_66_1 := [ 0 .. deduped_74_1[1] - 1 ];
    deduped_14_1 := deduped_82_1[1];
    deduped_65_1 := List( deduped_70_1, function ( o_2 )
            return Cardinality( deduped_14_1[1 + o_2] );
        end );
    hoisted_20_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_17_1 := deduped_76_1[3];
    deduped_19_1 := List( deduped_69_1, function ( m_2 )
            return Int( deduped_17_1[1 + m_2][1] );
        end );
    deduped_18_1 := List( deduped_69_1, function ( m_2 )
            return Int( deduped_17_1[1 + m_2][2] );
        end );
    deduped_16_1 := List( deduped_66_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_80_1, IndexOfObject, i_2 );
        end );
    deduped_21_1 := List( deduped_69_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( m_2 );
            deduped_1_2 := Cardinality( deduped_14_1[1 + deduped_18_1[deduped_2_2]] );
            return PairOfIntAndList( CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( hoisted_20_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_16_1[1 + deduped_19_1[deduped_2_2]] ) ) ) ) );
        end );
    deduped_64_1 := [ 0 .. Sum( List( deduped_69_1, function ( i_2 )
                    return deduped_21_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_4_1 := List( deduped_78_1, Cardinality );
    deduped_3_1 := List( deduped_77_1, Cardinality );
    deduped_63_1 := Concatenation( List( deduped_68_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_3_1[deduped_1_2], deduped_4_1[1 + deduped_66_1[deduped_1_2]] );
          end ) );
    deduped_62_1 := [ 1 .. Sum( List( deduped_69_1, function ( m_2 )
                  return Cardinality( deduped_14_1[1 + deduped_18_1[1 + m_2]] );
              end ) ) ];
    deduped_61_1 := Product( deduped_63_1 );
    deduped_60_1 := Concatenation( List( deduped_70_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_14_1[deduped_1_2] ), Cardinality( deduped_78_1[1 + IndexOfObject( deduped_16_1[deduped_1_2] )] ) );
          end ) );
    deduped_59_1 := [ 0 .. deduped_61_1 - 1 ];
    deduped_58_1 := Product( deduped_60_1 );
    deduped_57_1 := [ 0 .. deduped_58_1 - 1 ];
    deduped_25_1 := deduped_75_1[3];
    deduped_24_1 := deduped_75_1[2];
    deduped_27_1 := List( deduped_67_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_80_1, CreateCapCategoryObjectWithAttributes( deduped_80_1, IndexOfObject, deduped_24_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_80_1, IndexOfObject, deduped_25_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_42_1 := List( IndicesOfGeneratingMorphisms( deduped_80_1 ), function ( i_2 )
            return deduped_27_1[1 + i_2];
        end );
    deduped_51_1 := List( deduped_69_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_14_1[1 + deduped_18_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_42_1[deduped_2_2] ) );
        end );
    deduped_26_1 := deduped_75_1[1];
    deduped_23_1 := List( deduped_70_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_14_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_16_1[deduped_2_2] ) );
        end );
    deduped_50_1 := List( deduped_69_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_18_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_65_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_65_1[deduped_2_2] - 1 ], List( deduped_23_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_27_1[1 + deduped_26_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_43_1 := ValuesOfPreSheaf( range_1 )[2];
    deduped_41_1 := List( deduped_67_1, function ( i_2 )
            return deduped_25_1[1 + i_2];
        end );
    deduped_40_1 := List( deduped_67_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_80_1, IndexOfObject, deduped_25_1[1 + i_2] );
        end );
    deduped_39_1 := List( deduped_67_1, function ( i_2 )
            return deduped_24_1[1 + i_2];
        end );
    deduped_38_1 := List( deduped_67_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_80_1, IndexOfObject, deduped_24_1[1 + i_2] );
        end );
    deduped_37_1 := deduped_75_1[4];
    hoisted_53_1 := Concatenation( List( deduped_69_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_51_1[deduped_5_2];
              hoisted_3_2 := List( deduped_50_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_21_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_37_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_40_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_38_1[deduped_9_3] );
                      deduped_6_3 := deduped_26_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_39_1[deduped_4_3] and deduped_8_3 = deduped_41_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_78_1[1 + IndexOfObject( Source( deduped_27_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_81_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_43_1[SafeUniquePositionProperty( deduped_42_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_34_1 := Sum( deduped_65_1 );
    deduped_31_1 := Concatenation( List( deduped_70_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_14_1[deduped_1_2] ), deduped_78_1[1 + IndexOfObject( deduped_16_1[deduped_1_2] )] );
          end ) );
    deduped_13_1 := CreateCapCategoryObjectWithAttributes( deduped_81_1, Cardinality, Product( Concatenation( List( deduped_68_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_3_1[deduped_1_2], deduped_4_1[deduped_1_2] );
              end ) ) ) );
    hoisted_52_1 := Concatenation( List( deduped_69_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_50_1[deduped_3_2][1];
              hoisted_1_2 := deduped_51_1[deduped_3_2][1];
              return List( [ 0 .. deduped_21_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_60_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_60_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_58_1, deduped_4_3, deduped_5_3 * Product( deduped_60_1{[ deduped_6_3 + 1 .. deduped_34_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_81_1, deduped_13_1, deduped_31_1[deduped_6_3], AsList, List( deduped_57_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_58_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_54_1 := List( deduped_64_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_52_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_53_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_46_1 := Concatenation( List( deduped_69_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_14_1[1 + deduped_18_1[deduped_1_2]] ), Cardinality( deduped_78_1[1 + IndexOfObject( deduped_16_1[1 + deduped_19_1[deduped_1_2]] )] ) );
          end ) );
    deduped_47_1 := List( deduped_62_1, function ( j_2 )
            return Product( hoisted_46_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_55_1 := List( deduped_57_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_62_1, function ( j_3 )
                    return hoisted_54_1[j_3][hoisted_1_2] * deduped_47_1[j_3];
                end );
        end );
    hoisted_29_1 := deduped_82_1[2];
    deduped_30_1 := List( deduped_69_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_29_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_27_1[1 + deduped_26_1[1 + IndexOfObject( deduped_16_1[1 + deduped_19_1[deduped_2_2]] )]] ) );
        end );
    deduped_28_1 := List( deduped_69_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_19_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_65_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_65_1[deduped_2_2] - 1 ], List( deduped_23_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_27_1[1 + deduped_26_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_44_1 := Concatenation( List( deduped_69_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_30_1[deduped_5_2];
              hoisted_3_2 := List( deduped_28_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_21_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_37_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_40_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_38_1[deduped_9_3] );
                      deduped_6_3 := deduped_26_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_39_1[deduped_4_3] and deduped_8_3 = deduped_41_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_78_1[1 + IndexOfObject( Source( deduped_27_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_81_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_43_1[SafeUniquePositionProperty( deduped_42_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_36_1 := Concatenation( List( deduped_69_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_28_1[deduped_3_2][1];
              hoisted_1_2 := deduped_30_1[deduped_3_2][1];
              return List( [ 0 .. deduped_21_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_60_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_60_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_58_1, deduped_4_3, deduped_5_3 * Product( deduped_60_1{[ deduped_6_3 + 1 .. deduped_34_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_81_1, deduped_13_1, deduped_31_1[deduped_6_3], AsList, List( deduped_57_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_58_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_45_1 := List( deduped_64_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_36_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_44_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_49_1 := List( deduped_57_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_62_1, function ( j_3 )
                    return hoisted_45_1[j_3][hoisted_1_2] * deduped_47_1[j_3];
                end );
        end );
    hoisted_56_1 := 1 + Filtered( deduped_59_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + x_2;
                return hoisted_49_1[deduped_1_2] = hoisted_55_1[deduped_1_2];
            end )[1 + AsList( alpha_1 )[1 + CAP_JIT_INCOMPLETE_LOGIC( [ 0 .. Cardinality( Source( alpha_1 ) ) - 1 ][1] )]];
    deduped_6_1 := List( deduped_73_1, Cardinality );
    deduped_9_1 := List( deduped_71_1, function ( i_2 )
            return Product( deduped_63_1{[ 1 + Sum( deduped_6_1{[ 1 .. i_2 - 1 ]} ) .. Sum( deduped_6_1{[ 1 .. i_2 ]} ) ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, ValuesOnAllObjects, List( deduped_71_1, function ( i_2 )
              local hoisted_3_2, hoisted_4_2, hoisted_6_2, deduped_7_2, deduped_8_2, deduped_9_2, deduped_10_2, deduped_11_2, deduped_12_2;
              deduped_12_2 := CAP_JIT_INCOMPLETE_LOGIC( i_2 );
              deduped_11_2 := deduped_78_1[i_2];
              deduped_10_2 := deduped_73_1[i_2];
              deduped_9_2 := deduped_9_1[deduped_12_2];
              deduped_8_2 := Cardinality( deduped_10_2 );
              deduped_7_2 := Product( deduped_9_1{[ 1 .. deduped_12_2 - 1 ]} );
              hoisted_6_2 := Cardinality( deduped_11_2 );
              hoisted_3_2 := DivIntWithGivenQuotient( deduped_61_1, deduped_7_2, deduped_9_2 * Product( deduped_9_1{[ deduped_12_2 + 1 .. deduped_72_1 ]} ) );
              hoisted_4_2 := CAP_JIT_INCOMPLETE_LOGIC( AsList( CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryMorphismWithAttributes( deduped_81_1, deduped_13_1, CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( deduped_81_1, Cardinality, Product( deduped_63_1{[ 1 + Sum( deduped_6_1{[ 1 .. deduped_12_2 - 1 ]} ) .. Sum( deduped_6_1{[ 1 .. deduped_12_2 ]} ) ]} ) ) ), AsList, List( deduped_59_1, function ( i_3 )
                                return RemIntWithDomain( QuoIntWithDomain( i_3, deduped_7_2, deduped_61_1 ), deduped_9_2, hoisted_3_2 );
                            end ) ) ) )[hoisted_56_1] );
              return CreateCapCategoryMorphismWithAttributes( deduped_81_1, deduped_10_2, deduped_11_2, AsList, List( [ 0 .. deduped_8_2 - 1 ], function ( i_3 )
                        return DigitInPositionalNotation( hoisted_4_2, i_3, deduped_8_2, hoisted_6_2 );
                    end ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism :=
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local deduped_3_1, deduped_4_1, deduped_6_1, hoisted_9_1, deduped_10_1, deduped_14_1, hoisted_15_1, deduped_16_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, hoisted_22_1, hoisted_23_1, deduped_24_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, hoisted_32_1, deduped_33_1, deduped_34_1, deduped_37_1, hoisted_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1, deduped_44_1, deduped_45_1, deduped_46_1, hoisted_47_1, hoisted_48_1, hoisted_49_1, deduped_50_1, hoisted_52_1, deduped_53_1, deduped_54_1, hoisted_55_1, hoisted_56_1, hoisted_57_1, hoisted_58_1, hoisted_59_1, hoisted_60_1, hoisted_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1, deduped_69_1, deduped_70_1, deduped_71_1, deduped_72_1, deduped_73_1, deduped_74_1, deduped_75_1, deduped_76_1, deduped_77_1, deduped_78_1, deduped_79_1, deduped_80_1, deduped_81_1, deduped_82_1, deduped_83_1, deduped_84_1, deduped_85_1, deduped_86_1, deduped_87_1;
    deduped_87_1 := ValuesOfPreSheaf( source_1 );
    deduped_86_1 := Target( cat_1 );
    deduped_85_1 := Source( cat_1 );
    deduped_84_1 := DataTables( deduped_85_1 );
    deduped_83_1 := ValuesOfPreSheaf( range_1 )[1];
    deduped_82_1 := ValuesOfPreSheaf( source_1 )[1];
    deduped_81_1 := DefiningTripleOfUnderlyingQuiver( deduped_85_1 );
    deduped_80_1 := deduped_84_1[2];
    deduped_79_1 := deduped_84_1[1];
    deduped_78_1 := ListOfValues( deduped_82_1 );
    deduped_77_1 := deduped_81_1[1];
    deduped_76_1 := [ 1 .. deduped_77_1 ];
    deduped_75_1 := [ 0 .. deduped_81_1[1] - 1 ];
    deduped_74_1 := [ 0 .. deduped_81_1[2] - 1 ];
    deduped_73_1 := [ 0 .. deduped_77_1 - 1 ];
    deduped_72_1 := [ 0 .. deduped_79_1[2] - 1 ];
    deduped_71_1 := [ 0 .. deduped_79_1[1] - 1 ];
    deduped_16_1 := deduped_87_1[1];
    deduped_70_1 := List( deduped_75_1, function ( o_2 )
            return Cardinality( deduped_16_1[1 + o_2] );
        end );
    hoisted_22_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_19_1 := deduped_81_1[3];
    deduped_21_1 := List( deduped_74_1, function ( m_2 )
            return Int( deduped_19_1[1 + m_2][1] );
        end );
    deduped_20_1 := List( deduped_74_1, function ( m_2 )
            return Int( deduped_19_1[1 + m_2][2] );
        end );
    deduped_18_1 := List( deduped_71_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_85_1, IndexOfObject, i_2 );
        end );
    hoisted_23_1 := List( deduped_74_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_16_1[1 + deduped_20_1[deduped_2_2]] );
            return CreateCapCategoryObjectWithAttributes( hoisted_22_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_18_1[1 + deduped_21_1[deduped_2_2]] ) ) );
        end );
    deduped_24_1 := List( deduped_74_1, function ( m_2 )
            return PairOfIntAndList( hoisted_23_1[1 + m_2] );
        end );
    deduped_69_1 := [ 0 .. Sum( List( deduped_74_1, function ( i_2 )
                    return deduped_24_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_4_1 := List( deduped_83_1, Cardinality );
    deduped_3_1 := List( deduped_82_1, Cardinality );
    deduped_68_1 := Concatenation( List( deduped_73_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_3_1[deduped_1_2], deduped_4_1[1 + deduped_71_1[deduped_1_2]] );
          end ) );
    deduped_67_1 := [ 1 .. Sum( List( deduped_74_1, function ( m_2 )
                  return Cardinality( deduped_16_1[1 + deduped_20_1[1 + m_2]] );
              end ) ) ];
    deduped_66_1 := Product( deduped_68_1 );
    deduped_65_1 := Concatenation( List( deduped_75_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_16_1[deduped_1_2] ), Cardinality( deduped_83_1[1 + IndexOfObject( deduped_18_1[deduped_1_2] )] ) );
          end ) );
    deduped_64_1 := [ 0 .. deduped_66_1 - 1 ];
    deduped_63_1 := Product( deduped_65_1 );
    deduped_62_1 := [ 0 .. deduped_63_1 - 1 ];
    hoisted_61_1 := [ 0 .. Cardinality( Source( alpha_1 ) ) - 1 ];
    deduped_28_1 := deduped_80_1[3];
    deduped_27_1 := deduped_80_1[2];
    deduped_30_1 := List( deduped_72_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_85_1, CreateCapCategoryObjectWithAttributes( deduped_85_1, IndexOfObject, deduped_27_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_85_1, IndexOfObject, deduped_28_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_45_1 := List( IndicesOfGeneratingMorphisms( deduped_85_1 ), function ( i_2 )
            return deduped_30_1[1 + i_2];
        end );
    deduped_54_1 := List( deduped_74_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_16_1[1 + deduped_20_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_45_1[deduped_2_2] ) );
        end );
    deduped_29_1 := deduped_80_1[1];
    deduped_26_1 := List( deduped_75_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_16_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_18_1[deduped_2_2] ) );
        end );
    deduped_53_1 := List( deduped_74_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_20_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_70_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_70_1[deduped_2_2] - 1 ], List( deduped_26_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_30_1[1 + deduped_29_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_46_1 := ValuesOfPreSheaf( range_1 )[2];
    deduped_44_1 := List( deduped_72_1, function ( i_2 )
            return deduped_28_1[1 + i_2];
        end );
    deduped_43_1 := List( deduped_72_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_85_1, IndexOfObject, deduped_28_1[1 + i_2] );
        end );
    deduped_42_1 := List( deduped_72_1, function ( i_2 )
            return deduped_27_1[1 + i_2];
        end );
    deduped_41_1 := List( deduped_72_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_85_1, IndexOfObject, deduped_27_1[1 + i_2] );
        end );
    deduped_40_1 := deduped_80_1[4];
    hoisted_56_1 := Concatenation( List( deduped_74_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_54_1[deduped_5_2];
              hoisted_3_2 := List( deduped_53_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_24_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_40_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_43_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_41_1[deduped_9_3] );
                      deduped_6_3 := deduped_29_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_42_1[deduped_4_3] and deduped_8_3 = deduped_44_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_83_1[1 + IndexOfObject( Source( deduped_30_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_46_1[SafeUniquePositionProperty( deduped_45_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_37_1 := Sum( deduped_70_1 );
    deduped_34_1 := Concatenation( List( deduped_75_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_16_1[deduped_1_2] ), deduped_83_1[1 + IndexOfObject( deduped_18_1[deduped_1_2] )] );
          end ) );
    deduped_14_1 := CreateCapCategoryObjectWithAttributes( deduped_86_1, Cardinality, Product( Concatenation( List( deduped_73_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_3_1[deduped_1_2], deduped_4_1[deduped_1_2] );
              end ) ) ) );
    hoisted_55_1 := Concatenation( List( deduped_74_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_53_1[deduped_3_2][1];
              hoisted_1_2 := deduped_54_1[deduped_3_2][1];
              return List( [ 0 .. deduped_24_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_65_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_65_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_63_1, deduped_4_3, deduped_5_3 * Product( deduped_65_1{[ deduped_6_3 + 1 .. deduped_37_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_14_1, deduped_34_1[deduped_6_3], AsList, List( deduped_62_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_63_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_57_1 := List( deduped_69_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_55_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_56_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_49_1 := Concatenation( List( deduped_74_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_16_1[1 + deduped_20_1[deduped_1_2]] ), Cardinality( deduped_83_1[1 + IndexOfObject( deduped_18_1[1 + deduped_21_1[deduped_1_2]] )] ) );
          end ) );
    deduped_50_1 := List( deduped_67_1, function ( j_2 )
            return Product( hoisted_49_1{[ 1 .. j_2 - 1 ]} );
        end );
    hoisted_58_1 := List( deduped_62_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_67_1, function ( j_3 )
                    return hoisted_57_1[j_3][hoisted_1_2] * deduped_50_1[j_3];
                end );
        end );
    hoisted_32_1 := deduped_87_1[2];
    deduped_33_1 := List( deduped_74_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_32_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_30_1[1 + deduped_29_1[1 + IndexOfObject( deduped_18_1[1 + deduped_21_1[deduped_2_2]] )]] ) );
        end );
    deduped_31_1 := List( deduped_74_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_21_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_70_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_70_1[deduped_2_2] - 1 ], List( deduped_26_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_30_1[1 + deduped_29_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_47_1 := Concatenation( List( deduped_74_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_33_1[deduped_5_2];
              hoisted_3_2 := List( deduped_31_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_24_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_40_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_43_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_41_1[deduped_9_3] );
                      deduped_6_3 := deduped_29_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_42_1[deduped_4_3] and deduped_8_3 = deduped_44_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_83_1[1 + IndexOfObject( Source( deduped_30_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_46_1[SafeUniquePositionProperty( deduped_45_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_39_1 := Concatenation( List( deduped_74_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_31_1[deduped_3_2][1];
              hoisted_1_2 := deduped_33_1[deduped_3_2][1];
              return List( [ 0 .. deduped_24_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_65_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_65_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_63_1, deduped_4_3, deduped_5_3 * Product( deduped_65_1{[ deduped_6_3 + 1 .. deduped_37_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_14_1, deduped_34_1[deduped_6_3], AsList, List( deduped_62_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_63_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_48_1 := List( deduped_69_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_39_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_47_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_52_1 := List( deduped_62_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_67_1, function ( j_3 )
                    return hoisted_48_1[j_3][hoisted_1_2] * deduped_50_1[j_3];
                end );
        end );
    hoisted_60_1 := Filtered( deduped_64_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return hoisted_52_1[deduped_1_2] = hoisted_58_1[deduped_1_2];
        end );
    hoisted_59_1 := AsList( alpha_1 );
    deduped_6_1 := List( deduped_78_1, Cardinality );
    deduped_10_1 := List( deduped_76_1, function ( i_2 )
            return Product( deduped_68_1{[ 1 + Sum( deduped_6_1{[ 1 .. i_2 - 1 ]} ) .. Sum( deduped_6_1{[ 1 .. i_2 ]} ) ]} );
        end );
    hoisted_9_1 := List( deduped_76_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_86_1, Cardinality, Product( deduped_68_1{[ 1 + Sum( deduped_6_1{[ 1 .. i_2 - 1 ]} ) .. Sum( deduped_6_1{[ 1 .. i_2 ]} ) ]} ) );
        end );
    hoisted_15_1 := List( deduped_76_1, function ( i_2 )
            local hoisted_3_2, deduped_4_2, deduped_5_2;
            deduped_5_2 := deduped_10_1[i_2];
            deduped_4_2 := Product( deduped_10_1{[ 1 .. i_2 - 1 ]} );
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_66_1, deduped_4_2, deduped_5_2 * Product( deduped_10_1{[ i_2 + 1 .. deduped_77_1 ]} ) );
            return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_14_1, hoisted_9_1[i_2], AsList, List( deduped_64_1, function ( i_3 )
                      return RemIntWithDomain( QuoIntWithDomain( i_3, deduped_4_2, deduped_66_1 ), deduped_5_2, hoisted_3_2 );
                  end ) );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, ValuesOnAllObjects, List( deduped_76_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_4_2, deduped_5_2, deduped_6_2, deduped_7_2;
              deduped_7_2 := deduped_83_1[i_2];
              deduped_6_2 := deduped_78_1[i_2];
              deduped_5_2 := Cardinality( deduped_6_2 );
              hoisted_4_2 := Cardinality( deduped_7_2 );
              hoisted_1_2 := AsList( hoisted_15_1[i_2] );
              hoisted_2_2 := List( hoisted_61_1, function ( i_3 )
                        return hoisted_1_2[1 + hoisted_60_1[1 + hoisted_59_1[1 + i_3]]];
                    end )[1];
              return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_6_2, deduped_7_2, AsList, List( [ 0 .. deduped_5_2 - 1 ], function ( i_3 )
                        return DigitInPositionalNotation( hoisted_2_2, i_3, deduped_5_2, hoisted_4_2 );
                    end ) );
          end ) );
end
########
        
    ;
    
    ##
    AddMorphismsOfExternalHom( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, hoisted_11_1, deduped_12_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_25_1, deduped_28_1, hoisted_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, hoisted_37_1, hoisted_38_1, hoisted_39_1, deduped_40_1, deduped_42_1, deduped_43_1, deduped_44_1, hoisted_45_1, hoisted_46_1, hoisted_47_1, deduped_48_1, deduped_51_1, deduped_53_1, hoisted_57_1, hoisted_58_1, deduped_60_1, deduped_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1, deduped_69_1, deduped_70_1, deduped_71_1, deduped_72_1, deduped_73_1, deduped_74_1, deduped_75_1, deduped_76_1, deduped_77_1, deduped_78_1, deduped_79_1, deduped_80_1, deduped_81_1, deduped_82_1, deduped_83_1, deduped_84_1, deduped_85_1, deduped_86_1;
    deduped_86_1 := Target( cat_1 );
    deduped_85_1 := ValuesOfPreSheaf( arg3_1 );
    deduped_84_1 := ValuesOfPreSheaf( arg2_1 );
    deduped_83_1 := Source( cat_1 );
    deduped_82_1 := ValuesOfPreSheaf( arg3_1 )[1];
    deduped_81_1 := DataTables( deduped_83_1 );
    deduped_80_1 := ValuesOfPreSheaf( arg2_1 )[1];
    deduped_79_1 := DefiningTripleOfUnderlyingQuiver( deduped_83_1 );
    deduped_78_1 := ListOfValues( deduped_80_1 );
    deduped_77_1 := deduped_81_1[2];
    deduped_76_1 := deduped_81_1[1];
    deduped_75_1 := deduped_79_1[1];
    deduped_74_1 := [ 1 .. deduped_75_1 ];
    deduped_73_1 := [ 0 .. deduped_79_1[1] - 1 ];
    deduped_72_1 := [ 0 .. deduped_79_1[2] - 1 ];
    deduped_71_1 := [ 0 .. deduped_75_1 - 1 ];
    deduped_70_1 := [ 0 .. deduped_76_1[2] - 1 ];
    deduped_69_1 := [ 0 .. deduped_76_1[1] - 1 ];
    deduped_4_1 := deduped_84_1[1];
    deduped_68_1 := List( deduped_73_1, function ( o_2 )
            return Cardinality( deduped_4_1[1 + o_2] );
        end );
    hoisted_11_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_8_1 := deduped_79_1[3];
    deduped_10_1 := List( deduped_72_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][1] );
        end );
    deduped_9_1 := List( deduped_72_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][2] );
        end );
    deduped_6_1 := List( deduped_69_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_83_1, IndexOfObject, i_2 );
        end );
    deduped_12_1 := List( deduped_72_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( m_2 );
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return PairOfIntAndList( CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( hoisted_11_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[1 + deduped_10_1[deduped_2_2]] ) ) ) ) );
        end );
    deduped_67_1 := [ 0 .. Sum( List( deduped_72_1, function ( i_2 )
                    return deduped_12_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_3_1 := List( deduped_82_1, Cardinality );
    deduped_1_1 := List( deduped_80_1, Cardinality );
    deduped_66_1 := Concatenation( List( deduped_71_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_3_1[1 + deduped_69_1[deduped_1_2]] );
          end ) );
    deduped_65_1 := [ 1 .. Sum( List( deduped_72_1, function ( m_2 )
                  return Cardinality( deduped_4_1[1 + deduped_9_1[1 + m_2]] );
              end ) ) ];
    deduped_64_1 := Product( deduped_66_1 );
    deduped_7_1 := deduped_85_1[1];
    deduped_63_1 := Concatenation( List( deduped_73_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] ) );
          end ) );
    deduped_62_1 := [ 0 .. deduped_64_1 - 1 ];
    deduped_61_1 := Product( deduped_63_1 );
    deduped_60_1 := [ 0 .. deduped_61_1 - 1 ];
    deduped_16_1 := deduped_77_1[3];
    deduped_15_1 := deduped_77_1[2];
    deduped_18_1 := List( deduped_70_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_83_1, CreateCapCategoryObjectWithAttributes( deduped_83_1, IndexOfObject, deduped_15_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_83_1, IndexOfObject, deduped_16_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_35_1 := List( IndicesOfGeneratingMorphisms( deduped_83_1 ), function ( i_2 )
            return deduped_18_1[1 + i_2];
        end );
    deduped_44_1 := List( deduped_72_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_35_1[deduped_2_2] ) );
        end );
    deduped_17_1 := deduped_77_1[1];
    deduped_14_1 := List( deduped_73_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_4_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[deduped_2_2] ) );
        end );
    deduped_43_1 := List( deduped_72_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_68_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_68_1[deduped_2_2] - 1 ], List( deduped_14_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_36_1 := deduped_85_1[2];
    deduped_34_1 := List( deduped_70_1, function ( i_2 )
            return deduped_16_1[1 + i_2];
        end );
    deduped_33_1 := List( deduped_70_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_83_1, IndexOfObject, deduped_16_1[1 + i_2] );
        end );
    deduped_32_1 := List( deduped_70_1, function ( i_2 )
            return deduped_15_1[1 + i_2];
        end );
    deduped_31_1 := List( deduped_70_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_83_1, IndexOfObject, deduped_15_1[1 + i_2] );
        end );
    deduped_30_1 := deduped_77_1[4];
    hoisted_46_1 := Concatenation( List( deduped_72_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_44_1[deduped_5_2];
              hoisted_3_2 := List( deduped_43_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_12_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_36_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_28_1 := CreateCapCategoryObjectWithAttributes( deduped_86_1, Cardinality, Product( Concatenation( List( deduped_71_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_3_1[deduped_1_2] );
              end ) ) ) );
    deduped_25_1 := Sum( deduped_68_1 );
    deduped_22_1 := Concatenation( List( deduped_73_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] );
          end ) );
    hoisted_45_1 := Concatenation( List( deduped_72_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_43_1[deduped_3_2][1];
              hoisted_1_2 := deduped_44_1[deduped_3_2][1];
              return List( [ 0 .. deduped_12_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_63_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_63_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_61_1, deduped_4_3, deduped_5_3 * Product( deduped_63_1{[ deduped_6_3 + 1 .. deduped_25_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_28_1, deduped_22_1[deduped_6_3], AsList, List( deduped_60_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_61_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_47_1 := List( deduped_67_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_45_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_46_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_39_1 := Concatenation( List( deduped_72_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[1 + deduped_9_1[deduped_1_2]] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_1_2]] )] ) );
          end ) );
    deduped_40_1 := List( deduped_65_1, function ( j_2 )
            return Product( hoisted_39_1{[ 1 .. j_2 - 1 ]} );
        end );
    deduped_48_1 := List( deduped_60_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_65_1, function ( j_3 )
                    return hoisted_47_1[j_3][hoisted_1_2] * deduped_40_1[j_3];
                end );
        end );
    hoisted_20_1 := deduped_84_1[2];
    deduped_21_1 := List( deduped_72_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_20_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_2_2]] )]] ) );
        end );
    deduped_19_1 := List( deduped_72_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_10_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_68_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_68_1[deduped_2_2] - 1 ], List( deduped_14_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_18_1[1 + deduped_17_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_37_1 := Concatenation( List( deduped_72_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_21_1[deduped_5_2];
              hoisted_3_2 := List( deduped_19_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_12_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_30_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_33_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_31_1[deduped_9_3] );
                      deduped_6_3 := deduped_17_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_32_1[deduped_4_3] and deduped_8_3 = deduped_34_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_18_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_36_1[SafeUniquePositionProperty( deduped_35_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_29_1 := Concatenation( List( deduped_72_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_19_1[deduped_3_2][1];
              hoisted_1_2 := deduped_21_1[deduped_3_2][1];
              return List( [ 0 .. deduped_12_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_63_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_63_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_61_1, deduped_4_3, deduped_5_3 * Product( deduped_63_1{[ deduped_6_3 + 1 .. deduped_25_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_28_1, deduped_22_1[deduped_6_3], AsList, List( deduped_60_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_61_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_38_1 := List( deduped_67_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_29_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_37_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    deduped_42_1 := List( deduped_60_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_65_1, function ( j_3 )
                    return hoisted_38_1[j_3][hoisted_1_2] * deduped_40_1[j_3];
                end );
        end );
    hoisted_58_1 := Filtered( deduped_62_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return deduped_42_1[deduped_1_2] = deduped_48_1[deduped_1_2];
        end );
    deduped_51_1 := List( deduped_78_1, Cardinality );
    deduped_53_1 := List( deduped_74_1, function ( i_2 )
            return Product( deduped_66_1{[ 1 + Sum( deduped_51_1{[ 1 .. i_2 - 1 ]} ) .. Sum( deduped_51_1{[ 1 .. i_2 ]} ) ]} );
        end );
    hoisted_57_1 := List( deduped_74_1, function ( i_2 )
            local hoisted_3_2, deduped_4_2, deduped_5_2, deduped_6_2;
            deduped_6_2 := deduped_53_1[i_2];
            deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( i_2 );
            deduped_4_2 := Product( deduped_53_1{[ 1 .. i_2 - 1 ]} );
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_64_1, deduped_4_2, deduped_6_2 * Product( deduped_53_1{[ i_2 + 1 .. deduped_75_1 ]} ) );
            return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_28_1, CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryObjectWithAttributes( deduped_86_1, Cardinality, Product( deduped_66_1{[ 1 + Sum( deduped_51_1{[ 1 .. deduped_5_2 - 1 ]} ) .. Sum( deduped_51_1{[ 1 .. deduped_5_2 ]} ) ]} ) ) ), AsList, List( deduped_62_1, function ( i_3 )
                      return RemIntWithDomain( QuoIntWithDomain( i_3, deduped_4_2, deduped_64_1 ), deduped_6_2, hoisted_3_2 );
                  end ) );
        end );
    return List( [ 0 .. BigInt( Length( Filtered( deduped_62_1, function ( x_2 )
                          local deduped_1_2;
                          deduped_1_2 := 1 + x_2;
                          return deduped_42_1[deduped_1_2] = deduped_48_1[deduped_1_2];
                      end ) ) ) ^ BigInt( 1 ) - 1 ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + hoisted_58_1[1 + i_2];
            return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg3_1, ValuesOnAllObjects, List( deduped_74_1, function ( i_3 )
                      local hoisted_1_3, hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3;
                      deduped_6_3 := deduped_82_1[i_3];
                      deduped_5_3 := deduped_78_1[i_3];
                      deduped_4_3 := Cardinality( deduped_5_3 );
                      hoisted_3_3 := Cardinality( deduped_6_3 );
                      hoisted_1_3 := AsList( hoisted_57_1[i_3] )[hoisted_1_2];
                      return CreateCapCategoryMorphismWithAttributes( deduped_86_1, deduped_5_3, deduped_6_3, AsList, List( [ 0 .. deduped_4_3 - 1 ], function ( i_4 )
                                return DigitInPositionalNotation( hoisted_1_3, i_4, deduped_4_3, hoisted_3_3 );
                            end ) );
                  end ) );
        end );
end
########
        
    , 802 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.MorphismsOfExternalHom :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, hoisted_11_1, hoisted_12_1, deduped_13_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, hoisted_23_1, deduped_24_1, deduped_25_1, deduped_28_1, deduped_31_1, hoisted_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1, deduped_39_1, hoisted_40_1, hoisted_41_1, hoisted_42_1, deduped_43_1, deduped_45_1, deduped_46_1, deduped_47_1, hoisted_48_1, hoisted_49_1, hoisted_50_1, deduped_51_1, deduped_54_1, hoisted_56_1, deduped_57_1, hoisted_61_1, hoisted_62_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1, deduped_69_1, deduped_70_1, deduped_71_1, deduped_72_1, deduped_73_1, deduped_74_1, deduped_75_1, deduped_76_1, deduped_77_1, deduped_78_1, deduped_79_1, deduped_80_1, deduped_81_1, deduped_82_1, deduped_83_1, deduped_84_1, deduped_85_1, deduped_86_1, deduped_87_1, deduped_88_1, deduped_89_1, deduped_90_1, deduped_91_1, deduped_92_1;
    deduped_92_1 := Target( cat_1 );
    deduped_91_1 := ValuesOfPreSheaf( arg3_1 );
    deduped_90_1 := ValuesOfPreSheaf( arg2_1 );
    deduped_89_1 := Source( cat_1 );
    deduped_88_1 := ValuesOfPreSheaf( arg3_1 )[1];
    deduped_87_1 := DataTables( deduped_89_1 );
    deduped_86_1 := ValuesOfPreSheaf( arg2_1 )[1];
    deduped_85_1 := DefiningTripleOfUnderlyingQuiver( deduped_89_1 );
    deduped_84_1 := ListOfValues( deduped_86_1 );
    deduped_83_1 := deduped_87_1[2];
    deduped_82_1 := List( deduped_88_1, Cardinality );
    deduped_81_1 := deduped_87_1[1];
    deduped_80_1 := List( deduped_86_1, Cardinality );
    deduped_79_1 := deduped_85_1[1];
    deduped_78_1 := [ 1 .. deduped_79_1 ];
    deduped_77_1 := [ 0 .. deduped_85_1[1] - 1 ];
    deduped_76_1 := [ 0 .. deduped_85_1[2] - 1 ];
    deduped_75_1 := [ 0 .. deduped_79_1 - 1 ];
    deduped_74_1 := [ 0 .. deduped_81_1[2] - 1 ];
    deduped_73_1 := [ 0 .. deduped_81_1[1] - 1 ];
    deduped_4_1 := deduped_90_1[1];
    deduped_72_1 := List( deduped_77_1, function ( o_2 )
            return Cardinality( deduped_4_1[1 + o_2] );
        end );
    hoisted_11_1 := FiniteStrictCoproductCompletionOfSourceCategory( cat_1 );
    deduped_8_1 := deduped_85_1[3];
    deduped_10_1 := List( deduped_76_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][1] );
        end );
    deduped_9_1 := List( deduped_76_1, function ( m_2 )
            return Int( deduped_8_1[1 + m_2][2] );
        end );
    deduped_6_1 := List( deduped_73_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_89_1, IndexOfObject, i_2 );
        end );
    hoisted_12_1 := List( deduped_76_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return CreateCapCategoryObjectWithAttributes( hoisted_11_1, PairOfIntAndList, NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[1 + deduped_10_1[deduped_2_2]] ) ) );
        end );
    deduped_13_1 := List( deduped_76_1, function ( m_2 )
            return PairOfIntAndList( hoisted_12_1[1 + m_2] );
        end );
    deduped_71_1 := [ 0 .. Sum( List( deduped_76_1, function ( i_2 )
                    return deduped_13_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_70_1 := Concatenation( List( deduped_75_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_80_1[deduped_1_2], deduped_82_1[1 + deduped_73_1[deduped_1_2]] );
          end ) );
    deduped_69_1 := [ 1 .. Sum( List( deduped_76_1, function ( m_2 )
                  return Cardinality( deduped_4_1[1 + deduped_9_1[1 + m_2]] );
              end ) ) ];
    deduped_68_1 := Product( deduped_70_1 );
    deduped_7_1 := deduped_91_1[1];
    deduped_67_1 := Concatenation( List( deduped_77_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] ) );
          end ) );
    deduped_66_1 := [ 0 .. deduped_68_1 - 1 ];
    deduped_65_1 := Product( deduped_67_1 );
    deduped_64_1 := [ 0 .. deduped_65_1 - 1 ];
    deduped_19_1 := deduped_83_1[3];
    deduped_18_1 := deduped_83_1[2];
    deduped_21_1 := List( deduped_74_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_89_1, CreateCapCategoryObjectWithAttributes( deduped_89_1, IndexOfObject, deduped_18_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_89_1, IndexOfObject, deduped_19_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_38_1 := List( IndicesOfGeneratingMorphisms( deduped_89_1 ), function ( i_2 )
            return deduped_21_1[1 + i_2];
        end );
    deduped_47_1 := List( deduped_76_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := Cardinality( deduped_4_1[1 + deduped_9_1[deduped_2_2]] );
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_38_1[deduped_2_2] ) );
        end );
    deduped_20_1 := deduped_83_1[1];
    deduped_17_1 := List( deduped_77_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := Cardinality( deduped_4_1[deduped_2_2] );
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_6_1[deduped_2_2] ) );
        end );
    deduped_46_1 := List( deduped_76_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_72_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_72_1[deduped_2_2] - 1 ], List( deduped_17_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_21_1[1 + deduped_20_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    deduped_39_1 := deduped_91_1[2];
    deduped_37_1 := List( deduped_74_1, function ( i_2 )
            return deduped_19_1[1 + i_2];
        end );
    deduped_36_1 := List( deduped_74_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_89_1, IndexOfObject, deduped_19_1[1 + i_2] );
        end );
    deduped_35_1 := List( deduped_74_1, function ( i_2 )
            return deduped_18_1[1 + i_2];
        end );
    deduped_34_1 := List( deduped_74_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_89_1, IndexOfObject, deduped_18_1[1 + i_2] );
        end );
    deduped_33_1 := deduped_83_1[4];
    hoisted_49_1 := Concatenation( List( deduped_76_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_47_1[deduped_5_2];
              hoisted_3_2 := List( deduped_46_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_13_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_33_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_36_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_34_1[deduped_9_3] );
                      deduped_6_3 := deduped_20_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_35_1[deduped_4_3] and deduped_8_3 = deduped_37_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_21_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_92_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_39_1[SafeUniquePositionProperty( deduped_38_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_31_1 := CreateCapCategoryObjectWithAttributes( deduped_92_1, Cardinality, Product( Concatenation( List( deduped_75_1, function ( o_2 )
                  local deduped_1_2;
                  deduped_1_2 := 1 + o_2;
                  return ListWithIdenticalEntries( deduped_80_1[deduped_1_2], deduped_82_1[deduped_1_2] );
              end ) ) ) );
    deduped_28_1 := Sum( deduped_72_1 );
    deduped_25_1 := Concatenation( List( deduped_77_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[deduped_1_2] ), deduped_7_1[1 + IndexOfObject( deduped_6_1[deduped_1_2] )] );
          end ) );
    hoisted_48_1 := Concatenation( List( deduped_76_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_46_1[deduped_3_2][1];
              hoisted_1_2 := deduped_47_1[deduped_3_2][1];
              return List( [ 0 .. deduped_13_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_67_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_67_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_65_1, deduped_4_3, deduped_5_3 * Product( deduped_67_1{[ deduped_6_3 + 1 .. deduped_28_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_92_1, deduped_31_1, deduped_25_1[deduped_6_3], AsList, List( deduped_64_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_65_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_50_1 := List( deduped_71_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_48_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_49_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    hoisted_42_1 := Concatenation( List( deduped_76_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( Cardinality( deduped_4_1[1 + deduped_9_1[deduped_1_2]] ), Cardinality( deduped_7_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_1_2]] )] ) );
          end ) );
    deduped_43_1 := List( deduped_69_1, function ( j_2 )
            return Product( hoisted_42_1{[ 1 .. j_2 - 1 ]} );
        end );
    deduped_51_1 := List( deduped_64_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_69_1, function ( j_3 )
                    return hoisted_50_1[j_3][hoisted_1_2] * deduped_43_1[j_3];
                end );
        end );
    hoisted_23_1 := deduped_90_1[2];
    deduped_24_1 := List( deduped_76_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := hoisted_23_1[deduped_2_2];
            return NTuple( 2, AsList( deduped_1_2 ), ListWithIdenticalEntries( Cardinality( Source( deduped_1_2 ) ), deduped_21_1[1 + deduped_20_1[1 + IndexOfObject( deduped_6_1[1 + deduped_10_1[deduped_2_2]] )]] ) );
        end );
    deduped_22_1 := List( deduped_76_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_10_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_72_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_72_1[deduped_2_2] - 1 ], List( deduped_17_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_21_1[1 + deduped_20_1[1 + IndexOfObject( objC_3 )]];
                  end ) );
        end );
    hoisted_40_1 := Concatenation( List( deduped_76_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_24_1[deduped_5_2];
              hoisted_3_2 := List( deduped_22_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_13_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_33_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[1 + hoisted_2_2[deduped_11_3]]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := IndexOfObject( deduped_36_1[deduped_9_3] );
                      deduped_7_3 := IndexOfObject( deduped_34_1[deduped_9_3] );
                      deduped_6_3 := deduped_20_1[1 + deduped_7_3];
                      deduped_4_3 := 1 + deduped_6_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_35_1[deduped_4_3] and deduped_8_3 = deduped_37_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_6_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          deduped_5_3 := deduped_7_1[1 + IndexOfObject( Source( deduped_21_1[deduped_9_3] ) )];
                          return CreateCapCategoryMorphismWithAttributes( deduped_92_1, deduped_5_3, deduped_5_3, AsList, [ 0 .. Cardinality( deduped_5_3 ) - 1 ] );
                      else
                          return deduped_39_1[SafeUniquePositionProperty( deduped_38_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_32_1 := Concatenation( List( deduped_76_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_22_1[deduped_3_2][1];
              hoisted_1_2 := deduped_24_1[deduped_3_2][1];
              return List( [ 0 .. deduped_13_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_67_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_67_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_65_1, deduped_4_3, deduped_5_3 * Product( deduped_67_1{[ deduped_6_3 + 1 .. deduped_28_1 ]} ) );
                      return CreateCapCategoryMorphismWithAttributes( deduped_92_1, deduped_31_1, deduped_25_1[deduped_6_3], AsList, List( deduped_64_1, function ( i_4 )
                                return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_65_1 ), deduped_5_3, hoisted_3_3 );
                            end ) );
                  end );
          end ) );
    hoisted_41_1 := List( deduped_71_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
            deduped_4_2 := 1 + i_2;
            deduped_3_2 := hoisted_32_1[deduped_4_2];
            hoisted_2_2 := AsList( hoisted_40_1[deduped_4_2] );
            hoisted_1_2 := AsList( deduped_3_2 );
            return List( [ 0 .. Cardinality( Source( deduped_3_2 ) ) - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[1 + i_3]];
                end );
        end );
    deduped_45_1 := List( deduped_64_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_69_1, function ( j_3 )
                    return hoisted_41_1[j_3][hoisted_1_2] * deduped_43_1[j_3];
                end );
        end );
    hoisted_62_1 := Filtered( deduped_66_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + x_2;
            return deduped_45_1[deduped_1_2] = deduped_51_1[deduped_1_2];
        end );
    deduped_54_1 := List( deduped_84_1, Cardinality );
    deduped_57_1 := List( deduped_78_1, function ( i_2 )
            return Product( deduped_70_1{[ 1 + Sum( deduped_54_1{[ 1 .. i_2 - 1 ]} ) .. Sum( deduped_54_1{[ 1 .. i_2 ]} ) ]} );
        end );
    hoisted_56_1 := List( deduped_78_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_92_1, Cardinality, Product( deduped_70_1{[ 1 + Sum( deduped_54_1{[ 1 .. i_2 - 1 ]} ) .. Sum( deduped_54_1{[ 1 .. i_2 ]} ) ]} ) );
        end );
    hoisted_61_1 := List( deduped_78_1, function ( i_2 )
            local hoisted_3_2, deduped_4_2, deduped_5_2;
            deduped_5_2 := deduped_57_1[i_2];
            deduped_4_2 := Product( deduped_57_1{[ 1 .. i_2 - 1 ]} );
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_68_1, deduped_4_2, deduped_5_2 * Product( deduped_57_1{[ i_2 + 1 .. deduped_79_1 ]} ) );
            return CreateCapCategoryMorphismWithAttributes( deduped_92_1, deduped_31_1, hoisted_56_1[i_2], AsList, List( deduped_66_1, function ( i_3 )
                      return RemIntWithDomain( QuoIntWithDomain( i_3, deduped_4_2, deduped_68_1 ), deduped_5_2, hoisted_3_2 );
                  end ) );
        end );
    return List( [ 0 .. BigInt( Length( Filtered( deduped_66_1, function ( x_2 )
                          local deduped_1_2;
                          deduped_1_2 := 1 + x_2;
                          return deduped_45_1[deduped_1_2] = deduped_51_1[deduped_1_2];
                      end ) ) ) ^ BigInt( 1 ) - 1 ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + hoisted_62_1[1 + i_2];
            return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg3_1, ValuesOnAllObjects, List( deduped_78_1, function ( i_3 )
                      local hoisted_1_3, hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3;
                      deduped_6_3 := deduped_88_1[i_3];
                      deduped_5_3 := deduped_84_1[i_3];
                      deduped_4_3 := Cardinality( deduped_5_3 );
                      hoisted_3_3 := Cardinality( deduped_6_3 );
                      hoisted_1_3 := AsList( hoisted_61_1[i_3] )[hoisted_1_2];
                      return CreateCapCategoryMorphismWithAttributes( deduped_92_1, deduped_5_3, deduped_6_3, AsList, List( [ 0 .. deduped_4_3 - 1 ], function ( i_4 )
                                return DigitInPositionalNotation( hoisted_1_3, i_4, deduped_4_3, hoisted_3_3 );
                            end ) );
                  end ) );
        end );
end
########
        
    ;
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "PreSheavesOfCategoryFromDataTablesInSkeletalFinSetsPrecompiled", function ( quiver )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( quiver )
    local sFinSets;
    sFinSets := SkeletalCategoryOfFiniteSets(  : FinalizeCategory := true,
        overhead := true );
    return PreSheaves( CategoryFromDataTables( PathCategory( quiver : range_of_HomStructure := sFinSets,
            FinalizeCategory := true ) : FinalizeCategory := true ), sFinSets );
end;
        
        
    
    cat := category_constructor( quiver : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_PreSheavesOfCategoryFromDataTablesInSkeletalFinSetsPrecompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
