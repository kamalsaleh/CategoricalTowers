# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Implementations
#

##
InstallMethod( CategoryFromDataTables,
        "for a string, a category, and three lists",
        [ IsString, IsCapCategory, IsList, IsList, IsList ],
        
  function( name, V, data_tables, indices_of_generating_morphisms, labels )
    local C, C0, C1, s, t;
    
    C := CreateCapCategory( name,
                 IsCategoryFromDataTables,
                 IsObjectInCategoryFromDataTables,
                 IsMorphismInCategoryFromDataTables,
                 IsCapCategoryTwoCell );
    
    C!.category_as_first_argument := true;
    
    SetIndicesOfGeneratingMorphisms( C, indices_of_generating_morphisms );
    
    C!.labels := labels;
    
    SetIsFinite( C, true );
    
    SetIsEquippedWithHomomorphismStructure( C, true );
    SetRangeCategoryOfHomomorphismStructure( C, V );
    
    SetDataTablesOfCategory( C, data_tables );
    
    C0 := data_tables[1][1];
    
    ## s: C₁ → C₀
    s := data_tables[2][2];
    
    ## t: C₁ → C₀
    t := data_tables[2][3];
    
    SetDefiningPairOfUnderlyingQuiver( C, Pair( C0, List( indices_of_generating_morphisms, i -> Pair( s[1 + i], t[1 + i] ) ) ) );
    
    C!.compiler_hints :=
      rec( category_filter := IsCategoryFromDataTables,
           object_filter := IsObjectInCategoryFromDataTables and HasMapOfObject,
           morphism_filter := IsMorphismInCategoryFromDataTables and HasMapOfMorphism,
           category_attribute_names :=
           [ "DataTablesOfCategory",
             "IndicesOfGeneratingMorphisms",
             "DefiningPairOfUnderlyingQuiver",
             ] );
    
    ##
    AddObjectConstructor( C,
      function( C, obj_map )
        
        return CreateCapCategoryObjectWithAttributes( C,
                       MapOfObject, obj_map );
        
    end );
    
    ##
    AddObjectDatum( C,
      function( C, obj )
        
        return MapOfObject( obj );
        
    end );
    
    ##
    AddMorphismConstructor( C,
      function( C, source, mor_map, range )
        
        return CreateCapCategoryMorphismWithAttributes( C,
                       source,
                       range,
                       MapOfMorphism, mor_map );
        
    end );
    
    ##
    AddMorphismDatum( C,
      function( C, mor )
        
        return MapOfMorphism( mor );
        
    end );
    
    ##
    AddIsWellDefinedForObjects( C,
      function( C, obj )
        local V, C0, obj_map;
        
        V := RangeCategoryOfHomomorphismStructure( C );
        
        C0 := DataTablesOfCategory( C )[1][1];
        
        obj_map := ObjectDatum( C, obj );
        
        return IsWellDefinedForMorphisms( V, obj_map ) and
               IsTerminal( V, Source( obj_map ) ) and
               C0 = ObjectDatum( V, Range( obj_map ) );
        
    end );
    
    ##
    AddIsWellDefinedForMorphisms( C,
      function( C, mor )
        local V, C1, mor_map;
        
        V := RangeCategoryOfHomomorphismStructure( C );
        
        C1 := DataTablesOfCategory( C )[1][2];
        
        mor_map := MorphismDatum( C, mor );
        
        return IsWellDefinedForMorphisms( V, mor_map ) and
               IsTerminal( V, Source( mor_map ) ) and
               C1 = ObjectDatum( V, Range( mor_map ) );
        
    end );
    
    ##
    AddIsEqualForObjects( C,
      function( C, obj_1, obj_2 )
        local V;
        
        V := RangeCategoryOfHomomorphismStructure( C );
        
        return IsCongruentForMorphisms( V, ObjectDatum( C, obj_1 ), ObjectDatum( C, obj_2 ) );
        
    end );
    
    ##
    AddIsEqualForMorphisms( C,
      function( C, mor_1, mor_2 )
        local V;
        
        V := RangeCategoryOfHomomorphismStructure( C );
        
        return IsEqualForMorphisms( V, MorphismDatum( C, mor_1 ), MorphismDatum( C, mor_2 ) );
        
    end );
    
    ##
    AddIsCongruentForMorphisms( C,
      function( C, mor_1, mor_2 )
        local V;
        
        V := RangeCategoryOfHomomorphismStructure( C );
        
        return IsCongruentForMorphisms( V, MorphismDatum( C, mor_1 ), MorphismDatum( C, mor_2 ) );
        
    end );
    
    ##
    AddIdentityMorphism( C,
      function( C, obj )
        local o;
        
        o := AsList( ObjectDatum( C, obj ) )[1 + 0];
        
        return SetOfMorphisms( C )[1 + DataTablesOfCategory( C )[2][1][1 + o]];
        
    end );
    
    ##
    AddPreCompose( C,
      function( C, mor_1, mor_2 )
        local m1, m2;
        
        m1 := AsList( MorphismDatum( C, mor_1 ) )[1 + 0];
        m2 := AsList( MorphismDatum( C, mor_2 ) )[1 + 0];
        
        return SetOfMorphisms( C )[1 + DataTablesOfCategory( C )[2][4][1 + m1][1 + m2]];
        
    end );
    
    Assert( 0, IsIdenticalObj( V, RangeCategoryOfHomomorphismStructure( V ) ) );
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( C,
      function( C )
        
        return DistinguishedObjectOfHomomorphismStructure( RangeCategoryOfHomomorphismStructure( C ) );
        
    end );
    
    ##
    AddHomomorphismStructureOnObjects( C,
      function( C, obj_1, obj_2 )
        local V, o1, o2;
        
        V := RangeCategoryOfHomomorphismStructure( C );
        
        o1 := AsList( ObjectDatum( C, obj_1 ) )[1 + 0];
        o2 := AsList( ObjectDatum( C, obj_2 ) )[1 + 0];
        
        return ObjectConstructor( V,
                       DataTablesOfCategory( C )[2][5][1 + o1][1 + o2] );
        
    end );
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( C,
      function( C, source, mor_1, mor_2, range )
        local m1, m2;
        
        m1 := AsList( MorphismDatum( C, mor_1 ) )[1 + 0];
        m2 := AsList( MorphismDatum( C, mor_2 ) )[1 + 0];
        
        return MorphismConstructor( V,
                       source,
                       DataTablesOfCategory( C )[2][6][1 + m1][1 + m2],
                       range );
        
    end );
    
    ##
    AddInterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructureWithGivenObjects( C,
      function( C, distinguished_object, mor, range )
        local m;
        
        m := AsList( MorphismDatum( C, mor ) )[1 + 0];
        
        return MorphismConstructor( V,
                       distinguished_object,
                       DataTablesOfCategory( C )[2][7][1 + m],
                       range );
        
    end );
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( C,
      function( C, obj_1, obj_2, mor )
        local o1, o2, m;
        
        o1 := AsList( ObjectDatum( C, obj_1 ) )[1 + 0];
        o2 := AsList( ObjectDatum( C, obj_2 ) )[1 + 0];
        
        m := AsList( mor )[1 + 0];
        
        return SetOfMorphisms( C )[1 + DataTablesOfCategory( C )[2][8][1 + o1][1 + o2][1 + m]];
        
    end );
    
    #if false then
    if ValueOption( "no_precompiled_code" ) <> true then
        
        ADD_FUNCTIONS_FOR_CategoryFromDataTablesPrecompiled( C );
        
    fi;
    
    Finalize( C );
    
    return C;
    
end );

##
InstallMethodForCompilerForCAP( CreateObject,
        "for a category from data tables and an integer",
        [ IsCategoryFromDataTables, IsInt ],
        
  function( C, o )
    local V, C0, obj_map;
    
    V := RangeCategoryOfHomomorphismStructure( C );
    
    C0 := DataTablesOfCategory( C )[1][1];
    
    obj_map := MorphismConstructor( V,
                       TerminalObject( V ),
                       [ o ],
                       ObjectConstructor( V, C0 ) );
    
    return ObjectConstructor( C, obj_map );
    
end );

##
InstallMethod( \/,
        "for an integer and a category from data tables",
        [ IsInt, IsCategoryFromDataTables ],
        
  function( o, C )
    
    return CreateObject( C, o );
    
end );

##
InstallOtherMethodForCompilerForCAP( CreateMorphism,
        "for a category from data tables, two objects therein, and an integer",
        [ IsCategoryFromDataTables, IsObjectInCategoryFromDataTables, IsInt, IsObjectInCategoryFromDataTables ],
        
  function( C, source, m, range )
    local V, C1, mor_map;
    
    V := RangeCategoryOfHomomorphismStructure( C );
    
    C1 := DataTablesOfCategory( C )[1][2];
    
    mor_map := MorphismConstructor( V,
                       TerminalObject( V ),
                       [ m ],
                       ObjectConstructor( V, C1 ) );
    
    return MorphismConstructor( C,
                   source,
                   mor_map,
                   range );
    
end );

##
InstallMethod( CreateMorphism,
        "for two objects in a category from data tables and an integer",
        [ IsObjectInCategoryFromDataTables, IsInt, IsObjectInCategoryFromDataTables ],
        
  function( source, m, range )
    
    return CreateMorphism( CapCategory( source ), source, m, range );
    
end );

##
InstallMethodForCompilerForCAP( CreateMorphism,
        "for a category from data tables and an integer",
        [ IsCategoryFromDataTables, IsInt ],
        
  function( C, m )
    local data_tables, s, t;
    
    data_tables := DataTablesOfCategory( C );
    
    s := data_tables[2][2];
    t := data_tables[2][3];
    
    return CreateMorphism( C,
                   CreateObject( C, s[1 + m] ),
                   m,
                   CreateObject( C, t[1 +  m] ) );
    
end );

##
InstallMethod( \.,
        "for a category from data tables and a positive integer",
        [ IsCategoryFromDataTables, IsPosInt ],
        
  function( C, string_as_int )
    local name, labels;
    
    name := NameRNam( string_as_int );
    
    labels := C!.labels;
    
    if name in labels[1] then
        return CreateObject( C, -1 + SafePosition( labels[1], name ) );
    elif name in labels[2] then
        return CreateMorphism( C, IndicesOfGeneratingMorphisms( C )[SafePosition( labels[2], name )] );
    elif name[1] in [ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' ] then
        return CreateMorphism( C, Int( name ) );
    fi;
    
    Error( "no object or morphism of name ", name, "\n" );
    
end );

##
InstallMethodForCompilerForCAP( SetOfObjects,
        "for a category from data tables",
        [ IsCategoryFromDataTables ],
        
  function( C )
    local C0;
    
    C0 :=  DataTablesOfCategory( C )[1][1];
    
    return List( [ 0 .. C0 - 1 ], i -> CreateObject( C, i ) );
    
end );

##
InstallMethodForCompilerForCAP( SetOfMorphisms,
        "for a category from data tables",
        [ IsCategoryFromDataTables ],
        
  function( C )
    local C1;
    
    C1 := DataTablesOfCategory( C )[1][2];
    
    return List( [ 0 .. C1 - 1 ], i -> CreateMorphism( C, i ) );
    
end );

##
InstallMethodForCompilerForCAP( SetOfGeneratingMorphisms,
        "for a category from data tables",
        [ IsCategoryFromDataTables ],
        
  function( C )
    local mors;
    
    mors := SetOfMorphisms( C );
    
    return List( IndicesOfGeneratingMorphisms( C ), i -> mors[1 + i] );
    
end );

##
InstallMethod( OppositeCategoryFromDataTables,
        "for a category from data tables",
        [ IsCategoryFromDataTables ],
        
  function( C )
    local C_from_nerve, Cop, C_op;
    
    C_from_nerve := CategoryFromNerveData(
                            Name( C ),
                            NerveTruncatedInDegree2Data( C ),
                            IndicesOfGeneratingMorphisms( C ),
                            C!.labels );
    
    Cop := OppositeCategoryFromNerveData( C_from_nerve );
    
    C_op := CategoryFromDataTables(
                    Name( Cop ),
                    RangeCategoryOfHomomorphismStructure( Cop ),
                    DataTablesOfCategory( Cop ),
                    IndicesOfGeneratingMorphisms( Cop ),
                    Cop!.labels );
    
    SetOppositeCategoryFromDataTables( C_op, C );
    
    return C_op;
    
end );

####################################
#
# View, Print, and Display methods:
#
####################################

##
InstallMethod( ViewObj,
        "for an object in a category from data tables",
        [ IsObjectInCategoryFromDataTables ],
        
  function( obj )
    
    Print( "<(", CapCategory( obj )!.labels[1][1 + MapOfObject( obj )( 0 )], ")>" );
    
end );

##
InstallMethod( ViewObj,
        "for a morphism in a category from data tables",
        [ IsMorphismInCategoryFromDataTables ],
        
  function( mor )
    local C, labels, i, pos;
    
    C := CapCategory( mor );
    
    labels := C!.labels;
    
    i := MapOfMorphism( mor )( 0 );
    pos := Position( IndicesOfGeneratingMorphisms( C ), i );
    
    Print( "(", labels[1][1 + MapOfObject( Source( mor ) )( 0 )], ")" );
    Print( "-[(" );
    if pos = fail then
        Print( i );
    else
        Print( labels[2][pos] );
    fi;
    Print( ")]->" );
    Print( "(", labels[1][1 + MapOfObject( Range( mor ) )( 0 )], ")" );
    
end );

##
InstallMethod( LaTeXOutput,
        "for an object in a category from data tables",
        [ IsObjectInCategoryFromDataTables ],
        
  function( obj )
    
    return String( MapOfObject( obj )( 0 ) );
    
end );

##
InstallMethod( LaTeXOutput,
        "for a morphism in a category from data tables",
        [ IsMorphismInCategoryFromDataTables ],
        
  function( mor )
    local s;
    
    s := String( MapOfMorphism( mor )( 0 ) );
    
    if ValueOption( "OnlyDatum" ) = true then
        
        return s;
        
    fi;
    
    return Concatenation(
                   "{", LaTeXOutput( Source( mor ) ), "}",
                   "-\\left[{", s, "}\\right]\\rightarrow",
                   "{", LaTeXOutput( Range( mor ) ), "}" );
    
end );
