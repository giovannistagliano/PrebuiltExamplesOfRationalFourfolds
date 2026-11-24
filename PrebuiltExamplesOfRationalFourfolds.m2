newPackage(
    "PrebuiltExamplesOfRationalFourfolds",
    Version => "2.0",
    Date => "November 24, 2026",
    Headline => "Some prebuilt examples of rational fourfolds",
    Authors => {{Name => "Giovanni Staglianò", Email => "giovanni.stagliano@unict.it"}},
    PackageImports => {"SpecialFanoFourfolds"},
    PackageExports => {"SpecialFanoFourfolds"},
    AuxiliaryFiles => false,
    CacheExampleOutput => false,
    DebuggingMode => false,
    Reload => false
);

if SpecialFanoFourfolds.Options.Version < "2.8.1" then error "the package SpecialFanoFourfolds is outdated (required version 2.8.1 or newer); see updatePackage";

export{"associatedCastelnuovoSurface'","doubleCover"};

<< "-- warning: PrebuiltExamplesOfRationalFourfolds is deprecated; its examples are now taken from the local examples archive of SpecialFanoFourfolds (see localExamplesArchive)" << endl;

prebuiltExampleOfRationalFourfold = method();
prebuiltExampleOfRationalFourfold (String,ZZ) := (str,i) -> (
    if str === "prebuilt-example-in-P5" then return exampleOfRationalCubicFourfold i;
    if str === "prebuilt-example-in-P7" or str === "prebuilt-example" then return exampleOfRationalIntersectionsOfThreeQuadricsInP7 i;
    if str === "prebuilt-example-in-P8" then return exampleOfRationalGushelMukaiFourfold i;
    error ///Here are some of the allowed strings for specifying examples: "prebuilt-example-in-P5", "prebuilt-example-in-P7", "prebuilt-example-in-P8"///;
);

importFrom_SpecialFanoFourfolds {"WeightedSurfaceAssociatedToRationalFourfold","SurfaceAssociatedToRationalFourfold","HodgeSpecialSurface","recognize","availableExamples"};
doubleCover = method(Options => {Verify => true});
doubleCover WeightedSurfaceAssociatedToRationalFourfold := doubleCover SurfaceAssociatedToRationalFourfold := o -> U -> (
    if U.cache#?"DoubleCoverDefinedByCanonicalDivisor" then return U.cache#"DoubleCoverDefinedByCanonicalDivisor";
    X := U.cache#"Hodge-special fourfold";
    if not instance(X,IntersectionOfThreeQuadricsInP7) then error "expected a Castelnuovo surface associated to a complete intersection of 3 quadrics in PP^7";
    (mu,U',C,f) := building U;
    local h;
    if recognize X == "surf-7-1-9"
    then h = rationalMap(U,tally {(inverse f)^* C_1})
    else if recognize X == "surf-5-6-2-nodal"
    then h = rationalMap(U,tally {f C_1},3)
    else h = rationalMap(U,tally {f C_1});
    h = quadricFibration(h,Verify=>o.Verify);
    if dim target h != 2 then error "something went wrong";
    U.cache#"DoubleCoverDefinedByCanonicalDivisor" = h
);
doubleCover HodgeSpecialSurface := o -> T -> (
    if T.cache#?"doubleCover" then return T.cache#"doubleCover";
    h := map(T,1,0);
    if dim target h != 2 then error "dim target map(*,1,0) =!= 2";
    T.cache#"doubleCover" = quadricFibration(h,Verify=>o.Verify)
);
associatedCastelnuovoSurface' = method(Options => {Verbose => false, Verify => true});
associatedCastelnuovoSurface' IntersectionOfThreeQuadricsInP7 := o -> X -> (
    if X.cache#?"associatedCastelnuovoSurface'" then return X.cache#"associatedCastelnuovoSurface'";
    U := associatedCastelnuovoSurface(X,Verbose=>o.Verbose);
    if o.Verbose then (if U.cache#?"DoubleCoverDefinedByCanonicalDivisor" then << "-- getting by cache: double cover defined by canonical divisor" << endl else << "-- computing double cover defined by canonical divisor" << endl);
    g := doubleCover(U,Verify=>o.Verify);
    if o.Verbose then (if g.cache#?"discriminantLocusOfQuadricFibration" then << "-- getting by cache: discriminant of double cover" << endl else << "-- computing discriminant of double cover (this may take a very long time)" << endl);
    D := discriminant g;
    local F1; local F2;
    if o.Verify then (
        F1 = g^* point ambient D; F2 = g^* point D;
        if not (dim F1 == 0 and dim F2 == 0 and degree F1 == 2 and degree F2 == 2 and F1 == support F1 and degree support F2 == 1) then error "something went wrong";
        if o.Verbose then <<"-- test on discriminant of "<<expression g<<" successfully passed"<<endl;
    );
    K := coefficientRing X; x := local x;
    ringP2 := K[x_0..x_2];
    F := sub((ideal D)_0,vars ringP2);
    y := local y;
    R := K[gens ringP2,y,Degrees=>{3:{1},{4}}];
    T := projectiveVariety sub(ideal(y^2 - sub(F,R)),vars ring PP_K(1,1,1,4));
    T = surface(0_T,T);
    f := quadricFibration(rationalMap legacyRationalMap(ring T,ring target g,take(gens ring T,3)),Verify=>o.Verify);
    f.cache#"discriminantLocusOfQuadricFibration" = D;
    T.cache#"doubleCover" = f;
    if o.Verify then (
        F1 = f^* point ambient D; F2 = f^* point D;
        if not (dim F1 == 0 and dim F2 == 0 and degree F1 == 2 and degree F2 == 2 and F1 == support F1 and degree support F2 == 1) then error "something went wrong";
        if o.Verbose then <<"-- test on discriminant of "<<expression f<<" successfully passed"<<endl;
    );
    if o.Verbose then << "-- taking the pull-back on PP(1,1,1,4) of the image in PP^2 of the hyperplane section of U" << endl;
    Y := f^* g(U * random(1,0_U));
    if o.Verbose then <<"-- result: "<< ? Y <<endl;
    if o.Verbose then <<"-- decomposing curve in PP(1,1,1,4) by taking its image in PP^3 and then in PP^2"<<endl;
    j := parametrize ambient T;
    if degrees ring source j =!= {{1},{1},{1},{1}} then error "something went wrong";
    Y' := (inverse j) Y;
    if o.Verify then (if j Y' != Y then error "something went wrong");
    h := rationalMap (point ambient Y')_Y';
    I := kernel(map toLegacyRationalMap h,SubringLimit=>1);
    if o.Verbose then <<"-- degree of plane curve: "<<first degree I_0<<endl; 
    decI := decompose I;
    if # decI != 2 then <<"--WARNING: curve is not reducible on K"<<endl;
    if o.Verbose then <<"-- sending component in PP(1,1,1,4)"<<endl;
    if o.Verbose then <<"-- step 1/3"<<endl;
    J := projectiveVariety gens (toLegacyRationalMap h)^* first decI;
    if o.Verbose then <<"-- step 2/3"<<endl;
    J = Y'\J;
    if o.Verbose then <<"-- step 3/3"<<endl;
    Y1 := j J;
    if o.Verify then (if not (dim Y1 == 1 and isSubset(Y1,Y)) then error "something went wrong");
    if o.Verbose then (<<"-- result: "<<? Y1<<endl);
    E := D * f(Y1);
    if o.Verify then (if not (dim E == 0 and E \ support E == support E) then <<"WARNING: test on tangency not passed"<<endl else (if o.Verbose then <<"-- test on tangency successfully passed"<<endl));
    T#"CurveContainedInTheSurface" = {Y1};
    X.cache#"associatedCastelnuovoSurface'" = T
);

-- Each prebuilt example is now loaded from the local examples archive of SpecialFanoFourfolds.
-- (kind,i) => (name in the archive, fourfold type, expected class, characteristic, degree and sectional genus of the surface, discriminant)
PrebuiltExamplesInArchive = hashTable {
    ("prebuilt-example-in-P5",0) => ("0",1,CubicFourfold,10000019,9,2,42),
    ("prebuilt-example-in-P5",1) => ("1",1,CubicFourfold,10000019,8,3,14),
    ("prebuilt-example-in-P5",2) => ("2",1,CubicFourfold,10000019,7,0,26),
    ("prebuilt-example-in-P5",3) => ("3",1,CubicFourfold,10000019,10,6,38),
    ("prebuilt-example-in-P5",4) => ("4",1,CubicFourfold,10000019,7,1,26),
    ("prebuilt-example-in-P5",5) => ("5",1,CubicFourfold,10000019,8,0,38),
    ("prebuilt-example-in-P5",6) => ("6",1,CubicFourfold,10000019,11,8,14),
    ("prebuilt-example-in-P5",7) => ("7",1,CubicFourfold,10000019,10,6,14),
    ("prebuilt-example-in-P5",8) => ("8",1,CubicFourfold,10000019,13,12,14),
    ("prebuilt-example-in-P5",9) => ("9",1,CubicFourfold,10000019,14,15,14),
    ("prebuilt-example-in-P7",1) => ("1",3,IntersectionOfThreeQuadricsInP7,65521,1,0,31),
    ("prebuilt-example-in-P7",2) => ("2",3,IntersectionOfThreeQuadricsInP7,65521,9,3,47),
    ("prebuilt-example-in-P7",3) => ("3",3,IntersectionOfThreeQuadricsInP7,65521,13,8,55),
    ("prebuilt-example-in-P7",4) => ("4",3,IntersectionOfThreeQuadricsInP7,65521,11,5,55),
    ("prebuilt-example-in-P7",5) => ("5",3,IntersectionOfThreeQuadricsInP7,65521,9,2,79),
    ("prebuilt-example-in-P7",6) => ("6",3,IntersectionOfThreeQuadricsInP7,65521,11,4,87),
    ("prebuilt-example-in-P7",7) => ("7",3,IntersectionOfThreeQuadricsInP7,65521,12,6,96),
    ("prebuilt-example-in-P8",1) => ("G1",4,GushelMukaiFourfold,10000019,17,11,26),
    ("prebuilt-example-in-P8",2) => ("M1",4,GushelMukaiFourfold,65521,17,11,26)
};

expectedInvariantsString = (cls,p,d,g,D) -> "class " | toString cls | ", characteristic " | toString p | ", surface of degree " | toString d | " and sectional genus " | toString g | ", discriminant " | toString D;

prebuiltExampleFromArchive = (kind,i) -> (
    (str,n,cls,p,d,g,D) := PrebuiltExamplesInArchive#(kind,i);
    hint := "; the reference examples archive can be downloaded from GitHub with store \"@\" (warning: this replaces the current local examples archive, which can first be saved with export localExamplesArchive())";
    pre := "specialFourfold(\"" | kind | "\"," | toString i | ") corresponds to example(\"" | str | "\"," | toString n | ") of the local examples archive";
    if not member((n,str),availableExamples()) then error(pre | ", which is not present" | hint);
    X := example(str,n,Verbose=>false);
    S := surface X;
    if not (instance(X,cls) and char coefficientRing X == p and degree S == d and sectionalGenus S == g and discriminant X == D)
    then error(pre | ", which does not have the expected invariants (" | expectedInvariantsString(cls,p,d,g,D) | ")" | hint);
    X
);

exampleOfRationalCubicFourfold = memoize(i -> (
    if i < 0 or i > 9 then error "expected integer between 0 and 9";
    prebuiltExampleFromArchive("prebuilt-example-in-P5",i)
));

-- Data of the double covers defined by the canonical divisors of the associated Castelnuovo surfaces (not stored in the archive)
DoubleCoversOfIntersectionsOfThreeQuadricsInP7 = {
///(U -> (
F := U.cache#"MapToMinimalK3Surface";
t := gens ring target F;
u := local u;
ringP2 := ZZ/65521[u_0..u_2];
(image F).cache#"DoubleCoverDefinedByCanonicalDivisor" = quadricFibration rationalMap legacyRationalMap(ring image F,ringP2,{t_1^2-6457*t_0*t_2+1648*t_1*t_2+16581*t_2^2-32552*t_0*t_3+14908*t_1*t_3-14719*t_2*t_3+19563*t_3^2-22706*t_0*t_4+16284*t_1*t_4-3050*t_2*t_4+21466*t_3*t_4+22218*t_4^2, t_0*t_1+3384*t_0*t_2-8254*t_1*t_2+25908*t_2^2-3797*t_0*t_3+3681*t_1*t_3-19375*t_2*t_3-3091*t_3^2-21727*t_0*t_4+21205*t_1*t_4-31213*t_2*t_4+15228*t_3*t_4+12475*t_4^2, t_0^2+1194*t_0*t_2-16807*t_1*t_2+6305*t_2^2-27502*t_0*t_3+8557*t_1*t_3+17569*t_2*t_3-949*t_3^2+8924*t_0*t_4-2459*t_1*t_4-23159*t_2*t_4+19576*t_3*t_4-8733*t_4^2});
((image F).cache#"DoubleCoverDefinedByCanonicalDivisor").cache#"discriminantLocusOfQuadricFibration" = projectiveVariety ideal(u_0^8-5414*u_0^7*u_1+27439*u_0^6*u_1^2+1431*u_0^5*u_1^3+28932*u_0^4*u_1^4-18318*u_0^3*u_1^5-24437*u_0^2*u_1^6-22549*u_0*u_1^7+16693*u_1^8+31480*u_0^7*u_2+10938*u_0^6*u_1*u_2-24667*u_0^5*u_1^2*u_2-12371*u_0^4*u_1^3*u_2-10906*u_0^3*u_1^4*u_2+24517*u_0^2*u_1^5*u_2-14165*u_0*u_1^6*u_2-3698*u_1^7*u_2-2019*u_0^6*u_2^2-4788*u_0^5*u_1*u_2^2+14875*u_0^4*u_1^2*u_2^2+9442*u_0^3*u_1^3*u_2^2-4627*u_0^2*u_1^4*u_2^2+31786*u_0*u_1^5*u_2^2+19007*u_1^6*u_2^2+9454*u_0^5*u_2^3-3949*u_0^4*u_1*u_2^3-1276*u_0^3*u_1^2*u_2^3-14321*u_0^2*u_1^3*u_2^3-18681*u_0*u_1^4*u_2^3-14999*u_1^5*u_2^3+1008*u_0^4*u_2^4+24551*u_0^3*u_1*u_2^4+18977*u_0^2*u_1^2*u_2^4-21514*u_0*u_1^3*u_2^4-2300*u_1^4*u_2^4-10906*u_0^3*u_2^5+6666*u_0^2*u_1*u_2^5-21461*u_0*u_1^2*u_2^5-3215*u_1^3*u_2^5-22577*u_0^2*u_2^6-21781*u_0*u_1*u_2^6-32247*u_1^2*u_2^6+338*u_0*u_2^7+7459*u_1*u_2^7+15882*u_2^8);
))///,
///(U -> (
F := U.cache#"MapToMinimalK3Surface";
u := local u;
ringP2 := ZZ/65521[u_0..u_2];
t := gens ring target F;
(image F).cache#"DoubleCoverDefinedByCanonicalDivisor" = quadricFibration rationalMap legacyRationalMap(ring image F,ringP2,{t_2+18144*t_3-15166*t_4+13988*t_5-19511*t_6+20181*t_7, t_1+21702*t_3-770*t_4-16346*t_5-20028*t_6+25827*t_7, t_0+20752*t_3+18543*t_4-27221*t_5-4666*t_6+658*t_7});
((image F).cache#"DoubleCoverDefinedByCanonicalDivisor").cache#"discriminantLocusOfQuadricFibration" = projectiveVariety ideal(u_0^8-133*u_0^7*u_1+9523*u_0^6*u_1^2+4397*u_0^5*u_1^3+27954*u_0^4*u_1^4-28622*u_0^3*u_1^5+13482*u_0^2*u_1^6+12884*u_0*u_1^7-16993*u_1^8+8613*u_0^7*u_2-29622*u_0^6*u_1*u_2-8725*u_0^5*u_1^2*u_2-14123*u_0^4*u_1^3*u_2-26561*u_0^3*u_1^4*u_2-3271*u_0^2*u_1^5*u_2+16615*u_0*u_1^6*u_2-29911*u_1^7*u_2-16870*u_0^6*u_2^2-28818*u_0^5*u_1*u_2^2+31493*u_0^4*u_1^2*u_2^2+32029*u_0^3*u_1^3*u_2^2+28489*u_0^2*u_1^4*u_2^2+31170*u_0*u_1^5*u_2^2+8962*u_1^6*u_2^2-5333*u_0^5*u_2^3-15176*u_0^4*u_1*u_2^3-12496*u_0^3*u_1^2*u_2^3-825*u_0^2*u_1^3*u_2^3-23901*u_0*u_1^4*u_2^3-22670*u_1^5*u_2^3+30975*u_0^4*u_2^4-1600*u_0^3*u_1*u_2^4+1721*u_0^2*u_1^2*u_2^4-12407*u_0*u_1^3*u_2^4+4279*u_1^4*u_2^4+26414*u_0^3*u_2^5+8031*u_0^2*u_1*u_2^5+31764*u_0*u_1^2*u_2^5+30661*u_1^3*u_2^5-14554*u_0^2*u_2^6+19588*u_0*u_1*u_2^6-1925*u_1^2*u_2^6-24790*u_0*u_2^7-27818*u_1*u_2^7+21241*u_2^8);
))///,
///(U -> (
F := U.cache#"MapToMinimalK3Surface";
t := gens ring target F;
u := local u;
ringP2 := ZZ/65521[u_0..u_2];
(image F).cache#"DoubleCoverDefinedByCanonicalDivisor" = quadricFibration rationalMap legacyRationalMap(ring image F,ringP2,{t_1*t_2+19092*t_2^2-31679*t_0*t_3+23431*t_1*t_3+28358*t_2*t_3-19466*t_3^2-2159*t_0*t_4+18615*t_1*t_4-16503*t_2*t_4+31207*t_3*t_4-23942*t_4^2-30209*t_0*t_5+13366*t_1*t_5+1425*t_2*t_5-26998*t_3*t_5+13616*t_4*t_5+29605*t_5^2, t_0*t_1+5295*t_1^2+17860*t_0*t_2+17855*t_2^2+1819*t_0*t_3+16228*t_1*t_3-16845*t_2*t_3-20962*t_3^2+2*t_0*t_4+30378*t_1*t_4-9885*t_2*t_4-13405*t_3*t_4-554*t_4^2+11506*t_0*t_5-10278*t_1*t_5+27567*t_2*t_5+9939*t_3*t_5+12290*t_4*t_5+20618*t_5^2, t_0^2-30238*t_1^2-17890*t_0*t_2+25896*t_2^2+3925*t_0*t_3-17930*t_1*t_3+10914*t_2*t_3-29434*t_3^2+30945*t_0*t_4-2261*t_1*t_4+25983*t_2*t_4+9549*t_3*t_4-1262*t_4^2+32737*t_0*t_5-4823*t_1*t_5-6377*t_2*t_5-3611*t_3*t_5+15029*t_4*t_5-25833*t_5^2});
((image F).cache#"DoubleCoverDefinedByCanonicalDivisor").cache#"discriminantLocusOfQuadricFibration" = projectiveVariety ideal(u_0^8-12220*u_0^7*u_1-17581*u_0^6*u_1^2+15738*u_0^5*u_1^3-12810*u_0^4*u_1^4-3551*u_0^3*u_1^5+13281*u_0^2*u_1^6-704*u_0*u_1^7+30055*u_1^8+11353*u_0^7*u_2+5056*u_0^6*u_1*u_2-13094*u_0^5*u_1^2*u_2+5086*u_0^4*u_1^3*u_2+20235*u_0^3*u_1^4*u_2-3258*u_0^2*u_1^5*u_2-591*u_0*u_1^6*u_2-23897*u_1^7*u_2+8836*u_0^6*u_2^2-31968*u_0^5*u_1*u_2^2+651*u_0^4*u_1^2*u_2^2-26374*u_0^3*u_1^3*u_2^2+29878*u_0^2*u_1^4*u_2^2+11977*u_0*u_1^5*u_2^2+11937*u_1^6*u_2^2+9649*u_0^5*u_2^3-30783*u_0^4*u_1*u_2^3+8026*u_0^3*u_1^2*u_2^3-5090*u_0^2*u_1^3*u_2^3-24956*u_0*u_1^4*u_2^3+2188*u_1^5*u_2^3+25386*u_0^4*u_2^4-27470*u_0^3*u_1*u_2^4-2917*u_0^2*u_1^2*u_2^4+31444*u_0*u_1^3*u_2^4-16409*u_1^4*u_2^4+16514*u_0^3*u_2^5-7562*u_0^2*u_1*u_2^5-25112*u_0*u_1^2*u_2^5+31045*u_1^3*u_2^5-22724*u_0^2*u_2^6-17827*u_0*u_1*u_2^6-3327*u_1^2*u_2^6-25222*u_0*u_2^7-24489*u_1*u_2^7-30709*u_2^8);
))///,
///(U -> (
t := local t;
ringP5 := ZZ/65521[t_0..t_5];
I := ideal(t_1^2*t_2+17608*t_0*t_2^2+13163*t_1*t_2^2-7872*t_2^3-10493*t_0^2*t_3-28518*t_0*t_1*t_3+23670*t_1^2*t_3-32342*t_0*t_2*t_3+11741*t_1*t_2*t_3-25376*t_2^2*t_3+28800*t_0*t_3^2+25535*t_1*t_3^2-16414*t_2*t_3^2+25690*t_3^3+6517*t_0^2*t_4-23162*t_0*t_1*t_4+26757*t_1^2*t_4+29814*t_0*t_2*t_4+4654*t_1*t_2*t_4-15132*t_2^2*t_4-29404*t_0*t_3*t_4+1207*t_1*t_3*t_4-13406*t_2*t_3*t_4+15238*t_3^2*t_4+12790*t_0*t_4^2+16516*t_1*t_4^2-31879*t_2*t_4^2+21113*t_3*t_4^2-5679*t_4^3+22444*t_0^2*t_5-22602*t_0*t_1*t_5+11903*t_1^2*t_5-18187*t_0*t_2*t_5-6569*t_1*t_2*t_5+23370*t_2^2*t_5+4527*t_0*t_3*t_5-1887*t_1*t_3*t_5-19089*t_2*t_3*t_5+11040*t_3^2*t_5+30044*t_0*t_4*t_5-18938*t_1*t_4*t_5+18752*t_2*t_4*t_5-11665*t_3*t_4*t_5+9387*t_4^2*t_5+17577*t_0*t_5^2-10851*t_1*t_5^2-26710*t_2*t_5^2+30020*t_3*t_5^2-32066*t_4*t_5^2,t_0*t_1*t_2+25771*t_0*t_2^2-29791*t_1*t_2^2+26746*t_2^3+7285*t_0^2*t_3+21698*t_0*t_1*t_3+14476*t_1^2*t_3+22632*t_0*t_2*t_3+9046*t_1*t_2*t_3+14642*t_2^2*t_3+10116*t_0*t_3^2-21405*t_1*t_3^2+11735*t_2*t_3^2+5036*t_3^3-20299*t_0^2*t_4-15717*t_0*t_1*t_4+11423*t_1^2*t_4-22929*t_0*t_2*t_4+4984*t_1*t_2*t_4-7490*t_2^2*t_4+22824*t_0*t_3*t_4-13080*t_1*t_3*t_4-12251*t_2*t_3*t_4+20479*t_3^2*t_4+24193*t_0*t_4^2-19493*t_1*t_4^2+9512*t_2*t_4^2+30590*t_3*t_4^2-21100*t_4^3+24213*t_0^2*t_5-3692*t_0*t_1*t_5+13844*t_1^2*t_5-13647*t_0*t_2*t_5-22821*t_1*t_2*t_5-9537*t_2^2*t_5-20337*t_0*t_3*t_5+7851*t_1*t_3*t_5+21290*t_2*t_3*t_5+26690*t_3^2*t_5-12064*t_0*t_4*t_5+24190*t_1*t_4*t_5+17039*t_2*t_4*t_5+7118*t_3*t_4*t_5+21312*t_4^2*t_5-28334*t_0*t_5^2+7980*t_1*t_5^2+10136*t_2*t_5^2-16080*t_3*t_5^2-25314*t_4*t_5^2,t_0^2*t_2-14127*t_0*t_2^2-10743*t_1*t_2^2-7205*t_2^3-9665*t_0^2*t_3+22078*t_0*t_1*t_3-31042*t_1^2*t_3+6597*t_0*t_2*t_3-8278*t_1*t_2*t_3-23706*t_2^2*t_3-601*t_0*t_3^2-12161*t_1*t_3^2-29996*t_2*t_3^2-17283*t_3^3+4920*t_0^2*t_4+26198*t_0*t_1*t_4-22255*t_1^2*t_4+9705*t_0*t_2*t_4+30068*t_1*t_2*t_4-32551*t_2^2*t_4-24490*t_0*t_3*t_4+15087*t_1*t_3*t_4-31785*t_2*t_3*t_4-14036*t_3^2*t_4-24432*t_0*t_4^2-14438*t_1*t_4^2+12158*t_2*t_4^2-10142*t_3*t_4^2+437*t_4^3-14562*t_0^2*t_5-8797*t_0*t_1*t_5-15067*t_1^2*t_5-28417*t_0*t_2*t_5-7719*t_1*t_2*t_5-23767*t_2^2*t_5-11072*t_0*t_3*t_5+147*t_1*t_3*t_5-24010*t_2*t_3*t_5-4789*t_3^2*t_5+6699*t_0*t_4*t_5-27433*t_1*t_4*t_5+30905*t_2*t_4*t_5+15748*t_3*t_4*t_5+27194*t_4^2*t_5-21116*t_0*t_5^2+13836*t_1*t_5^2-18588*t_2*t_5^2-18055*t_3*t_5^2-22453*t_4*t_5^2,t_1^3-21984*t_0*t_2^2+12876*t_1*t_2^2+18082*t_2^3-8036*t_0^2*t_3-17817*t_0*t_1*t_3+22006*t_1^2*t_3+18704*t_0*t_2*t_3-11973*t_1*t_2*t_3+10151*t_2^2*t_3-9428*t_0*t_3^2+15660*t_1*t_3^2+31892*t_2*t_3^2-9116*t_3^3-26809*t_0^2*t_4+2048*t_0*t_1*t_4-21257*t_1^2*t_4-8806*t_0*t_2*t_4+16634*t_1*t_2*t_4-26992*t_2^2*t_4-1754*t_0*t_3*t_4+31000*t_1*t_3*t_4-17145*t_2*t_3*t_4+31676*t_3^2*t_4-5012*t_0*t_4^2+24782*t_1*t_4^2-12935*t_2*t_4^2-15675*t_3*t_4^2-21976*t_4^3+17838*t_0^2*t_5-10515*t_0*t_1*t_5+14560*t_1^2*t_5+29498*t_0*t_2*t_5-17633*t_1*t_2*t_5-17086*t_2^2*t_5-31256*t_0*t_3*t_5-1718*t_1*t_3*t_5+31547*t_2*t_3*t_5+7490*t_3^2*t_5+2710*t_0*t_4*t_5+22102*t_1*t_4*t_5-12421*t_2*t_4*t_5-17060*t_3*t_4*t_5-25326*t_4^2*t_5-16028*t_0*t_5^2+28955*t_1*t_5^2-12876*t_2*t_5^2-25593*t_3*t_5^2-11056*t_4*t_5^2,t_0*t_1^2-12104*t_0*t_2^2+13063*t_1*t_2^2+8781*t_2^3+31963*t_0^2*t_3-13659*t_0*t_1*t_3+1255*t_1^2*t_3-21010*t_0*t_2*t_3+20003*t_1*t_2*t_3+21201*t_2^2*t_3-20012*t_0*t_3^2-16986*t_1*t_3^2-1542*t_2*t_3^2+3826*t_3^3+13445*t_0^2*t_4+18862*t_0*t_1*t_4-23335*t_1^2*t_4-1652*t_0*t_2*t_4-32760*t_1*t_2*t_4-28346*t_2^2*t_4+22680*t_0*t_3*t_4-6871*t_1*t_3*t_4-19873*t_2*t_3*t_4+24218*t_3^2*t_4-7695*t_0*t_4^2+10877*t_1*t_4^2-5822*t_2*t_4^2-7503*t_3*t_4^2+19727*t_4^3-186*t_0^2*t_5+15269*t_0*t_1*t_5-16299*t_1^2*t_5-32590*t_0*t_2*t_5+19559*t_1*t_2*t_5+21102*t_2^2*t_5-24025*t_0*t_3*t_5+3329*t_1*t_3*t_5-4419*t_2*t_3*t_5+18138*t_3^2*t_5+32398*t_0*t_4*t_5-5146*t_1*t_4*t_5-3545*t_2*t_4*t_5-1634*t_3*t_4*t_5+1228*t_4^2*t_5-6947*t_0*t_5^2+625*t_1*t_5^2+239*t_2*t_5^2-19372*t_3*t_5^2+13096*t_4*t_5^2,t_0^2*t_1+2330*t_0*t_2^2+11913*t_1*t_2^2+13704*t_2^3+21702*t_0^2*t_3+21222*t_0*t_1*t_3-20145*t_1^2*t_3+13347*t_0*t_2*t_3-32194*t_1*t_2*t_3+19373*t_2^2*t_3+16357*t_0*t_3^2+25116*t_1*t_3^2-388*t_2*t_3^2+8811*t_3^3+23362*t_0^2*t_4-4015*t_0*t_1*t_4-18186*t_1^2*t_4+19582*t_0*t_2*t_4+24595*t_1*t_2*t_4-1335*t_2^2*t_4-21886*t_0*t_3*t_4+9395*t_1*t_3*t_4+18304*t_2*t_3*t_4-12163*t_3^2*t_4-17735*t_0*t_4^2-5307*t_1*t_4^2-10769*t_2*t_4^2-7621*t_3*t_4^2+15189*t_4^3-31598*t_0^2*t_5+27598*t_0*t_1*t_5+5767*t_1^2*t_5-128*t_0*t_2*t_5+9498*t_1*t_2*t_5+7647*t_2^2*t_5+1994*t_0*t_3*t_5-29397*t_1*t_3*t_5-32634*t_2*t_3*t_5+176*t_3^2*t_5-18686*t_0*t_4*t_5+6633*t_1*t_4*t_5-23621*t_2*t_4*t_5+640*t_3*t_4*t_5+30408*t_4^2*t_5+8591*t_0*t_5^2-32704*t_1*t_5^2-22423*t_2*t_5^2-20497*t_3*t_5^2-1082*t_4*t_5^2,t_0^3-12629*t_0*t_2^2-18716*t_1*t_2^2+25861*t_2^3-6451*t_0^2*t_3-28745*t_0*t_1*t_3-24241*t_1^2*t_3-17146*t_0*t_2*t_3-28243*t_1*t_2*t_3-22255*t_2^2*t_3-30878*t_0*t_3^2+19291*t_1*t_3^2+12999*t_2*t_3^2+21798*t_3^3+22390*t_0^2*t_4-21510*t_0*t_1*t_4-22696*t_1^2*t_4-8589*t_0*t_2*t_4+23086*t_1*t_2*t_4+25647*t_2^2*t_4-32613*t_0*t_3*t_4-21686*t_1*t_3*t_4+6774*t_2*t_3*t_4+1846*t_3^2*t_4+32188*t_0*t_4^2+545*t_1*t_4^2-29408*t_2*t_4^2+26557*t_3*t_4^2+24500*t_4^3+19823*t_0^2*t_5+20181*t_0*t_1*t_5+4*t_1^2*t_5-25031*t_0*t_2*t_5-29788*t_1*t_2*t_5+23403*t_2^2*t_5+10727*t_0*t_3*t_5-20616*t_1*t_3*t_5+7184*t_2*t_3*t_5-27424*t_3^2*t_5-19932*t_0*t_4*t_5-23344*t_1*t_4*t_5+31253*t_2*t_4*t_5+27555*t_3*t_4*t_5+22324*t_4^2*t_5-21494*t_0*t_5^2-10671*t_1*t_5^2-25326*t_2*t_5^2-29061*t_3*t_5^2-186*t_4*t_5^2);
f := inverse rationalMap legacyRationalMap(ringP5/I,ring U,{t_0, t_1, t_2, t_3, t_4});
U.cache#"MapToMinimalK3Surface" = f;
u := local u;
ringP2 := ZZ/65521[u_0..u_2];
F := U.cache#"MapToMinimalK3Surface";
(image F).cache#"DoubleCoverDefinedByCanonicalDivisor" = quadricFibration rationalMap legacyRationalMap(ring image F,ringP2,{t_1*t_2+819*t_2^2-24705*t_0*t_3+12677*t_1*t_3-20842*t_2*t_3-5377*t_3^2-27077*t_0*t_4+19883*t_1*t_4-6913*t_2*t_4-24238*t_3*t_4+28382*t_4^2+12267*t_0*t_5-10492*t_1*t_5-15907*t_2*t_5+8542*t_3*t_5-4033*t_4*t_5+32404*t_5^2, t_0*t_1-3686*t_1^2-8680*t_0*t_2-31314*t_2^2+7232*t_0*t_3+20758*t_1*t_3+16250*t_2*t_3-20240*t_3^2-8777*t_0*t_4+1571*t_1*t_4-25837*t_2*t_4-16209*t_3*t_4-1677*t_4^2-17177*t_0*t_5-25747*t_1*t_5-26407*t_2*t_5+30275*t_3*t_5+11689*t_4*t_5+29798*t_5^2, t_0^2+17581*t_1^2-13463*t_0*t_2+18102*t_2^2-11452*t_0*t_3-400*t_1*t_3+13202*t_2*t_3-14645*t_3^2-15269*t_0*t_4+5358*t_1*t_4-19829*t_2*t_4-24270*t_3*t_4+29392*t_4^2-21944*t_0*t_5-2573*t_1*t_5-22275*t_2*t_5-12909*t_3*t_5-31559*t_4*t_5+25661*t_5^2});
((image F).cache#"DoubleCoverDefinedByCanonicalDivisor").cache#"discriminantLocusOfQuadricFibration" = projectiveVariety ideal(u_0^8-12256*u_0^7*u_1+32449*u_0^6*u_1^2-2557*u_0^5*u_1^3+29136*u_0^4*u_1^4+31970*u_0^3*u_1^5-18282*u_0^2*u_1^6+18341*u_0*u_1^7+3498*u_1^8-30718*u_0^7*u_2+31964*u_0^6*u_1*u_2+25969*u_0^5*u_1^2*u_2-22161*u_0^4*u_1^3*u_2-19457*u_0^3*u_1^4*u_2+7362*u_0^2*u_1^5*u_2+23930*u_0*u_1^6*u_2-3187*u_1^7*u_2-22213*u_0^6*u_2^2+12768*u_0^5*u_1*u_2^2-31167*u_0^4*u_1^2*u_2^2-13563*u_0^3*u_1^3*u_2^2+32484*u_0^2*u_1^4*u_2^2-1232*u_0*u_1^5*u_2^2+16214*u_1^6*u_2^2-22773*u_0^5*u_2^3+7862*u_0^4*u_1*u_2^3-24592*u_0^3*u_1^2*u_2^3-28456*u_0^2*u_1^3*u_2^3-19326*u_0*u_1^4*u_2^3+3245*u_1^5*u_2^3-5536*u_0^4*u_2^4+22603*u_0^3*u_1*u_2^4-18854*u_0^2*u_1^2*u_2^4+21807*u_0*u_1^3*u_2^4+29145*u_1^4*u_2^4-11356*u_0^3*u_2^5-7898*u_0^2*u_1*u_2^5-25606*u_0*u_1^2*u_2^5+20348*u_1^3*u_2^5-23028*u_0^2*u_2^6-21835*u_0*u_1*u_2^6+25075*u_1^2*u_2^6+20383*u_0*u_2^7+7763*u_1*u_2^7-2622*u_2^8);
))///,
///(U -> (
y := gens ring ambient U;
t := local t;
ringP8 := ZZ/65521[t_0..t_8];
I := ideal(t_2*t_3-9224*t_3^2-27189*t_1*t_4+6837*t_2*t_4+3644*t_3*t_4-7369*t_4^2+12266*t_1*t_5-15368*t_2*t_5+16662*t_3*t_5+16359*t_4*t_5-9720*t_5^2+29332*t_1*t_6+6466*t_2*t_6+58*t_3*t_6-29805*t_4*t_6+7792*t_5*t_6+17318*t_6^2+4904*t_1*t_7+18676*t_2*t_7-14127*t_3*t_7-19062*t_4*t_7+27898*t_5*t_7-19504*t_6*t_7+25526*t_7^2+7875*t_1*t_8-3821*t_2*t_8-4314*t_3*t_8-15415*t_4*t_8+19793*t_5*t_8-30081*t_6*t_8-13445*t_7*t_8-6188*t_8^2,t_1*t_3+1987*t_3^2+27346*t_1*t_4-19095*t_2*t_4-14358*t_3*t_4+26328*t_4^2+32559*t_1*t_5+4945*t_2*t_5-23894*t_3*t_5-1119*t_4*t_5+23569*t_5^2+30210*t_1*t_6-20550*t_2*t_6-17930*t_3*t_6+17204*t_4*t_6-29005*t_5*t_6+27100*t_6^2+2515*t_1*t_7+25932*t_2*t_7-22114*t_3*t_7-13766*t_4*t_7-30628*t_5*t_7-182*t_6*t_7-28576*t_7^2+9995*t_1*t_8-14835*t_2*t_8+2205*t_3*t_8-19817*t_4*t_8-27908*t_5*t_8-32300*t_6*t_8-13964*t_7*t_8-32684*t_8^2,t_2^2-13821*t_3^2-15778*t_1*t_4+27272*t_2*t_4-8094*t_3*t_4-24035*t_4^2+24246*t_1*t_5+10274*t_2*t_5+18643*t_3*t_5-14001*t_4*t_5+29696*t_5^2+6865*t_1*t_6+2386*t_2*t_6+29503*t_3*t_6+29256*t_4*t_6-30156*t_5*t_6-9292*t_6^2+11307*t_1*t_7-20137*t_2*t_7-21407*t_3*t_7-2221*t_4*t_7-23628*t_5*t_7-14226*t_6*t_7+8779*t_7^2+18230*t_1*t_8-28650*t_2*t_8+29355*t_3*t_8-8707*t_4*t_8-5828*t_5*t_8+8199*t_6*t_8-17584*t_7*t_8+7097*t_8^2,t_1*t_2+18483*t_3^2+4049*t_1*t_4-13899*t_2*t_4-6907*t_3*t_4+28338*t_4^2-4408*t_1*t_5-16334*t_2*t_5-20719*t_3*t_5+29082*t_4*t_5-29250*t_5^2+7244*t_1*t_6+32582*t_2*t_6-1829*t_3*t_6+16852*t_4*t_6+1607*t_5*t_6-22320*t_6^2-32149*t_1*t_7-18532*t_2*t_7-7435*t_3*t_7+51*t_4*t_7+14917*t_5*t_7-25231*t_6*t_7+16795*t_7^2+26768*t_1*t_8+22882*t_2*t_8-18473*t_3*t_8-17853*t_4*t_8+7914*t_5*t_8+16428*t_6*t_8-25333*t_7*t_8+1591*t_8^2,t_1^2-6792*t_3^2-24336*t_1*t_4-30737*t_2*t_4+17888*t_3*t_4+4565*t_4^2-16550*t_1*t_5+31301*t_2*t_5-27697*t_3*t_5-19712*t_4*t_5-20330*t_5^2-2135*t_1*t_6+951*t_2*t_6-879*t_3*t_6-29015*t_4*t_6-22178*t_5*t_6+23410*t_6^2+27797*t_1*t_7-21160*t_2*t_7+958*t_3*t_7+2912*t_4*t_7+18289*t_5*t_7+3706*t_6*t_7-20525*t_7^2+17211*t_1*t_8-28215*t_2*t_8-32229*t_3*t_8-32151*t_4*t_8-27424*t_5*t_8-30874*t_6*t_8+22318*t_7*t_8+32718*t_8^2,144*t_3^2+t_0*t_4+25476*t_1*t_4-13889*t_2*t_4-3736*t_3*t_4+597*t_4^2+10168*t_0*t_5-11250*t_1*t_5+12596*t_2*t_5-20021*t_3*t_5+29532*t_4*t_5+12911*t_5^2-23513*t_0*t_6-31312*t_1*t_6-21706*t_2*t_6-6345*t_3*t_6+14658*t_4*t_6-10100*t_5*t_6-29939*t_6^2+5910*t_0*t_7+4328*t_1*t_7-10994*t_2*t_7-26506*t_3*t_7-22299*t_4*t_7+5729*t_5*t_7+30506*t_6*t_7-12768*t_7^2+19368*t_0*t_8+29746*t_1*t_8+9801*t_2*t_8+28928*t_3*t_8+27496*t_4*t_8+5586*t_5*t_8+22125*t_6*t_8-2826*t_7*t_8-23577*t_8^2,t_0*t_3+491*t_3^2+11560*t_1*t_4+16000*t_2*t_4+1467*t_3*t_4+9544*t_4^2-10281*t_0*t_5+25416*t_1*t_5-10823*t_2*t_5+16731*t_3*t_5+18238*t_4*t_5-12132*t_5^2+22487*t_0*t_6-21592*t_1*t_6-24406*t_2*t_6-24603*t_3*t_6+11609*t_4*t_6-18051*t_5*t_6+10956*t_6^2-18542*t_0*t_7+22020*t_1*t_7+16073*t_2*t_7+18236*t_3*t_7-4744*t_4*t_7-17875*t_5*t_7-26646*t_6*t_7+12278*t_7^2-30274*t_0*t_8-24535*t_1*t_8-10814*t_2*t_8+29232*t_3*t_8-14227*t_4*t_8+17364*t_5*t_8-19205*t_6*t_8-1474*t_7*t_8-7429*t_8^2,t_0*t_2+12254*t_3^2+22640*t_1*t_4-28584*t_2*t_4+32109*t_3*t_4-16172*t_4^2+12323*t_0*t_5-20230*t_1*t_5+8636*t_2*t_5+18739*t_3*t_5+7914*t_4*t_5-8695*t_5^2-18078*t_0*t_6+5327*t_1*t_6-30432*t_2*t_6-3117*t_3*t_6-18571*t_4*t_6+22492*t_5*t_6-15301*t_6^2-20021*t_0*t_7+20522*t_1*t_7-3660*t_2*t_7+20252*t_3*t_7-13058*t_4*t_7-917*t_5*t_7-2640*t_6*t_7+17663*t_7^2+11584*t_0*t_8-25136*t_1*t_8+3090*t_2*t_8-100*t_3*t_8-4242*t_4*t_8-31705*t_5*t_8+16029*t_6*t_8-16490*t_7*t_8-9832*t_8^2,t_0*t_1+31705*t_3^2-29902*t_1*t_4-29584*t_2*t_4+28898*t_3*t_4-29474*t_4^2-8674*t_0*t_5+8421*t_1*t_5+4931*t_2*t_5+15917*t_3*t_5+2698*t_4*t_5-5973*t_5^2+14346*t_0*t_6+7176*t_1*t_6+9226*t_2*t_6-23905*t_3*t_6-27591*t_4*t_6+22904*t_5*t_6-21982*t_6^2-21547*t_0*t_7+25764*t_1*t_7+2670*t_2*t_7-4342*t_3*t_7+18572*t_4*t_7-20941*t_5*t_7-20804*t_6*t_7+5882*t_7^2-21657*t_0*t_8+7413*t_1*t_8+4433*t_2*t_8-32576*t_3*t_8-1438*t_4*t_8+32245*t_5*t_8+16346*t_6*t_8+3851*t_7*t_8-2475*t_8^2,t_0^2-21514*t_3^2+792*t_1*t_4-29905*t_2*t_4-10080*t_3*t_4-14241*t_4^2+20232*t_0*t_5-7211*t_1*t_5+28886*t_2*t_5-1726*t_3*t_5+29175*t_4*t_5+25250*t_5^2-32294*t_0*t_6+30483*t_1*t_6-5596*t_2*t_6-19174*t_3*t_6-14986*t_4*t_6-14418*t_5*t_6-10545*t_6^2-29772*t_0*t_7+15508*t_1*t_7-27173*t_2*t_7-11900*t_3*t_7-8060*t_4*t_7-15389*t_5*t_7+9615*t_6*t_7-31992*t_7^2+19544*t_0*t_8+17113*t_1*t_8+20830*t_2*t_8-4398*t_3*t_8-21121*t_4*t_8+13088*t_5*t_8+20426*t_6*t_8-21104*t_7*t_8+26061*t_8^2);
g := legacyRationalMap(ringP8/I,ring U,{t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8});
f := legacyRationalMap(target g,source g,{y_2^2+5637*y_0*y_3+29479*y_1*y_3-3666*y_2*y_3-9551*y_3^2+8112*y_0*y_4-30853*y_1*y_4+2136*y_2*y_4-5255*y_3*y_4+22385*y_4^2+28903*y_0*y_5-17441*y_1*y_5+4051*y_2*y_5+13752*y_3*y_5+9030*y_4*y_5-6123*y_5^2-3610*y_0*y_6+22674*y_1*y_6+4366*y_2*y_6-9710*y_3*y_6+14145*y_4*y_6+10222*y_5*y_6-21929*y_6^2+28417*y_0*y_7-4027*y_1*y_7+7481*y_2*y_7+3831*y_3*y_7+13689*y_4*y_7+23359*y_5*y_7-24590*y_6*y_7-17909*y_7^2, 455*y_0*y_3-25551*y_0*y_4-18492*y_0*y_5+2689*y_0*y_6+32626*y_0*y_7, 455*y_1*y_3-25551*y_1*y_4-18492*y_1*y_5+2689*y_1*y_6+32626*y_1*y_7, 455*y_2*y_3-25551*y_2*y_4-18492*y_2*y_5+2689*y_2*y_6+32626*y_2*y_7, 455*y_3^2-25551*y_3*y_4-18492*y_3*y_5+2689*y_3*y_6+32626*y_3*y_7, 455*y_3*y_4-25551*y_4^2-18492*y_4*y_5+2689*y_4*y_6+32626*y_4*y_7, 455*y_3*y_5-25551*y_4*y_5-18492*y_5^2+2689*y_5*y_6+32626*y_5*y_7, 455*y_3*y_6-25551*y_4*y_6-18492*y_5*y_6+2689*y_6^2+32626*y_6*y_7, 455*y_3*y_7-25551*y_4*y_7-18492*y_5*y_7+2689*y_6*y_7+32626*y_7^2});
forceInverseMap(f,g);
U.cache#"MapToMinimalK3Surface" = rationalMap f;
u := local u;
ringP2 := ZZ/65521[u_0..u_2];
F := U.cache#"MapToMinimalK3Surface";
(image F).cache#"DoubleCoverDefinedByCanonicalDivisor" = quadricFibration rationalMap legacyRationalMap(ring image F,ringP2,{t_3*t_6-11544*t_4*t_6-8379*t_5*t_6+13952*t_6^2+11964*t_0*t_7-3441*t_1*t_7-28661*t_2*t_7+31378*t_3*t_7+7636*t_4*t_7+24449*t_5*t_7+32601*t_6*t_7-21771*t_7^2-24631*t_0*t_8-31369*t_1*t_8+4041*t_2*t_8-7920*t_3*t_8-26281*t_4*t_8-24761*t_5*t_8-22981*t_6*t_8-26790*t_7*t_8-16419*t_8^2, t_1*t_4-25233*t_2*t_4-10200*t_3*t_4+24920*t_4^2-10454*t_0*t_5+12815*t_1*t_5+19610*t_2*t_5-30273*t_3*t_5-3435*t_4*t_5+9933*t_5^2+19437*t_0*t_6+8621*t_1*t_6+22620*t_2*t_6+5466*t_4*t_6+22413*t_5*t_6+4750*t_6^2-7420*t_0*t_7-13609*t_1*t_7-8184*t_2*t_7-16774*t_3*t_7-20624*t_4*t_7-6281*t_5*t_7+8925*t_6*t_7-2028*t_7^2+12067*t_0*t_8+679*t_1*t_8-11144*t_2*t_8+3404*t_3*t_8+7822*t_4*t_8+11333*t_5*t_8-285*t_6*t_8-9717*t_7*t_8+29495*t_8^2, t_0*t_4-29918*t_2*t_4+15090*t_3*t_4-3903*t_4^2+13580*t_0*t_5+31028*t_1*t_5-18858*t_2*t_5-5108*t_3*t_5-26727*t_4*t_5-25849*t_5^2-13850*t_0*t_6-13950*t_1*t_6+15148*t_2*t_6-16725*t_4*t_6+12906*t_5*t_6-5215*t_6^2+19454*t_0*t_7+12274*t_1*t_7-5182*t_2*t_7+15642*t_3*t_7+27094*t_4*t_7-11219*t_5*t_7+16304*t_6*t_7+5891*t_7^2+31143*t_0*t_8-5272*t_1*t_8-2639*t_2*t_8+23117*t_3*t_8-20189*t_4*t_8-28635*t_5*t_8+28087*t_6*t_8-10749*t_7*t_8+30929*t_8^2});
((image F).cache#"DoubleCoverDefinedByCanonicalDivisor").cache#"discriminantLocusOfQuadricFibration" = projectiveVariety ideal(u_0^8+23468*u_0^7*u_1+27663*u_0^6*u_1^2+7787*u_0^5*u_1^3+7700*u_0^4*u_1^4+29312*u_0^3*u_1^5-27053*u_0^2*u_1^6+1149*u_0*u_1^7+2903*u_1^8-19163*u_0^7*u_2+23628*u_0^6*u_1*u_2+834*u_0^5*u_1^2*u_2-1916*u_0^4*u_1^3*u_2-2692*u_0^3*u_1^4*u_2+26553*u_0^2*u_1^5*u_2-2219*u_0*u_1^6*u_2+22457*u_1^7*u_2-2462*u_0^6*u_2^2+10852*u_0^5*u_1*u_2^2+22356*u_0^4*u_1^2*u_2^2+20438*u_0^3*u_1^3*u_2^2-14463*u_0^2*u_1^4*u_2^2+7668*u_0*u_1^5*u_2^2-17879*u_1^6*u_2^2+164*u_0^5*u_2^3+10580*u_0^4*u_1*u_2^3-27306*u_0^3*u_1^2*u_2^3-20897*u_0^2*u_1^3*u_2^3-12829*u_0*u_1^4*u_2^3-7999*u_1^5*u_2^3+3674*u_0^4*u_2^4-3339*u_0^3*u_1*u_2^4+13994*u_0^2*u_1^2*u_2^4+14897*u_0*u_1^3*u_2^4+31781*u_1^4*u_2^4+12183*u_0^3*u_2^5+7177*u_0^2*u_1*u_2^5-22721*u_0*u_1^2*u_2^5+6399*u_1^3*u_2^5+18687*u_0^2*u_2^6-11460*u_0*u_1*u_2^6-4706*u_1^2*u_2^6+11590*u_0*u_2^7-19922*u_1*u_2^7+16642*u_2^8);
))///,
///(U -> (
F := U.cache#"MapToMinimalK3Surface";
t := gens ring target F;
u := local u;
ringP2 := ZZ/65521[u_0..u_2];
(image F).cache#"DoubleCoverDefinedByCanonicalDivisor" = quadricFibration rationalMap legacyRationalMap(ring image F,ringP2,{t_0*t_3^2+775*t_1*t_3^2+14485*t_2*t_3^2-17714*t_3^3-21860*t_1^2*t_4-7776*t_0*t_2*t_4-26930*t_1*t_2*t_4-830*t_2^2*t_4+10829*t_0*t_3*t_4+22084*t_1*t_3*t_4-19294*t_2*t_3*t_4-15275*t_3^2*t_4-23527*t_0*t_4^2-6259*t_1*t_4^2+870*t_2*t_4^2-31029*t_3*t_4^2+16386*t_4^3+19438*t_1^2*t_5-11864*t_0*t_2*t_5-11018*t_1*t_2*t_5+9660*t_2^2*t_5+20068*t_0*t_3*t_5-28634*t_1*t_3*t_5+32018*t_2*t_3*t_5+1771*t_3^2*t_5+30405*t_0*t_4*t_5-16757*t_1*t_4*t_5-12941*t_2*t_4*t_5+24217*t_3*t_4*t_5-24965*t_4^2*t_5-10023*t_0*t_5^2+4934*t_1*t_5^2+23062*t_2*t_5^2+21780*t_3*t_5^2-5795*t_4*t_5^2+30611*t_5^3-7385*t_1^2*t_6-21912*t_0*t_2*t_6-29027*t_1*t_2*t_6+10174*t_2^2*t_6-12477*t_0*t_3*t_6-28301*t_1*t_3*t_6+11703*t_2*t_3*t_6-25518*t_3^2*t_6-6479*t_0*t_4*t_6-17815*t_1*t_4*t_6-17993*t_2*t_4*t_6-27972*t_3*t_4*t_6-5046*t_4^2*t_6+3443*t_0*t_5*t_6+22026*t_1*t_5*t_6-17396*t_2*t_5*t_6+13516*t_3*t_5*t_6+11752*t_4*t_5*t_6+1717*t_5^2*t_6+13704*t_0*t_6^2+11627*t_1*t_6^2+28872*t_2*t_6^2-18938*t_3*t_6^2+22126*t_4*t_6^2+31260*t_5*t_6^2-10395*t_6^3, t_2^2*t_3+28972*t_1*t_3^2-6524*t_2*t_3^2-3265*t_3^3-13875*t_1^2*t_4-26676*t_0*t_2*t_4-29*t_1*t_2*t_4-6324*t_2^2*t_4+2766*t_0*t_3*t_4+11401*t_1*t_3*t_4+6828*t_2*t_3*t_4+16752*t_3^2*t_4+10706*t_0*t_4^2+25788*t_1*t_4^2-914*t_2*t_4^2-11619*t_3*t_4^2-27712*t_4^3-30208*t_1^2*t_5-22958*t_0*t_2*t_5-11105*t_1*t_2*t_5+18747*t_2^2*t_5+1619*t_0*t_3*t_5-23497*t_1*t_3*t_5+22227*t_2*t_3*t_5+9891*t_3^2*t_5-9196*t_0*t_4*t_5-30227*t_1*t_4*t_5+22519*t_2*t_4*t_5+23532*t_3*t_4*t_5+25772*t_4^2*t_5-20311*t_0*t_5^2-9241*t_1*t_5^2-18204*t_2*t_5^2-7455*t_3*t_5^2-3555*t_4*t_5^2+10617*t_5^3+2352*t_1^2*t_6+8222*t_0*t_2*t_6+4481*t_1*t_2*t_6+8405*t_2^2*t_6+32119*t_0*t_3*t_6-13323*t_1*t_3*t_6-7418*t_2*t_3*t_6-6878*t_3^2*t_6+19917*t_0*t_4*t_6-22942*t_1*t_4*t_6-30912*t_2*t_4*t_6-29177*t_3*t_4*t_6+23105*t_4^2*t_6-18486*t_0*t_5*t_6-24991*t_1*t_5*t_6-21329*t_2*t_5*t_6+24962*t_3*t_5*t_6-8951*t_4*t_5*t_6-5668*t_5^2*t_6+28895*t_0*t_6^2-12336*t_1*t_6^2+6850*t_2*t_6^2+17222*t_3*t_6^2+29599*t_4*t_6^2-6854*t_5*t_6^2-16379*t_6^3, t_1*t_2*t_3+31143*t_1*t_3^2+15166*t_2*t_3^2+14041*t_3^3+24539*t_1^2*t_4+12362*t_0*t_2*t_4-15271*t_1*t_2*t_4+29840*t_2^2*t_4+1581*t_0*t_3*t_4+18183*t_1*t_3*t_4-11892*t_2*t_3*t_4+28181*t_3^2*t_4+1088*t_0*t_4^2+23846*t_1*t_4^2-9046*t_2*t_4^2-5892*t_3*t_4^2-18410*t_4^3-19258*t_1^2*t_5-25278*t_0*t_2*t_5+14727*t_1*t_2*t_5+1847*t_2^2*t_5-635*t_0*t_3*t_5-3280*t_1*t_3*t_5-23458*t_2*t_3*t_5-13411*t_3^2*t_5+19077*t_0*t_4*t_5-4727*t_1*t_4*t_5-11142*t_2*t_4*t_5-14817*t_3*t_4*t_5+6439*t_4^2*t_5+16302*t_0*t_5^2-17311*t_1*t_5^2+23604*t_2*t_5^2+3105*t_3*t_5^2+6996*t_4*t_5^2-23279*t_5^3+18964*t_1^2*t_6+11178*t_0*t_2*t_6+25637*t_1*t_2*t_6-3614*t_2^2*t_6-25776*t_0*t_3*t_6-2049*t_1*t_3*t_6+15390*t_2*t_3*t_6-27993*t_3^2*t_6+1886*t_0*t_4*t_6+13924*t_1*t_4*t_6+19552*t_2*t_4*t_6-458*t_3*t_4*t_6-28207*t_4^2*t_6+20234*t_0*t_5*t_6-31240*t_1*t_5*t_6+21405*t_2*t_5*t_6-13358*t_3*t_5*t_6+692*t_4*t_5*t_6-8625*t_5^2*t_6+30552*t_0*t_6^2-16718*t_1*t_6^2+29262*t_2*t_6^2-25123*t_3*t_6^2+6890*t_4*t_6^2+6922*t_5*t_6^2-7850*t_6^3});
((image F).cache#"DoubleCoverDefinedByCanonicalDivisor").cache#"discriminantLocusOfQuadricFibration" = projectiveVariety ideal(u_0^8+12090*u_0^7*u_1+14463*u_0^6*u_1^2-28521*u_0^5*u_1^3+26241*u_0^4*u_1^4+28184*u_0^3*u_1^5-29243*u_0^2*u_1^6-8122*u_0*u_1^7+27802*u_1^8+20336*u_0^7*u_2-106*u_0^6*u_1*u_2-18788*u_0^5*u_1^2*u_2-15664*u_0^4*u_1^3*u_2+22399*u_0^3*u_1^4*u_2-16390*u_0^2*u_1^5*u_2+32059*u_0*u_1^6*u_2-18861*u_1^7*u_2-19156*u_0^6*u_2^2-24731*u_0^5*u_1*u_2^2+23208*u_0^4*u_1^2*u_2^2+28688*u_0^3*u_1^3*u_2^2+15961*u_0^2*u_1^4*u_2^2+1531*u_0*u_1^5*u_2^2-343*u_1^6*u_2^2-19841*u_0^5*u_2^3-5522*u_0^4*u_1*u_2^3+24350*u_0^3*u_1^2*u_2^3-29869*u_0^2*u_1^3*u_2^3-2173*u_0*u_1^4*u_2^3+24297*u_1^5*u_2^3+2537*u_0^4*u_2^4-2770*u_0^3*u_1*u_2^4+20012*u_0^2*u_1^2*u_2^4-23827*u_0*u_1^3*u_2^4-6067*u_1^4*u_2^4+6913*u_0^3*u_2^5-12254*u_0^2*u_1*u_2^5-11094*u_0*u_1^2*u_2^5+5285*u_1^3*u_2^5+24754*u_0^2*u_2^6+24608*u_0*u_1*u_2^6-4722*u_1^2*u_2^6+29203*u_0*u_2^7+2106*u_1*u_2^7+31024*u_2^8);
))///,
null
};

exampleOfRationalIntersectionsOfThreeQuadricsInP7 = memoize(i -> (
    if i < 1 or i > 7 then error "expected integer between 1 and 7";
    X := prebuiltExampleFromArchive("prebuilt-example-in-P7",i);
    f := DoubleCoversOfIntersectionsOfThreeQuadricsInP7_(i-1);
    if f =!= null then (
        U := (surface X).cache#("surfaceDeterminingInverseOfFanoMap",ideal X);
        if not (U.cache#?"MapToMinimalK3Surface" and (image U.cache#"MapToMinimalK3Surface").cache#?"DoubleCoverDefinedByCanonicalDivisor") then (value f) U;
    );
    X.cache#"prebuilt-example" = i;
    X
));

exampleOfRationalGushelMukaiFourfold = memoize(i -> (
    if i < 1 or i > 2 then error "expected integer between 1 and 2";
    prebuiltExampleFromArchive("prebuilt-example-in-P8",i)
));

beginDocumentation()
document {Key => PrebuiltExamplesOfRationalFourfolds, Headline => "A package for explicit examples of rational fourfolds"}
undocumented {associatedCastelnuovoSurface',doubleCover};
