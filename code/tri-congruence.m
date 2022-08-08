intrinsic InternalTriangleGroupMapExactFull(Delta::GrpPSL2Tri : Simplify := 1) -> SeqEnum
  {Returns the full quaternionic representation for Delta.}

  require IsTriangleGroup(Delta) : "Must be triangle group";

  a,b,c := Explode(DefiningABC(Delta));
  m := Lcm([a,b,c]);
  K<z2m> := CyclotomicField(2*m);
  z2a := z2m^(m div a);
  z2b := z2m^(m div b);
  z2c := z2m^(m div c);
  l2a := z2a+1/z2a;
  l2b := z2b+1/z2b;
  l2c := z2c+1/z2c;
  if Simplify ge 1 then
    F := sub<K | [l2a,l2b,l2c]>;
    if F cmpeq Rationals() then
      ZF := Integers();
    else
      OF := EquationOrder(F);
      ZF := MaximalOrder(OF : Ramification := PrimeDivisors(m));
      _, ZF := OptimizedRepresentation(ZF);
    end if;
    F<w> := NumberField(ZF);
  else
    F<w> := sub<K | [z2m+1/z2m]>;
  end if;
  l2a := F!l2a;
  l2b := F!l2b;
  l2c := F!l2c;

  if Simplify ge 1 then
    OF := EquationOrder(F);
    ZZF := MaximalOrder(OF : Ramification := PrimeDivisors(m));
    bl, ZZFop := OptimizedRepresentation(ZZF);
    if bl then
      Fop := NumberField(ZZFop);
    else
      Fop := F;
    end if;
  else
    Fop := F;
  end if;

  Ffree<fa,fb,fc> := FreeAlgebra(Fop, 3);
  B<fa,fb,fc> := quo<Ffree |
                fa^2 - l2a*fa + 1,
                fb^2 - l2b*fb + 1,
                fc^2 - l2c*fc + 1,
                fa*fb - l2c + fc,
                fb*fc - l2a + fa,
                fc*fa - l2b + fb,
                fb*fa - l2b*fa - l2a*fb - fc + l2a*l2b,
                fc*fb - l2c*fb - l2b*fc - fa + l2b*l2c,
                fa*fc - l2a*fc - l2c*fa - fb + l2c*l2a>;

  Bass, mass := Algebra(B);

  bl, Bquat, mquat := IsQuaternionAlgebra(Bass);
  assert bl;

  faquat := mquat(mass(fa));
  fbquat := mquat(mass(fb));
  fcquat := mquat(mass(fc));

  // when integrated into the package, cache
  iota := Delta`TriangleGroupMap^-1*
	                           map<Delta`TriangleGroup -> Bquat |
                  x :-> &*([Bquat!1] cat [[faquat,fbquat,fcquat][Abs(s)]^Sign(s) : s in Eltseq(x)])>;

  return iota;
end intrinsic;

intrinsic CongruenceImage(Delta::GrpPSL2Tri, NN::Any) -> Map, Grp
  {Computes the image of reduction modulo NN on the triangle group Delta.}

  /*
  F<l2a,l2b,l2c> := FunctionField(Rationals(),3);
  Ffree<fa,fb,fc> := FreeAlgebra(F, 3);
  B<fa,fb,fc> := quo<Ffree |
				  fa^2 - l2a*fa + 1,
				  fb^2 - l2b*fb + 1,
				  fc^2 - l2c*fc + 1,
				  fa*fb - l2c + fc,
				  fb*fc - l2a + fa,
				  fc*fa - l2b + fb,
				  fb*fa - l2b*fa - l2a*fb - fc + l2a*l2b,
				  fc*fb - l2c*fb - l2b*fc - fa + l2b*l2c,
				  fa*fc - l2a*fc - l2c*fa - fb + l2c*l2a>;
  Bass, mass := Algebra(B);
  Eltseq(iota(mass(fa))), Eltseq(iota(mass(fa))), Eltseq(iota(mass(fa)));
  */

  a,b,c := Explode(DefiningABC(Delta));
  m := Lcm([a,b,c]);
  K<z2m> := CyclotomicField(2*m);
  z2a := z2m^(m div a);
  z2b := z2m^(m div b);
  z2c := z2m^(m div c);
  l2a := z2a+1/z2a;
  l2b := z2b+1/z2b;
  l2c := z2c+1/z2c;
  F := sub<K | [l2a,l2b,l2c]>;
  if F cmpeq Rationals() then
    F := RationalsAsNumberField();
	ZZF := Integers(F);
  else
	OF := EquationOrder(F);
	ZZF := MaximalOrder(OF : Ramification := PrimeDivisors(m));
	_, ZZF := OptimizedRepresentation(ZZF);
  end if;
  F<w> := NumberField(ZZF);
  l2a := ZZF!l2a;
  l2b := ZZF!l2b;
  l2c := ZZF!l2c;

  daelt := [
				0,
				0,
				0,
				1,
				l2b,
				0,
				-1,
				0,
				-l2a*l2b,
				1,
				l2a,
				l2b,
				-1,
				0,
				0,
				l2a
		    ];
  dbelt := [
				0,
				0,
				1,
				0,
				-l2b*l2c,
				l2b,
				l2c,
				1,
				-1,
				0,
				l2b,
				0,
				l2c,
				-1,
				0,
				0
			];
  dcelt := [
			  0,
			  1,
			  0,
			  0,
			  -1,
			  l2c,
			  0,
			  0,
			  l2a,
			  0,
			  0,
			  -1,
			  -l2a*l2c,
			  l2a,
			  1,
			  l2c
		  ];

  ZZE := Order(NN);
  E := NumberField(ZZE);
  _ := IsSubfield(E,F);

  ZZFmodNN, modNN := quo<ZZF | Generators(NN)>;
  gensDeltamodNN := [[ZZFmodNN | -1,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0,-1]] cat
                      [[modNN(a) : a in dselt] : dselt in [daelt,dbelt,dcelt]];
  pmGNN := MatrixGroup<4, ZZFmodNN | gensDeltamodNN>;
  return pmGNN;
end intrinsic;


intrinsic RamificationTypeF(Delta::GrpPSL2Tri, NN::RngOrdIdl : Al := "MinDegree") -> SeqEnum
  {Returns the cycle type of the ramification above 0,1,oo.}

  if Norm(NN) eq 1 then
    GNN := Sym(1);
    return [Id(GNN) : i in [1..3]], 0, GNN;
  end if;

  iota := InternalTriangleGroupMapExactFull(Delta);
  B := Codomain(iota);
  F := BaseField(B);
  ZZF := Integers(F);
  O := Order([iota(Delta.i) : i in [1..3]]);
  Omax := MaximalOrder(O);
  bbeta := Discriminant(O);

  ZZE := Order(NN);
  E := NumberField(ZZE);
  if Degree(E) lt Degree(F) then
    _ := IsSubfield(E,F);
    ddFE := ZZE!!Discriminant(Integers(RelativeField(E,F)));
  else
    ddFE := 1*ZZE;
  end if;

  NNfact := Factorization(ZZF!!NN);
  phiPPs := [* *];
  mPPs := [* *];
  for PPfact in NNfact do
    PP := PPfact[1];
    e := PPfact[2];
    assert Norm(bbeta + PP) eq 1;  // must be coprime
    // assert Valuation(ZZF!!ddFE,PP) eq 0;
    BPP, phiPP, mPP := pMatrixRing(Omax,PP);
    Append(~phiPPs, phiPP);
    Append(~mPPs, mPP);
  end for;
  PPes := [PPfact[1]^PPfact[2] : PPfact in NNfact];

  ZZFmodNN, modNN := quo<ZZF | Generators(NN)>;

  deltamatsmodNN := [];
  for i := 1 to 3 do
    delta := iota(Delta.i);
    deltaPPmats := [* Eltseq(phiPP(delta)) : phiPP in phiPPs *];
    deltamatseq := [ CRT([ZZF | deltaPPmats[j][i]@@mPPs[j] : j in [1..#deltaPPmats]],
                               PPes) : i in [1..4]];
    Append(~deltamatsmodNN, [modNN(a) : a in deltamatseq]);
  end for;

  GNN := MatrixGroup<2, ZZFmodNN | deltamatsmodNN cat [[-1,0,0,-1]]>;

  if Al eq "MinDegree" then
    mperm, GNNperm := PermutationRepresentation(GNN);
    if #Generators(GNN) eq 3 then
      m1 := Id(GNN);
    else
      m1 := mperm(GNN.4);
    end if;
    GNNpermp, mpermp := quo<GNNperm | m1>;
    mpermp0, GNNpermp0 := MinimalDegreePermutationRepresentation(GNNpermp);
    sigmas := [GNNpermp0.i : i in [1..3]];
  elif Al eq "Compute0" then
    H0 := sub<GNN | [x : x in GNN | x[2,1] eq 0]>;
  end if;

  return sigmas, Genus(sigmas), GNNpermp0;
end intrinsic;


intrinsic RamificationType(Delta::GrpPSL2Tri, NN::Any : GammaType := 0) -> SeqEnum
  {Returns the cycle type of the ramification above 0,1,oo; GammaType is either 0 or 1}

  if Norm(NN) eq 1 then
    GNN := Sym(1);
    return [Id(GNN) : i in [1..3]], 0, GNN;
  end if;

  iota := InternalTriangleGroupMapExactFull(Delta);
  B := Codomain(iota);
  F := BaseField(B);
  ZZF := Integers(F);
  O := Order([iota(Delta.i) : i in [1..3]]);
  Omax := MaximalOrder(O);
  bbeta := Discriminant(O);

  ZZE := Order(NN);
  E := NumberField(ZZE);
  _ := IsSubfield(E,F);
  if Degree(E) lt Degree(F) then
    if Type(E) eq FldRat then
      ddFE := Discriminant(Integers(RelativeField(E,F)))*ZZE;
    else
      ddFE := ZZE!!Discriminant(Integers(RelativeField(E,F)));
    end if;
  else
    ddFE := 1*ZZE;
  end if;

  NNfact := Factorization(ZZF!!NN);
  phiPPs := [* *];
  mPPs := [* *];
  for PPfact in NNfact do
    PP := PPfact[1];
    e := PPfact[2];
    assert Norm(bbeta + PP) eq 1;  // must be coprime
    assert Valuation(ZZF!!ddFE,PP) eq 0;
    BPP, phiPP, mPP := pMatrixRing(Omax,PP);
    Append(~phiPPs, phiPP);
    Append(~mPPs, mPP);
  end for;
  PPes := [PPfact[1]^PPfact[2] : PPfact in NNfact];

  ZZFmodNN, modNN := quo<ZZF | Generators(NN)>;

  deltamatsmodNN := [];
  for i := 1 to 3 do
    delta := iota(Delta.i);
    deltaPPmats := [* Eltseq(phiPP(delta)) : phiPP in phiPPs *];
    deltamatseq := [ CRT([ZZF | deltaPPmats[j][i]@@mPPs[j] : j in [1..#deltaPPmats]],
                               PPes) : i in [1..4]];
    Append(~deltamatsmodNN, [modNN(a) : a in deltamatseq]);
  end for;

  GNN := MatrixGroup<2, ZZFmodNN | deltamatsmodNN cat [[-1,0,0,-1]]>;

  ZGNN := [z : z in GNN | z[1,1] eq z[2,2] and z[2,1] eq 0 and z[1,2] eq 0];

  mperm, GNNperm := PermutationRepresentation(GNN);
  if #Generators(GNN) eq 3 then
    m1 := Id(GNNperm);
    nm1 := 1;
  else
    m1 := mperm(GNN.4);
    nm1 := 2;
  end if;
  GNNpermp, mpermp := quo<GNNperm | m1>;

  ZZEmodNN := quo<ZZE | NN>;
  if GammaType eq 0 then
    index := #ProjectiveLine(ZZEmodNN);
  else
    UmodNN := UnitGroup(ZZEmodNN);
    index := #ProjectiveLine(ZZEmodNN)*#UmodNN;
    if NN + 2*ZZE ne NN then
      index div:= 2;
    end if;
    // index *:= #UmodNN div #sub<UmodNN | [2*x : x in UmodNN]>;
  end if;
  Hs := Subgroups(GNNpermp : IndexEqual := index);
  Ts := [CosetTable(GNNpermp, H`subgroup) : H in Hs];
  mpermp0s := [CosetTableToRepresentation(GNNpermp,T) : T in Ts];
  if GammaType eq 0 then
    mpermp0s := [mpermp0 : mpermp0 in mpermp0s | #Kernel(mpermp0) eq (#ZGNN div nm1)];
  else
    mpermp0s := [mpermp0 : mpermp0 in mpermp0s | #Kernel(mpermp0) eq 1];
  end if;

  // need only one!
  assert #mpermp0s eq 1;
  mpermp0 := mpermp0s[1];
  kermpermp0 := Kernel(mpermp0);
  if GammaType eq 0 then
    assert &and[mpermp(mperm(z)) in kermpermp0 : z in ZGNN];
  end if;

  sigmas := [mpermp0(GNNpermp.i) : i in [1..3]];

  return sigmas, Genus(sigmas), Image(mpermp0);
end intrinsic;


intrinsic ProjectiveRamificationType(Delta::GrpPSL2Tri, NN::Any) -> SeqEnum
  {Returns the cycle type of the ramification above 0,1,oo}

  if Norm(NN) eq 1 then
    GNN := Sym(1);
    return [Id(GNN) : i in [1..3]], 0, GNN;
  end if;

  iota := Delta`TriangleGroupMapExact;
  A := Codomain(iota);
  Oseq := [1] cat [iota(Delta.i) : i in [1..3]];
  ZZE := Order(NN);
  E := NumberField(ZZE);

  basefieldeqQQ := Type(BaseField(A)) eq FldRat;
  if basefieldeqQQ then
    E := RationalsAsNumberField();
    ZZE := Integers(E);
    O := QuaternionOrder([x*y : x,y in Oseq]);
  else
    O := Order([x*y : x,y in Oseq]);
  end if;
  Omax := O;

  NNfact := Factorization(ZZE!!NN);
  phipps := [* *];
  mpps := [* *];
  for ppfact in NNfact do
    pp := ppfact[1];
    e := ppfact[2];
    if basefieldeqQQ then
      if Valuation(ZZE!Discriminant(Omax),pp) ne 0 and HilbertSymbol(A,pp) eq 1 then
        Omax := pMaximalOrder(Omax, pp);
      end if;
      assert Valuation(ZZE!Discriminant(Omax),pp) eq 0;  // must be coprime
      App, phipp, mpp := pMatrixRing(Omax,Norm(pp));
    else
      if Valuation(Discriminant(Omax),pp) ne 0 and HilbertSymbol(A,pp) eq 1 then
        Omax := pMaximalOrder(Omax, pp);
      end if;
      assert Valuation(Discriminant(Omax),pp) eq 0;  // must be coprime
      App, phipp, mpp := pMatrixRing(Omax,pp);
    end if;
    Append(~phipps, phipp);
    Append(~mpps, mpp);
  end for;
  ppes := [ppfact[1]^ppfact[2] : ppfact in NNfact];

  ZZEmodNN, modNN := quo<ZZE | Generators(NN)>;

  thetas := [];
  for s := 1 to 3 do
    lams := Norm(iota(Delta.s));
    vals := [Valuation(lams*ZZE,ppfact[1]) : ppfact in NNfact];
    assert &and[v mod 2 eq 0 and v ge 0 : v in vals];
    theta := WeakApproximation([ppfact[1] : ppfact in NNfact], [v div 2 : v in vals]);
    Append(~thetas, theta);
  end for;

  deltamatsmodNN := [];
  for s := 1 to 3 do
    delta := iota(Delta.s)/thetas[s];
    deltappmats := [* Eltseq(phipp(delta)) : phipp in phipps *];
    deltamatseq := [ CRT([ZZE | deltappmats[j][i]@@mpps[j] : j in [1..#deltappmats]],
                                 ppes) : i in [1..4]];
    Append(~deltamatsmodNN, [modNN(a) : a in deltamatseq]);
  end for;

  reps, red := ProjectiveLine(ZZEmodNN);
  cosetaction := function(alpha);
    seq := [];
    for i := 1 to #reps do
      alpp := Matrix(2,2,alpha)*Matrix(2,1,[modNN(c) : c in Eltseq(reps[i])]);
      _, repi := red([a@@modNN : a in Eltseq(alpp)],false,false);
      Append(~seq, Index(reps, repi));
    end for;
    return Sym(#reps)!seq;
  end function;

  sigmas := [cosetaction(d) : d in deltamatsmodNN];

  return sigmas, Genus(sigmas), sub<Universe(sigmas) | sigmas>;
end intrinsic;
