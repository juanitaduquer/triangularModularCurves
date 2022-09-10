//*****************************//
//        Miscellaneous        //
//*****************************//
intrinsic Lambda(s::RngIntElt) -> FldCycElt
{Returns lambda(s)=zeta_s+zeta_s^(-1), where zeta_s is a primitive s-th root of 1.}
  return RootOfUnity(s)+(1/RootOfUnity(s));
end intrinsic;

intrinsic LambdaZeta(zeta::FldFinElt,m::RngIntElt,s::RngIntElt) -> FldFinElt
{Returns lambda(s)=zeta_s+zeta_s^(-1), where zeta_s is computed from the 2m-th root of 1 given.}
  return Parent(zeta)!(zeta^((2*m) div s)+(zeta^((2*m) div s))^(-1));
end intrinsic;

intrinsic LexOrderABC(L::SeqEnum) -> SeqEnum
{Sorts the list by lex order in (a,b,c,q)}
  N := [];
  for t in L do
    Append(~N,[t[1],t[2],t[3],t[5],t[4],t[6]]);
  end for;
  N:=Sort(N);
  M:=[];
  for t in N do
    Append(~M,[t[1],t[2],t[3],t[5],t[4],t[6]]);
  end for;
  return M;
end intrinsic;
//*****************************//
//  Triple (a,b,c) conditions  //
//*****************************//
intrinsic IsHyperbolicTriple(a::RngIntElt,b::RngIntElt,c::RngIntElt) -> BoolElt
  {Returns true if the triple (a,b,c) is hyperbolic.}
  if (1/a+1/b+1/c-1) lt 0 then
    return true;
  else
    return false;
  end if;
end intrinsic;

//*****************************//
//     Group of definition     //
//*****************************//
intrinsic GroupForABC(a::RngIntElt,b::RngIntElt,c::RngIntElt,p::RngIntElt) -> SeqEnum
  {Returns the size q of the residue field of a prime of E(a,b,c) above p and 1 or -1 if the associated group is PSL_2(Fq) or PGL_2(Fq) respectively.}
  m := Lcm([a,b,c]);
  twom := 2*m;
  twom div:= p^Valuation(twom,p);
  if twom eq 1 then
    power := 1;
  else
    power := Order(p,twom);
  end if;
  bigPower := p^power;
  k := GF(bigPower);
  twoap,twobp,twocp := Explode([(2*s) div (p^Valuation(2*s,p)) : s in [a,b,c]]);
  zeta_twom := PrimitiveElement(k)^((bigPower-1) div twom);
  genF := [LambdaZeta(zeta_twom,m,2*s) : s in [a,b,c] | s mod p ne 0];
  genE := [LambdaZeta(zeta_twom,m,s) : s in [a,b,c] | s mod p ne 0];
  lastE := k!1;
  for s in [s : s in [a,b,c] | s mod p ne 0] do
    lastE *:= LambdaZeta(zeta_twom,m,2*s);
  end for;
  Append(~genE,lastE);
  F := sub<k|genF>;
  E := sub<k| genE>;
  degE := Degree(E);
  degF := Degree(F);
  if degF eq degE then
    return [#E,1];
  end if;
  return [#E,-1];
end intrinsic;

//*****************************//
//         Ramification        //
//*****************************//

intrinsic RamoficationAtS(s::RngIntElt,q::RngIntElt) -> RngIntElt
{Given s, it computes the ramification degree associated to sigma_s using Lemma 3.1 of [DR. & V.]}
  assert s ne 2 or (s eq 2 and IsPrimePower(q) and IsEven(q));
  if q mod s eq 0 then
    return (q/s)*(s-1);
  elif (q+1) mod s eq 0 then
    return ((q+1)/s)*(s-1);
  elif (q-1) mod s eq 0 then
    return ((q-1)/s)*(s-1);
  end if;
end intrinsic;

intrinsic RamificationFromMatrix(M::AlgMatElt,q::RngIntElt) -> RngIntElt
{Computes the ramification at s from the matrix representation of pi_PP(delta_s).}
  if IsIrreducible(CharacteristicPolynomial(M)) then
    // The non-split semisimple case
    return (q+1)/2;
  else
    // The split semisimple case
    return (q-1)/2;
  end if;
end intrinsic;

intrinsic RamificationTriple(a::RngIntElt,b::RngIntElt,c::RngIntElt,p::RngIntElt,q::RngIntElt,pm::RngIntElt) -> RngIntElt
{Returns the ramification of the cover X_0(a,b,c;pp)->P^1}
  if p eq 2 then
    return &+[RamoficationAtS(s,q) : s in [a,b,c]];
  end if;
  // This is the hardest case. We cannot defice the ramification from only knowing that the genus is in ZZ
  if [a,b] eq [2,2] then
    // sigmas := MatricesTriple([a,b,c],q,pm);
    // return &+[RamificationFromMatrix(sigmas[i],q) : i in[1..3]];
  end if;
  if a ne 2 then
    return &+[RamoficationAtS(s,q) : s in [a,b,c]];
  else
    if pm eq 1 then
      if q mod 4 eq 1 then
        return (q-1)/2+RamoficationAtS(b,q)+RamoficationAtS(c,q);
      else
        return (q+1)/2+RamoficationAtS(b,q)+RamoficationAtS(c,q);
      end if;
    else
    // Now anyting can happen. We use that g is an integer.
      r := (q+1)/2+RamoficationAtS(b,q)+RamoficationAtS(c,q);
      if Floor((1/2)*(-2*(q+1)+r+2)) eq ((1/2)*(-2*(q+1)+r+2)) then
        return r;
      else;
        return r-1;
      end if;
    end if;
  end if;
end intrinsic;

//*****************************//
//           Bounds            //
//*****************************//

intrinsic QBound(a::RngIntElt,b::RngIntElt,c::RngIntElt,g::RngIntElt) -> RngIntElt
{The maximum value of q that can give X_0(a,b,c;pp) of genus < g0 for pp with residue field of size q}
  chi := 1-(1/a+1/b+1/c);
  return Ceiling(2*(g+1)/chi+1);
end intrinsic;

intrinsic CBound(a::RngIntElt,b::RngIntElt,q::RngIntElt,g::RngIntElt) -> Any
{The maximum value of c that can give X_0(a,b,c;pp) of genus < g0}
  lhs := 1-1/a-1/b-2*(g+1)/(q-1);
  if lhs le 0 then
    // There is no bound on c given by this inequality
    return Infinity();
  else
    return Floor(1/lhs);
  end if;
end intrinsic;

intrinsic QMax(g::RngIntElt) -> RngIntElt
{The maximum value of q that can give X_0(a,b,c;pp) of genus < g0 for pp with residue field of size q}
  return 2*42*(g+1)+1;
end intrinsic;

//*****************************//
//            Genus            //
//*****************************//
intrinsic GenusTriangularModularCurve(a::RngIntElt,b::RngIntElt,c::RngIntElt,p::RngIntElt : q:= -1, pm:= 0) -> RngIntElt
{The genus of X_0(a,b,c,pp) from Theorem 3.3 of [DR. & V.]}
  if q eq -1 then
    q, pm := Explode(GroupForABC(a,b,c,p));
  end if;
  r := RamificationTriple(a,b,c,p,q,pm);
  return (1/2)*(-2*(q+1)+r+2);
end intrinsic;

intrinsic IsQAdmissible(a::RngIntElt,b::RngIntElt,c::RngIntElt,p::RngIntElt, q::RngIntElt) -> BoolElt
{True if the triple (a,b,c) is q-admissible.}
  return &and[((q+1) mod s)*((q-1) mod s) eq 0 or s eq p : s in [a,b,c]];
end intrinsic;

intrinsic IspSplit(a::RngIntElt,b::RngIntElt,c::RngIntElt,p::RngIntElt, q::RngIntElt) ->BoolElt
{True if the prime pp divides beta.}
  if 2*a*b*c mod p ne 0 then
    return true;
  else
    m := Lcm([a,b,c]);
    twom := 2*m;
    twom div:= p^Valuation(twom,p);
    if twom eq 1 then
      power := 1;
    else
      power := Order(q,twom);
    end if;
    bigPower := q^power;
    k := GF(bigPower);
    twoap,twobp,twocp := Explode([(2*s) div (p^Valuation(2*s,p)) : s in [a,b,c]]);
    zeta_twom := PrimitiveElement(k)^((bigPower-1) div twom);
    for i in [i:i in [1..twom]|Gcd(i,twom) eq 1] do
      z := zeta_twom^i;
      z2a,z2b,z2c := Explode([z^(twom div twos) : twos in [twoap,twobp,twocp]]);
      l2a, l2b, l2c := Explode([z2a + 1/z2a, z2b + 1/z2b, z2c + 1/z2c]);
      if (l2a^2 + l2b^2 + l2c^2 - l2a*l2b*l2c - 4) ne 0 then
        return true;
      end if;
    end for;
    return false;
  end if;
end intrinsic;

//************************************************//
//                  Enumeration                   //
//************************************************//
intrinsic ListBoundedGenusAdmissible(genus::RngIntElt) -> SeqEnum
{Returns the list (organized by genus in ascending order) of lists (a,b,c;p) such that the curve X_0(a,b,c;pp) have genus bounded by g and pp is a prime of norm p}
  list := [[]:i in [0..genus]];
  boundq := QMax(genus);
  powers := [ n : n in [2..boundq] | IsPrimePower(n) ];
  for q in powers do
    possibilities := Set(PrimeDivisors(q) cat Divisors(q+1) cat Divisors(q-1));
    Exclude(~possibilities,1);
    p := PrimeDivisors(q)[1];
    possibilities := Sort(SetToSequence(possibilities));
    // print "Possibilities for q=",q," are ",possibilities;
    for i in [1..#possibilities] do
      a := possibilities[i];
      for j in [i..#possibilities] do
        b := possibilities[j];
        cbound := CBound(a,b,q,genus);
        for k in [j..#possibilities] do
          c := possibilities[k];
          if c le cbound and IsHyperbolicTriple(a,b,c) and IsQAdmissible(a,b,c,p,q) then
            qFromGroup, pm := Explode(GroupForABC(a,b,c,p));
            if q eq qFromGroup and IspSplit(a,b,c,p,q) then
              // print a,b,c;
              g := GenusTriangularModularCurve(a,b,c,p:q:=q,pm:=pm);
              // print "genus", g;
              if g le genus then
                Append(~list[Integers()!(g+1)],[a,b,c,p,q,pm]);
              end if;
            end if;
          end if;
        end for;
      end for;
    end for;
  end for;
  return [LexOrderABC(list[i]):i in [1..genus+1]];
end intrinsic;

intrinsic CountBoundedGenus(g::RngIntElt) -> SeqEnum
{Counts how many curves of genus up to g there are.}
  L := ListBoundedGenusAdmissible(g);
  return [#L[1]+5] cat [#L[i]: i in [2..#L]];
end intrinsic;


//************************************************//
//                Composite Level                 //
//************************************************//
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
  // Omax := MaximalOrder(O);
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
    BPP, phiPP, mPP := pMatrixRing(O,PP); //This is where Omax lives.
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
  // Omax := MaximalOrder(O);
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
    BPP, phiPP, mPP := pMatrixRing(O,PP); //This is where Omax lives.
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
  // assert mpermp0s eq 1;  Investigate this bug
  mpermp0 := mpermp0s[1];
  kermpermp0 := Kernel(mpermp0);
  if GammaType eq 0 then
    assert &and[mpermp(mperm(z)) in kermpermp0 : z in ZGNN];
  end if;

  sigmas := [mpermp0(GNNpermp.i) : i in [1..3]];

  return sigmas, Genus(sigmas), Image(mpermp0);
end intrinsic;

intrinsic OrderPXL(M::Any,bound::Any)->Any
{Returns the order of the matrix when thought in PXL}
  matrix := M;
  for ord in [1..bound] do
    if matrix[1][1] eq matrix[2][2] and matrix[1][2] eq matrix[2][1] and matrix[1][2] eq 0 then
      return ord;
    end if;
    matrix *:= M;
  end for;
  return -1;
end intrinsic;

intrinsic SameSquareClass(x::Any,y::Any) -> BoolElt
{Returns true if x and y differ by a square}
  return x in [s^2*y:s in Parent(x)];
end intrinsic;

intrinsic EquivModH1(M1::Any,M2::Any) ->BoolElt
{Returns true if M1 and M2 are equivalent modulo H1}
  return (SameSquareClass(Determinant(M1),Determinant(M2))) and ((M1[1][1] eq M2[1][1] and M1[2][1] eq M2[2][1]) or (M1[1][1] eq -M2[1][1] and M1[2][1] eq -M2[2][1]));
end intrinsic;

intrinsic FindEquivModH1(M::Any,H1QuotientReps::SeqEnum) -> Any
{Returns the equivalent to M from the list of representatives}
  return [Meq : Meq in H1QuotientReps | EquivModH1(Meq,M)][1];
end intrinsic;

intrinsic FindMatrixH1(ZZEmodNN::Any,x::Any) ->Any
{Returns a matrix in the class}
  for y in CartesianPower(ZZEmodNN,2) do
    if (x[1]*y[2]-y[1]*x[2]) eq x[3] then
      return Matrix([[x[1],y[1]],[x[2],y[2]]]);
    end if;
  end for;
end intrinsic;

intrinsic H1QuotientReps(ZZEmodNN::Any) -> Any, Any
{Returns matrix representatives for GN/H1 and a map to those representatives}
  reps := [];
  repsSq := [];
  for x in ZZEmodNN do
    if IsUnit(x) and not &or[SameSquareClass(x,y): y in repsSq] then
      Append(~repsSq,x);
    end if;
  end for;
  for x in CartesianPower(ZZEmodNN,2) do
    if [x[1],x[2]] ne [ZZEmodNN!0,ZZEmodNN!0] then
      for sq in repsSq do
        M := FindMatrixH1(ZZEmodNN,<x[1],x[2],sq>);
        if #[Mat: Mat in reps | EquivModH1(Mat,M)] eq 0 then
          Append(~reps,M);
        end if;
      end for;
    end if;
  end for;
  return reps;
end intrinsic;

intrinsic ProjectiveRamificationType(Delta::GrpPSL2Tri, NN::Any : GammaType := 0) -> BoolElt, SeqEnum
  {Returns the cycle type of the ramification above 0,1,oo; GammaType is either 0 or 1}

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
    OLambda := QuaternionOrder([x*y : x,y in Oseq]);
  else
    OLambda := Order([x*y : x,y in Oseq]);
  end if;

  NNfact := Factorization(ZZE!!NN);
  phipps := [* *];
  mpps := [* *];
  for ppfact in NNfact do
    pp := ppfact[1];
    e := ppfact[2];
    if basefieldeqQQ then
      if Valuation(ZZE!Discriminant(OLambda),pp) ne 0 then
        return false,_,_,_;
      end if;
      App, phipp, mpp := pMatrixRing(OLambda,Norm(pp));
    else
      if Valuation(Discriminant(OLambda),pp) ne 0 then
        return false,_,_,_;
      end if;
      App, phipp, mpp := pMatrixRing(OLambda,pp);
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

  print "Triangle group, ",DefiningABC(Delta),". Norm of the ideal ", Factorization(Norm(NN)),". Orders: ",[OrderPXL(Matrix(2,2,d),1000) : d in deltamatsmodNN];
  if [OrderPXL(Matrix(2,2,d),1000) : d in deltamatsmodNN] ne DefiningABC(Delta) then
    print "HERE!!!!!!!", "Triangle group, ",DefiningABC(Delta),". Norm of the ideal ", Factorization(Norm(NN)),". Orders: ",[OrderPXL(Matrix(2,2,d),1000) : d in deltamatsmodNN];
  end if;

  cosetaction := function(alpha,reps,red);
    seq := [];
    for i := 1 to #reps do
      alpp := Matrix(2,2,alpha)*Matrix(2,1,[modNN(c) : c in Eltseq(reps[i])]);
      _, repi := red([a@@modNN : a in Eltseq(alpp)],false,false);
      Append(~seq, Index(reps, repi));
    end for;
    return Sym(#reps)!seq;
  end function;

  IsSquareQuot := function(sq)
    ZZQ := Parent(sq);
    L := [s : s in ZZQ | s^2 eq sq];
    if #L eq 0 then
      return false,_;
    else
      return true,L[1];
    end if;
  end function;

  cosetactionH1 := function(alpha,reps);
    delt := Matrix(2,2,alpha);
    bool,sq := IsSquareQuot(Determinant(delt));
    if bool then
      delt := Matrix(2,2,[alpha[i]*sq^(-1):i in [1..#alpha]]);
      print [delt^s : s in DefiningABC(Delta)];
    end if;
    seq := [];
    for i := 1 to #reps do
      alpp := delt*reps[i];
      M := FindEquivModH1(alpp,reps);
      Append(~seq, Index(reps, M));
    end for;
    print seq;
    return Sym(#reps)!seq;
  end function;

  if GammaType eq 0 then
    reps, red := ProjectiveLine(ZZEmodNN);
    sigmas := [cosetaction(d,reps, red) : d in deltamatsmodNN];
  else
    //GammaType is 1
    reps := H1QuotientReps(ZZEmodNN);
    sigmas := [cosetactionH1(d,reps) : d in deltamatsmodNN];
  end if;
  return true, sigmas, Genus(sigmas), sub<Universe(sigmas) | sigmas>;
end intrinsic;

intrinsic DeleteDuplicates(L::List) -> List
{Deletes repeated entries}
  new := [];
  for x in L do
    if not &or[new[j] eq x : j in [1..#new]] then
      Append(~new,x);
    end if;
  end for;
  return new;
end intrinsic;

intrinsic EnumerateCompositeLevel(genus::RngIntElt) -> Any
{Returns a list of curves X_0(a,b,c;NN) of genus bounded by genus and with NN a non-prime ideal}
  primesList := ListBoundedGenusAdmissible(genus);
  primesList := &cat[primesList[i] : i in [1..#primesList]];
  primesGrouped := {[primesList[j] : j in [1..#primesList] | primesList[i][1..3] eq primesList[j][1..3]] : i in [1..#primesList]};
  primesGrouped := Sort(SetToSequence(primesGrouped));
  list := [*[**] : i in [1..(genus+1)]*];
  for dat in primesGrouped do
    a,b,c := Explode(dat[1]);
    print "=====";
    print a,b,c;
    ps := [d[4] : d in dat];
    qs := [d[5] : d in dat];
    xs := [d[6] : d in dat];

    Delta := TriangleGroup(a,b,c);
    E := BaseField(QuaternionAlgebra(Delta));
    ZZE := Integers(E);

    pps := [pp : pp in PrimesUpTo(Max(qs),E) | Norm(pp) in qs];
    NNOKs := [1*ZZE];
    idealsChecked := [1*ZZE];
    while NNOKs ne [] do
      NNOKs_frontier := [];
      for NN in NNOKs do
        for pp in pps do
          NNP := NN*pp;
          toCheck := false;
          if not NNP in idealsChecked then
            if NN ne 1*ZZE and Degree(E) ne 1 then
              if &and[(&or[&or[[*[a,b,c],ND*pp*] eq list[i][j] : j in [1..#list[i]]] : i in [1..#list]]) : ND in Divisors(NN) | ND ne NN ] then
                toCheck := true;
              else
                print "Not low g";
              end if;
            else
              toCheck := true;
            end if;
          end if;
          if toCheck then
            Append(~idealsChecked,NNP);
            print "....   ", Norm(NNP);
            // INSERT p's!!!!!!!!!
            sigmas, g := ProjectiveRamificationType(Delta, NNP);
            p := Factorization(Norm(pp))[1][1];
            if not IsPrime(NNP) then
              for mult in CartesianPower([1,p],3) do
                Deltap := TriangleGroup(a*mult[1],b*mult[2],c*mult[3]);
                Ep := BaseField(QuaternionAlgebra(Deltap));
                _ := IsSubfield(E,Ep);
                ZZEp := Integers(Ep);
                NNPp := [N :N in IdealsUpTo(Norm(NNP),ZZEp)|Norm(N) eq Norm(NNP)][1];
                _, _ := ProjectiveRamificationType(Deltap, NNPp);
              end for;
            end if;
            // sigmas,g:= RamificationType(Delta, NNP:GammaType :=0);
            if g le genus then
              list[g+1] := Append(list[g+1],[*[a,b,c],NNP*]);
              print "genus ",g," ", Norm(NNP);
              Append(~NNOKs_frontier, NNP);
            end if;
          end if;
        end for;
      end for;
      NNOKs := NNOKs_frontier;
    end while;
  end for;
  return [*DeleteDuplicates(list[i]) : i in [1..#list]*];
end intrinsic;
