AttachSpec("~/Documents/Code/Belyi/Code/spec");
// AttachSpec("~/Belyi/Code/spec");
load "matrices.m";
load "listOrganizer.m";

lambda := function(s)
// Input: an integer s. Ourput: lambda(s)=zeta_s+zeta_s^{-1}
  return RootOfUnity(s)+(1/RootOfUnity(s));
end function;

lambdaZeta := function(zeta,m,s)
// Input: 2m-th root of 1, an integer s.
// Ourput: lambda(s)=zeta_s+zeta_s^{-1}, where zeta_s is computed from the root of 1.
  return Parent(zeta)!(zeta^((2*m) div s)+(zeta^((2*m) div s))^(-1));
end function;

//*****************************//
//    Triple conditions        //
//*****************************//
isHyperbolic := function(a,b,c)
  // Given a triple (a,b,c), it returns true if the triple is hyperbolic.
  if (1/a+1/b+1/c-1) lt 0 then
    return true;
  else
    return false;
  end if;
end function;

isExceptional := function(a,b,c)
  if [a,b,c] in [[2,3,3],[3,3,3],[3,4,4],[2,3,4],[2,5,5],[5,5,5],[3,3,5],[3,5,5],[2,3,5]] then
    return true;
  end if;
  return false;
end function;

//*****************************//
//       Trace Triples         //
//*****************************//

possibleTraces := function(s,q)
  /* Input: a positive integer s and a power of an odd prime q
    Output: Possible traces in F_q such that +/- the matrix in SL_2(F_q) has order 2s if q != s
    if p=s, then it returns 0, -2, 2 */

  traces := [];
  if IsPrime(q) and q eq s then
    return [GF(q)!2,GF(q)!0,GF(q)!(-2)];
  end if;
  if (q-1) mod (2*s) eq 0 then
    k := GF(q);
  else
    k := GF(q^2);
  end if;
  zeta := PrimitiveElement(k)^((#k-1) div (2*s));
  for i in [i : i in [1..2*s] | Gcd(i,2*s) eq 1] do
    trace := zeta^i+zeta^(-i);
    if not trace in traces then
      Append(~traces, trace);
    end if;
    if not -trace in traces then
      Append(~traces, -trace);
    end if;
  end for;
  return traces;
end function;

traceTriples := function(a,b,c,q)
  /* input: (a,c,b) triple and q power of a prime
  output: Possible trace triples*/
  tracesA:=possibleTraces(a,q);
  tracesB:=possibleTraces(b,q);
  tracesC:=possibleTraces(c,q);
  traces := [];
  for t1 in tracesA do
    for t2 in tracesB do
      for t3 in tracesC do
        Append(~traces,[t1,t2,t3]);
      end for;
    end for;
  end for;
  return traces;
end function;

isCommutative := function(traceTriple)
// Given a triple (a,b,c), it returns true if the trace triple is commutative and false otherwise.
  t1,t2,t3 := Explode(traceTriple);
  beta := t1^2+t2^2+t3^2-t1*t2*t3-4;
  return beta eq 0;
end function;

isProjective := function(traceTriple)
// Given a trace triple, it returns true if the triple is projective and false otherwise.
  return not isCommutative(traceTriple);
end function;

isSquareRootFromK := function(t,k,q)
  R<x> := PolynomialRing(GF(q));
  for u in k do
    if not IsSquare(u) then
      roots := Roots(x^2-u,GF(q));
       if t in [r[1] : r in roots] then
         print "Is square";
         return true;
       end if;
    end if;
  end for;
  return false;
end function;

isIrregular := function(traceTriple,q)
  /* input: a trace triple
     output: true if the triple is irregular (page 29 of Clark&Voight)
  */
  sq, kSize := IsSquare(q);
  if not sq then
    return false;
  else
    t := traceTriple;
    k := GF(kSize);
    for i in [1..3] do
      valid := false;
      if t[i]^kSize eq t[i] then
        valid := true;
        for j in [j : j in [1,2,3]|j ne i] do
          print j;
          if t[j] ne 0 and not isSquareRootFromK(t[j],k,q) then
            valid := false;
          end if;
        end for;
      end if;
      if valid then
        return true;
      end if;
    end for;
    return false;
  end if;
end function;

isRegular := function(traceTriple,q)
  return not isIrregular(traceTriple,q);
end function;

//*****************************//
//     Counting with traces    //
//*****************************//
checkTriples := function(a,b,c,p,q)
  list:=[];
  triples := traceTriples(a,b,c,q);
  for t in triples do
    if isProjective(t) then
      if isRegular(t,q) then
        print "regular",t;
        Append(~list,1);
      else
        k := GF(p);
        k1<t1> := ext < k|CharacteristicPolynomial(k!t[1],k)>;
        k2<t2> := ext < k1|CharacteristicPolynomial(k!t[2],k1)>;
        k3<t3> := ext < k2|CharacteristicPolynomial(k!t[3],k2)>;
        print k3;
        if k3 eq sub<k3|t1^2,t2^2,t3^2,t1*t2*t3> then
          Append(~list, 1);
        end if;
        print "Here", a,b,c;
        Append(~list,-1);
      end if;
    end if;
  end for;
  return list;
end function;

//*****************************//
//     Group of definition     //
//*****************************//

groupForABC := function(a,b,c,p)
// Input: a hyperbolic projective triple [a,b,c] and an integer bound
// Output: q such that G=PXL_2(F_q) is as in Theorem A (Clark and Voight)
  if p ne 2 then
    m := Lcm([a,b,c]);
    m div:= p^Valuation(m,p);
    power := Order(p,2*m);
    bigPower := p^power;
    k := GF(bigPower);
    zeta_2m := Roots(CyclotomicPolynomial(2*m),k)[1][1];
    genF := [lambdaZeta(zeta_2m,m,2*s) : s in [a,b,c] | s mod p ne 0];
    genE := [lambdaZeta(zeta_2m,m,s) : s in [a,b,c] | s mod p ne 0];
    lastE := k!1;
    for s in [s : s in [a,b,c] | s mod p ne 0] do
      lastE *:= lambdaZeta(zeta_2m,m,2*s);
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
  else
    print "computing a splitting field";
    E := SplittingField([MinimalPolynomial(lambda(a)),MinimalPolynomial(lambda(b)),MinimalPolynomial(lambda(c)),MinimalPolynomial(lambda(2*a)*lambda(2*b)*lambda(2*c))]);
    print "The field E is", E;
    ZZE := RingOfIntegers(E);
    D_E := Factorization(ideal<ZZE|ZZE!p>);
    P := ideal<ZZE|D_E[1][1]>;
    q := #ResidueClassField(P);
    return [q,-1];
  end if;
end function;

//*****************************//
//         Ramification        //
//*****************************//

e_x := function(x,q)
// Given an integer x>1, it computes the ramification degree associated to sigma_a.
// This uses Lemmas TODO: find lemmas on the paper
  if q mod x eq 0 then
    return q*(x-1)/x;
  elif (q+1) mod x eq 0 then
    return (q+1)*(x-1)/x;
  elif (q-1) mod x eq 0 then
    return (q-1)*(x-1)/x;
  end if;
end function;

ramificationTriple := function(a,b,c,p,q,pm)
// Computes the ramification of the cover X_0(a,b,c;p)->P^1
  if p eq 2 then
    return &+[e_x(s,q) : s in [a,b,c]];
  end if;
  if a ne 2 then
    return &+[e_x(s,q) : s in [a,b,c]];
  else
    if pm eq 1 then
      if q mod 4 eq 1 then
        return (q-1)/2+e_x(b,q)+e_x(c,q);
      else
        return (q+1)/2+e_x(b,q)+e_x(c,q);
      end if;
    else
    // Now anyting can happen.
      Mat := matricesTriple([a,b,c],q,pm);
      sigma2 := Mat[1];
      if IsIrreducible(CharacteristicPolynomial(sigma2)) then
        // The non-split semisimple case
        return (q+1)/2+e_x(b,q)+e_x(c,q);
      else
        // The split semisimple case
        return (q-1)/2+e_x(b,q)+e_x(c,q);
      end if;
    end if;
  end if;
end function;

//*****************************//
//           Bounds            //
//*****************************//

qBound := function(a,b,c)
  chi := 1-(1/a+1/b+1/c);
  return Ceiling(4/chi+1);
end function;

cBound := function(a,b,q)
  lhs := 1-1/a-4/(q-1) -1/b;
  if lhs le 0 then
    return q+1;
  else
    return Floor(1/lhs+1);
  end if;
end function;

qMax := function(g)
  return 2*42*(g+1)+1;
end function;


//*****************************//
//            Genus            //
//*****************************//

genusTriangularModularCurve := function(a,b,c,p,q,pm)
  r := ramificationTriple(a,b,c,p,q,pm);
  return (1/2)*(-2*(q+1)+r+2);
end function;

isQAdmissible := function(a,b,c,p,q)
  return &and[((q+1) mod s)*((q-1) mod s) eq 0 or s eq p : s in [a,b,c]];
end function;

ispSplit := function(a,b,c,p,q)
  if 2*a*b*c mod p ne 0 then
    return true;
  elif p eq 2 then
    for m in Divisors(a) do
      z := a div m;
      if [b,c] eq [m*(z+1),m*z*(z+1)] or [b,c] eq [-m*(-z+1),m*z*(-z+1)] then
        return false;
      end if;
    end for;
    return true;
  else
    F:=GF(q);
    m := Lcm([a,b,c]);
    m div:= p^Valuation(m,p);
    power := Order(p,2*m);
    bigPower := p^power;
    k := GF(bigPower);
    ap,bp,cp := Explode([s div p^Valuation(s,p) : s in [a,b,c]]);
    // Primitive element ^(q-1)/(2m)
    zeta_2m := Roots(CyclotomicPolynomial(2*m),k)[1][1];
    for i in [i:i in [1..2*m]|Gcd(i,2*m) eq 1] do
      z := zeta_2m^i;
      z2a,z2b,z2c := Explode([z^(m div s):s in [ap,bp,cp]]);
      l2a, l2b, l2c := Explode([z2a + 1/z2a, z2b + 1/z2b, z2c + 1/z2c]);
      print l2a^2 + l2b^2 + l2c^2 - l2a*l2b*l2c - 4;
      if (l2a^2 + l2b^2 + l2c^2 - l2a*l2b*l2c - 4) ne 0 then
        return true;
      end if;
    end for;
    return false;
  end if;
end function;

//************************************************//
//                  Enumeration                   //
//************************************************//

//*****************************//
//         prime case          //
//*****************************//
listBoundedGenus := function(genus)
  list:=[];
  boundq := qMax(genus);
  powers := [ n : n in [2..boundq] | IsPrimePower(n) ];
  for q in powers do
    possibilities := Set(Divisors(q) cat Divisors(q+1) cat Divisors(q-1));
    Exclude(~possibilities,1);
    p := PrimeDivisors(q)[1];
    possibilities := Sort(SetToSequence(possibilities));
    print "Possibilities for q=",q," are ",possibilities;
    for i in [1..#possibilities] do
      a := possibilities[i];
      for j in [i..#possibilities] do
        b := possibilities[j];
        cbound := cBound(a,b,q);
        for k in [j..#possibilities] do
          c := possibilities[k];
          if c le cbound and isHyperbolic(a,b,c) and isQAdmissible(a,b,c,p,q) then
            qFromGroup, pm := Explode(groupForABC(a,b,c,p));
            if q eq qFromGroup and ispSplit(a,b,c,p,q) then
              // if p ne 2 then
                print a,b,c;
                g := genusTriangularModularCurve(a,b,c,p,q,pm);
                print "genus", g;
                if g eq genus then
                  Append(~list,[a,b,c,p,q,pm]);
                end if;
              // else
              //   pass := PassportRepresentatives(PGL(2,q) : abc := [a,b,c]);
              //   if not #pass eq 0 then
              //     pm := -1;
              //     partition := pass[1][1];
              //     ramification := 0;
              //     for part in partition do
              //       ramification +:= &+[(j[1]-1)*(j[2]) : j in part];
              //     end for;
              //     g := (1/2)*(-2*(q+1)+ramification+2);
              //     print "(",a,b,c,")", g;
              //     if g eq genus then
              //       Append(~list,[a,b,c,2,q,pm]);
              //     end if;
              //   end if;
              // end if;
            end if;
          end if;
        end for;
      end for;
    end for;
  end for;
  return lexOrderABC(list);
end function;

//*****************************//
//       Composite level       //
//*****************************//

fixedPoints := function(x,a,b,c,p,q,pm)
  // Counts how many fixed points the action of x has on the quotient G/H_0.
  if not x eq 2 then
    if (q+1) mod x eq 0 then
      return 0;
    elif (q-1) mod x eq 0 then
      return 2;
    elif q mod x eq 0 then
      return 1;
    end if;
  elif pm eq 1 and p ne 2 then
    if q mod 4 eq 1 then
      return 2;
    else
      return 0;
    end if;
  end if;
  if pm eq -1 and p ne 2 then
    Mat := matricesTriple([a,b,c],q,pm);
    sigma2 := Mat[1];
    if IsIrreducible(CharacteristicPolynomial(sigma2)) then
      // The non-split semisimple case
      return 0;
    else
      // The split semisimple case
      return 2;
    end if;
  else
    // The case p=2, a=2
    return 1;
  end if;
end function;

genusDifferentPrimes := function(triples, fixedPoints2)
  a,b,c := Explode([triples[1][1],triples[1][2],triples[1][3]]);
  if a eq 2 then
    fix_a := &*fixedPoints2;
  else
    fix_a := &*[fixedPoints(a,a,b,c,t[4],t[5],t[6]) : t in triples];
  end if;
  fix_b := &*[fixedPoints(b,a,b,c,t[4],t[5],t[6]) : t in triples];
  fix_c := &*[fixedPoints(c,a,b,c,t[4],t[5],t[6]) : t in triples];
  degree := &*[t[5]+1 : t in triples];
  ram_a := (a-1)*(degree-fix_a)/a;
  ram_b := (b-1)*(degree-fix_b)/b;
  ram_c := (c-1)*(degree-fix_c)/c;
  return (1/2)*(-2*degree+ram_a+ram_b+ram_c +2);
end function;

// genusSamePrime := function(triple,power)
//   degree := ;
//
// end function;

primesAbove := function(t)
  a,b,c,p := Explode([t[1],t[2],t[3],t[4]]);
  E := SplittingField([MinimalPolynomial(lambda(a)),MinimalPolynomial(lambda(b)),MinimalPolynomial(lambda(c)),MinimalPolynomial(lambda(2*a)*lambda(2*b)*lambda(2*c))]);
  ZZE := RingOfIntegers(E);
  DE := Factorization(ideal<ZZE|ZZE!p>);
  numberOfPrimes := (#DE)*DE[1][2];
  return numberOfPrimes;
end function;

createNewList := function(lists)
  // Concatennates elements of lists that only differ by one element
  new:=[];
  checked := [];
  for i in [1..#lists] do
    if not i in checked then
      t := lists[i];
      Append(~checked, i);
      for j in [j: j in [(i+1)..#lists] | not j in checked] do
        S := Set(t cat lists[j]);
        if #S eq (#t+1) then
          Append(~new, SetToSequence(S));
          Append(~checked, j);
        end if;
      end for;
    end if;
  end for;
  return SetToSequence(Set(new));
end function;

fixedPointsWithGenus := function(t)
  if t[1] ne 2 then
    return fixedPoints(t[1],t[1],t[2],t[3],t[4],t[5],t[6]);
  end if;
  if t[4] eq 2 then
    return 1;
  end if;
  possibleG := (1/2)*(-2*(t[5]+1)+(t[5]+1)/2+e_x(t[2],t[5])+e_x(t[3],t[5])+2);
  if Floor(possibleG) eq t[7] then
    return 0;
  end if;
  return 2;
end function;

// Possibilities expects [a,b,c,p,q,g]
listCompositeGenusDifferentPrimes := function(possibilities, g)
  /*input: A list of [a,b,c,p,q] where the curve X_0 has genus <= g. A bound g on the genus
  output: A list of all curves [a,b,c,p_i,q_i] for 1<i where the curve X_0(a,b,c;\prod pp_1) has genus <=g.
  */
  lowGenus := <>;
  toCheck := possibilities;
  while #toCheck ne 0 do
    t := toCheck[1];
    sameTriple := [t];
    for i in [2..#toCheck] do
      if [toCheck[i][1],toCheck[i][2],toCheck[i][3]] eq [t[1],t[2],t[3]] then
        Append(~sameTriple, toCheck[i]);
      end if;
    end for;
    for poss in sameTriple do
      Exclude(~toCheck, poss);
    end for;
    // Add #fixed points for efficiency
    if #sameTriple ge 2 and t[1] eq 2 then
      fixedPts := [fixedPointsWithGenus(tp) : tp in sameTriple];
    else
      fixedPts := [-10 : tp in sameTriple];
    end if;
    if #sameTriple ge 2 then
      possibleSubsets := Subsequences(Set(sameTriple), 2);
      list2 := [i : i in possibleSubsets | i[1][4] lt i[2][4]];
      newList := list2;
      while #list2 ne 0 do
        newList := [];
        for triples in list2 do
          genus := genusDifferentPrimes(triples,[fixedPts[Position(sameTriple,tt)] : tt in triples]);
          if genus le g then
            Append(~newList,triples);
            if genus eq g then
              Append(~lowGenus,triples);
            end if;
          end if;
        end for;
        list2 := createNewList(newList);
      end while;
    end if;
  end while;
  return lowGenus;
end function;

listCompositeGenusSameRationalPrimes := function(possibilities, g)
  lowGenus := <>;
  for t in possibilities do
    n := primesAbove(t);
    if n ge 2 then
      fixedPts := fixedPointsWithGenus(t);
      for i in [2..n] do
        genus := genusDifferentPrimes([t : j in [1..i]],[fixedPts : j in [1..i]]);
        if genus le g then
          if genus eq g then
            Append(~lowGenus,[t : j in [1..i]]);
          end if;
        else
          break;
        end if;
      end for;
    end if;
  end for;
  return lowGenus;
end function;

isHyperbolicInfinity := function(a,b,c,p)
  chi := -1;
  for s in [a,b,c] do
    if s ne p then
      chi+:=1/s;
    end if;
  end for;
  if chi lt 0 then
    return true;
  end if;
  return false;
end function;

stringWithInf:=function(a,b,c,p)
  st:="";
  inf:=0;
  for s in [a,b,c] do
    if s ne p then
      st cat:= IntegerToString(s) cat ",";
    else
      inf+:=1;
    end if;
  end for;
  st cat:= &cat["inf," : i in [1..inf]];
  return st;
end function;

listNonCocompact := function(possibleTriples,g)
  genusG:=[];
  // First, look for the triples that are hyperbolic only when adding infinity instead of p
  boundq:=qMax(g);
  sphericalEuclidean:=[[2,2,n]:n in [2..boundq]] cat [[2,3,3],[2,3,4],[2,3,5],[2,3,6],[2,4,4],[3,3,3]];
  for t in sphericalEuclidean do
    check := [s : s in t|IsPrime(s) and s ne 2];
    for s in check do
      if #[v : v in t| v mod s eq 0 and not IsPrime(v)] eq 0 and isHyperbolicInfinity(t[1],t[2],t[3],s) then
        q,pm:=Explode(groupForABC(t[1],t[2],t[3],s));
        print t,s,genusTriangularModularCurve(t[1],t[2],t[3],s,q,pm);
        if isQAdmissible(t[1],t[2],t[3],s,q) and genusTriangularModularCurve(t[1],t[2],t[3],s,q,pm) eq g then
          st:="[" cat stringWithInf(t[1],t[2],t[3],s) cat IntegerToString(s) cat",";
          st cat:= IntegerToString(q) cat "," cat IntegerToString(pm)cat"]";
          Append(~genusG,st);
        end if;
      end if;
    end for;
  end for;
  // Now look for the triples that are already hyperbolic
  for t in possibleTriples do
    a,b,c,p:=Explode([t[1],t[2],t[3],t[4]]);
    if p in [a,b,c] then
      st := "[" cat stringWithInf(a,b,c,p);
      st cat:= IntegerToString(p)cat "," cat IntegerToString(t[5]) cat "," cat IntegerToString(t[6])cat"]";
      Append(~genusG,st);
    end if;
  end for;
  return SetToSequence(SequenceToSet(genusG));
end function;
