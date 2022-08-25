load "matrices.m";
load "listOrganizer.m";
// Attach("tri-congruence.m");


//*****************************//
//        Miscellaneous        //
//*****************************//
lambda := function(s)
/*  Input: an integer s.
    Ourput: lambda(s)=zeta_s+zeta_s^{-1}, where zeta_s is a primitive s-th root of 1.*/
  return RootOfUnity(s)+(1/RootOfUnity(s));
end function;

lambdaZeta := function(zeta,m,s)
// Input: 2m-th root of 1, an integer s.
// Ourput: lambda(s)=zeta_s+zeta_s^{-1}, where zeta_s is computed from the 2m-th root of 1 given.
  return Parent(zeta)!(zeta^((2*m) div s)+(zeta^((2*m) div s))^(-1));
end function;

//*****************************//
//  Triple (a,b,c) conditions  //
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
//     Group of definition     //
//*****************************//

groupForABC := function(a,b,c,p)
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
  genF := [lambdaZeta(zeta_twom,m,2*s) : s in [a,b,c] | s mod p ne 0];
  genE := [lambdaZeta(zeta_twom,m,s) : s in [a,b,c] | s mod p ne 0];
  lastE := k!1;
  for s in [s : s in [a,b,c] | s mod p ne 0] do
    lastE *:= lambdaZeta(zeta_twom,m,2*s);
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
end function;

//*****************************//
//         Ramification        //
//*****************************//

e_x := function(x,q)
// Given an integer x>1, it computes the ramification degree associated to sigma_a.
// This uses Lemma 3.1 of [DR. & V.]
  if q mod x eq 0 then
    return (q/x)*(x-1);
  elif (q+1) mod x eq 0 then
    return ((q+1)/x)*(x-1);
  elif (q-1) mod x eq 0 then
    return ((q-1)/x)*(x-1);
  end if;
end function;

ramificationFromMatrix := function(M,q)
  if IsIrreducible(CharacteristicPolynomial(M)) then
    // The non-split semisimple case
    return (q+1)/2;
  else
    // The split semisimple case
    return (q-1)/2;
  end if;
end function;

ramificationTriple := function(a,b,c,p,q,pm)
// Computes the ramification of the cover X_0(a,b,c;p)->P^1
  if p eq 2 then
    return &+[e_x(s,q) : s in [a,b,c]];
  end if;
  // This is the hardest case. We cannot defice the ramification from only knowing that the genus is in ZZ
  if [a,b] eq [2,2] then
    sigmas := matricesTriple([a,b,c],q,pm);
    return &+[ramificationFromMatrix(sigmas[i],q) : i in[1..3]];
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
    // Now anyting can happen. We can use matrices, or check g is an integer.
    // The latter is more efficient
      r := (q+1)/2+e_x(b,q)+e_x(c,q);
      if Floor((1/2)*(-2*(q+1)+r+2)) eq ((1/2)*(-2*(q+1)+r+2)) then
        return (q+1)/2+e_x(b,q)+e_x(c,q);
      else;
        return (q-1)/2 +e_x(b,q)+e_x(c,q);
      end if;
      // Mat := matricesTriple([a,b,c],q,pm);
      // sigma2 := Mat[1];
      // if IsIrreducible(CharacteristicPolynomial(sigma2)) then
      //   // The non-split semisimple case
      //   return (q+1)/2+e_x(b,q)+e_x(c,q);
      // else
      //   // The split semisimple case
      //   return (q-1)/2+e_x(b,q)+e_x(c,q);
      // end if;
    end if;
  end if;
end function;

//*****************************//
//           Bounds            //
//*****************************//

// Come from Section 3 of [DR. & V.]. In particular, Proposition 3.11.
qBound := function(a,b,c,g0)
  chi := 1-(1/a+1/b+1/c);
  return Ceiling(2*(g0+1)/chi+1);
end function;

cBound := function(a,b,q,g0)
  lhs := 1-1/a-1/b-2*(g0+1)/(q-1);
  if lhs le 0 then
    // There is no bound on c given by this inequality
    return Infinity();
  else
    return Floor(1/lhs);
  end if;
end function;

qMax := function(g)
  return 2*42*(g+1)+1;
end function;


//*****************************//
//            Genus            //
//*****************************//
genusTriangularModularCurve := function(a,b,c,p : q := -1, pm := 0)
  // Theorem 3.3 of [DR. & V.]
  if q eq -1 then
    q, pm := Explode(groupForABC(a,b,c,p));
  end if;
  r := ramificationTriple(a,b,c,p,q,pm);
  return (1/2)*(-2*(q+1)+r+2);
end function;

isQAdmissible := function(a,b,c,p,q)
  return &and[((q+1) mod s)*((q-1) mod s) eq 0 or s eq p : s in [a,b,c]];
end function;

ispSplit := function(a,b,c,p,q)
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
end function;



// fixedPointsWithGenus := function(t)
//   if t[1] ne 2 then
//     return fixedPoints(t[1],t[1],t[2],t[3],t[4],t[5],t[6]);
//   end if;
//   if t[4] eq 2 then
//     return 1;
//   end if;
//   possibleG := (1/2)*(-2*(t[5]+1)+(t[5]+1)/2+e_x(t[2],t[5])+e_x(t[3],t[5])+2);
//   if Floor(possibleG) eq t[7] then
//     return 0;
//   end if;
//   return 2;
// end function;


//***********************************************//
//              Non-cocompact case               //
//***********************************************//

isHyperbolicInfinity := function(t,changeP,p)
  // Input: a triple t. A boolean triple t, a prime p.
  // Output: Checks if the triple t is hyperbolic, when changeP dictates what entries in t are changed to infinity.
  chi := -1;
  for i in [1..3] do
    s:=t[i];
    if s ne p or not changeP[i] then
      chi+:=1/s;
    end if;
  end for;
  if chi lt 0 then
    return true;
  end if;
  return false;
end function;

stringWithInf:=function(t,changeP,p)
  // Input: a triple t. A boolean triple t, a prime p.
  // Output: Returns a sting of a triple whrn t is changed as dictated by changeP.
  a,b,c := Explode(t);
  st:="";
  inf:=0;
  for i in [1..3] do
    s :=t[i];
    assert (s ne p and not changeP[i]) or s eq p;
    if not changeP[i] then
      st cat:= IntegerToString(s) cat ",";
    else
      inf+:=1;
    end if;
  end for;
  if inf eq 0 then
    return st;
  else
    if inf eq 1 then
      return st cat "inf";
    else
      return st cat &cat["inf," : i in [1..(inf-1)]] cat "inf";
    end if;
  end if;
end function;

changeP := function(t,p)
  triplesChangep := [];
  changed:=1;
  while changed le #[s:s in t|s eq p] do
    tri := [];
    ci := 0;
    for i in [1..3] do
      if t[i] ne p or ci ge changed then
        Append(~tri,false);
      else
        Append(~tri, true);
        ci+:=1;
      end if;
    end for;
    Append(~triplesChangep,tri);
    changed+:=1;
  end while;
  return triplesChangep;
end function;

isExceptional := function(a,b,c)
  if a eq b and a eq 2 then
    return true;
  else
    return [a,b,c] in [[2,3,3],[3,3,3],[3,4,4],[2,3,4],[2,5,5],[5,5,5],[3,3,5],[3,5,5],[2,3,5]];
  end if;
end function;

listBoundedGenusNonCocompact := function(g)
  genusG:=[];
  // First, look for the triples that are hyperbolic only when adding infinity instead of p
  boundq := qMax(g);
  // print boundq;
  sphericalEuclidean := [[2,2,n] : n in [2..boundq]] cat [[2,3,3],[2,3,4],[2,3,5],[2,3,6],[2,4,4],[3,3,3]];
  for t in sphericalEuclidean do
    check := [s : s in t|IsPrime(s)];
    for p in check do
      if &or[isHyperbolicInfinity(t,change,p) : change in changeP(t,p)] then
        q,pm := Explode(groupForABC(t[1],t[2],t[3],p));
        for change in changeP(t,p) do
          if #[v : v in t| v mod p eq 0 and not IsPrime(v)] eq 0 and isHyperbolicInfinity(t,change,p) then
            if q le boundq then
              if not isExceptional(t[1],t[2],t[3]) then
                genus := genusTriangularModularCurve(t[1],t[2],t[3],p:q:=q,pm:=pm);
                // print genus, t, stringWithInf(t,change,p);
                if isQAdmissible(t[1],t[2],t[3],p,q) and ispSplit(t[1],t[2],t[3],p,q) and genus eq g then
                  st:="[" cat stringWithInf(t,change,p) cat "," cat IntegerToString(p) cat",";
                  st cat:= IntegerToString(q) cat "," cat IntegerToString(pm)cat"]";
                  Append(~genusG,st);
                end if;
              end if;
            end if;
          end if;
        end for;
      end if;
    end for;
  end for;
  return SetToSequence(SequenceToSet(genusG));
end function;

//************************************************//
//                  Enumeration                   //
//************************************************//

//*****************************//
//         prime case          //
//*****************************//
listBoundedGenusCocompact := function(genus)
  list:=[[]:i in [0..genus]];
  boundq := qMax(genus);
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
        cbound := cBound(a,b,q,genus);
        for k in [j..#possibilities] do
          c := possibilities[k];
          if c le cbound and isHyperbolic(a,b,c) and isQAdmissible(a,b,c,p,q) then
            qFromGroup, pm := Explode(groupForABC(a,b,c,p));
            if q eq qFromGroup and ispSplit(a,b,c,p,q) then
              // print a,b,c;
              g := genusTriangularModularCurve(a,b,c,p:q:=q,pm:=pm);
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
  return [lexOrderABC(list[i]):i in [1..genus+1]];
end function;

countBoundedGenus := function(genus)
  L := listBoundedGenusCocompact(genus);
  return [#L[i]+#listBoundedGenusNonCocompact(i-1): i in [1..#L]];
end function;
