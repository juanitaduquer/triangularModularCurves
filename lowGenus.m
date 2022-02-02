// load "matrices.m";
load "listOrganizer.m";
// AttachSpec("~/Documents/Code/Belyi/Code/spec");

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

isCommutative := function(a,b,c)
// Given a triple (a,b,c), it returns true if the triple is commutative and false otherwise.
  beta := lambda(2*a)^2 +lambda(2*b)^2 + lambda(2*c)^2 -lambda(2*a)*lambda(2*b)*lambda(2*c)-4;
  if beta eq 0 then
    return true;
  end if;
  return false;
end function;

isProjective := function(a,b,c)
// Given a triple (a,b,c), it returns true if the triple is projective and false otherwise.
  exceptional_triples:=[[2,3,3],[3,3,3],[3,4,4],[2,3,4],[2,5,5],[5,5,5],[3,3,5],[3,5,5],[2,3,5]];
  if [a,b,c] in exceptional_triples then
    return false;
  elif isCommutative(a,b,c) then
    return false;
  end if;
  return true;
end function;

//*****************************//
//     Group of definition     //
//*****************************//

// SetDebugOnError(true);
groupForABC := function(a,b,c,p)
// Input: a hyperbolic projective triple [a,b,c] and an integer bound
// Output: q leq bound (if possible) such that G is as in Theorem A (Clark and Voight)
  m := Lcm([a,b,c]);
  m div:= p^Valuation(m,p);
  power := Order(p,2*m);
  bigPower := p^power;
  k := GF(bigPower);
  zeta_2m := Roots(CyclotomicPolynomial(2*m),k)[1][1];
  genF := [lambdaZeta(zeta_2m,m,2*s) : s in [a,b,c] | s mod p ne 0];
  genE := [lambdaZeta(zeta_2m,m,s) : s in [a,b,c] | s mod p ne 0];
  lastE := k!1;
  for s in [a,b,c] do
    if s mod p ne 0 then
      lastE *:= lambdaZeta(zeta_2m,m,2*s);
    end if;
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
// This uses Lemmas TODO: find lemmas on the paper
  assert x ne 2;
  if (q+1) mod x eq 0 then
    return (q+1)*(x-1)/x;
  elif (q-1) mod x eq 0 then
    return (q-1)*(x-1)/x;
  elif q mod x eq 0 then
    return q*(x-1)/x;
  end if;
end function;

ramificationTriple := function(a,b,c,p,q,pm)
// Computes the ramification of the cover X_0(a,b,c;p)->P^1
  if a ne 2 then
    return e_x(a,q)+e_x(b,q)+e_x(c,q);
  else
    if pm eq 1 then
      if q mod 4 eq 1 then
        return (q-1)/2+e_x(b,q)+e_x(c,q);
      else
        return (q+1)/2+e_x(b,q)+e_x(c,q);
      end if;
    else
      // if q mod 4 eq 1 then
      //   return (q-1)/2+e_x(b,q)+e_x(c,q);
      // end if;
      // Now any option can happen. We also need to make sure that the triple
      // generates the group G and not just a subgroup
      // Mat := matricesTriple([a,b,c],q,pm);
      // sigma2 := Mat[1];
      // if sigma2[1][1] ne 0 then
      //   return (q-1)/2+e_x(b,q)+e_x(c,q);
      // end if;
      // return (q+1)/2+e_x(b,q)+e_x(c,q);
      // print "We are computing passportReps";
      pass := PassportRepresentatives(PGL(2,q):abc:=[a,b,c]);
      partition := pass[1][1];
      ramification := 0;
      for i in partition do
        for j in i do
          ramification := ramification + (j[1]-1)*(j[2]);
        end for;
      end for;
      return ramification;
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
//          Low genus          //
//*****************************//

genusTriangularModularCurve := function(a,b,c,p)
  group := groupForABC(a,b,c,p);
  q := group[1];
  pm := group[2];
  try
    r := ramificationTriple(a,b,c,p,q,pm);
    return (1/2)*(-2*(q+1)+r+2), q, pm;
  catch e
    error "no genus";
  end try;
end function;

isRamified := function(a,b,c,p)
  Delta := TriangleGroup(a,b,c);
  A := QuaternionAlgebra(Delta);
  E := BaseField(A);
  ZZE := Integers(E);
  pp := p*ZZE;
  if not pp in RamifiedPlaces(A) then
    return false;
  end if;
  return true;
end function;

isQAdmissible := function(a,b,c,p)
  qAdm := true;
  for s in [a,b,c] do
    if s mod p eq 0 then
      if s ne p then
        qAdm := false;
      end if;
    end if;
  end for;
  return qAdm;
end function;

listBoundedGenus := function(genus)
  list:=[];
  boundq := qMax(genus);
  powers := [ n : n in [2..boundq] | IsPrimePower(n) ];
  for q in powers do
    if q mod 2 ne 0 then
      possibilities := Set(Divisors(q) cat Divisors(q+1) cat Divisors(q-1));
      Exclude(~possibilities,1);
      p := PrimeDivisors(q)[1];
      possibilities := Sort(SetToSequence(possibilities));
      print "Possibilities for q=",q," are ",possibilities;
      for i in [1..#possibilities] do
        a := possibilities[i];
        for j in [i..#possibilities] do
          b:= possibilities[j];
          cbound := cBound(a,b,q);
          for k in [j..#possibilities] do
            c:=possibilities[k];
            if c le cbound and isHyperbolic(a,b,c) and isProjective(a,b,c) then
              if (2*a*b*c) mod p ne 0 then
                print a,b,c;
                g,qPower,pm := genusTriangularModularCurve(a,b,c,p);
                print "genus", g;
                if q eq qPower and g eq genus then
                  Append(~list,[a,b,c,p,q,pm]);
                end if;
              elif (a*b*c) mod p eq 0 then
                // Check if p is uramified in the quaternion algebra
                print a,b,c;
                print "p", p;
                if not isRamified(a,b,c,p) and isQAdmissible(a,b,c,p) then
                  g,qPower,pm := genusTriangularModularCurve(a,b,c,p);
                  print "genus", g;
                  if q eq qPower and g eq genus then
                    Append(~list,[a,b,c,p,q,pm]);
                  end if;
                end if;
              end if;
            end if;
          end for;
        end for;
      end for;
    else
      possibilities := Set(Divisors(2) cat Divisors(q+1) cat Divisors(q-1));
      Exclude(~possibilities,1);
      p := 2;
      possibilities := Sort(SetToSequence(possibilities));
      print "Possibilities for q=",q," are ",possibilities;
      for i in [1..#possibilities] do
        a := possibilities[i];
        for j in [i..#possibilities] do
          b:= possibilities[j];
          cbound := cBound(a,b,q);
          for k in [j..#possibilities] do
            c:=possibilities[k];
            if c le cbound and isHyperbolic(a,b,c) and isQAdmissible(a,b,c,p) and not isRamified(a,b,c,p) then
              pass := [];
              pm := 0;
              passPSL := PassportRepresentatives(PSL(2,q) : abc := [a,b,c]);
              if not #passPSL eq 0 then
                pass := passPSL;
                pm := 1;
              else
                passPGL := PassportRepresentatives(PGL(2,q) : abc := [a,b,c]);
                if not #passPGL eq 0 then
                  pass := passPGL;
                  pm := -1;
                end if;
              end if;
              if not #pass eq 0 then
                partition := pass[1][1];
                ramification := 0;
                for i in partition do
                  for j in i do
                    ramification := ramification + (j[1]-1)*(j[2]);
                  end for;
                end for;
                g := (1/2)*(-2*(q+1)+ramification+2);
                print "(",a,b,c,")", g;
                if g eq genus then
                  Append(~list,[a,b,c,2,q,pm]);
                end if;
              end if;
            end if;
          end for;
        end if;
      end for;
    end for;
  end for;
  return lexOrderABC(list);
end function;
