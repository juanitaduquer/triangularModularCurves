ramificationX1 := function(s,fixedPtsX0,deg,q,pm)
  if fixedPtsX0 eq 0 then
    return (deg)*(s-1)/s;
  elif fixedPtsX0 eq 1 then
    if pm eq 1 then
      return (deg-(q-1)/2)*(s-1)/s;
    else
      return (deg-(q-1))*(s-1)/s;
    end if;
  elif fixedPtsX0 eq 2 then
    return (deg)*(s-1)/s;
  end if;
end function;

genusX1 := function(t)
  a,b,c,p,q,pm:=Explode([t[1],t[2],t[3],t[4],t[5],t[6]]);
  if pm eq 1 then
    deg := (q^2 -1)/2;
  else
    deg := q^2-1;
  end if;
  fixedPtsA := fixedPointsWithGenus(t);
  r:= ramificationX1(t[1],fixedPtsA,deg,q,pm)+ramificationX1(b,fixedPoints(b,a,b,c,p,q,pm),deg,q,pm)+ramificationX1(c,fixedPoints(c,a,b,c,p,q,pm),deg,q,pm);
  return (1/2)*(-2*deg+r+2);
end function;

fixedPtsX1 := function(s,p,q,pm)
  if pm eq 1 then
    return (q-1)/2;
  else
    return (q-1);
  end if;
end function;

genusCompositeX1:=function(list,powers)
  a,b,c:=Explode([list[1][1],list[1][2],list[1][3]]);
  N := &*[list[i][4]^powers[i]: i in [1..#list]];
  degree := (EulerPhi(N)/2) * &*[list[i][5]^powers[i]+list[i][5]^(powers[i]-1) : i in [1..#list]];
  if &and[l[4]in[l[1],l[2],l[3]] : l in list] and &and[list[1][4] eq l[4] : l in list] and SequenceToSet(powers) eq {1} then
    return (degree*((1-1/a-1/b-1/c)/2))+1 - &+[&*[fixedPtsX1(s,list[i][4],list[i][5],list[i][6]) : i in [1..#list]] : s in [a,b,c] | s eq list[1][4]];
  else
    return (degree*((1-1/a-1/b-1/c)/2))+1;
  end if;
end function;

listFixedGenusX1 := function(possibilities,g)
  lowGenus := [];
  for t in possibilities do
    genus := genusX1(t);
    if genus eq g then
      Append(~lowGenus,t);
    end if;
  end for;
  return lowGenus;
end function;

listCompositeGenusX1 := function(possibilities, g)
  /*input: A list of [a,b,c,p,q] where the curve X_0 has genus <= g. A bound g on the genus
  output: A list of all curves [a,b,c,p_i,q_i] where the curve X_1(a,b,c;prod p_i^e_i) has genus <=g.
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
    if #sameTriple ge 2 then
      possibleSubsets := Subsequences(Set(sameTriple), 2);
      list2 := [i : i in possibleSubsets | i[1][4] lt i[2][4]];
      newList := list2;
      while #list2 ne 0 do
        newList := [];
        for triples in list2 do
          genus := genusCompositeX1(triples,[1: i in triples]);
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

listCompositeGenusSameRationalPrimesX1 := function(possibilities, g)
  lowGenus := <>;
  for t in possibilities do
    n := primesAbove(t);
    if n ge 2 then
      for i in [2..n] do
        genus := genusCompositeX1([t : j in [1..i]],[1 : j in [1..i]]);
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

listCompositeGenusSamePrimesX1 := function(possibilities, g)
  lowGenus := <>;
  boundq:=qMax(g);
  for t in possibilities do
    for e in [e : e in [2..boundq]|t[5]^e+t[5]^(e-1)le boundq] do
      genus := genusCompositeX1([t],[e]);
      if genus le g then
        if genus eq g then
          Append(~lowGenus,Append(t,e));
        end if;
      else
        break;
      end if;
    end for;
  end for;
  return lowGenus;
end function;


listNonCocompactX1 := function(possibleTriples,g)
  genusG:=[];
  // First, look for the triples that are hyperbolic only when adding infinity instead of p
  boundq := qMax(g);
  sphericalEuclidean := [[2,2,n] : n in [2..boundq]] cat [[2,3,3],[2,3,4],[2,3,5],[2,3,6],[2,4,4],[3,3,3]];
  for t in sphericalEuclidean do
    check := [s : s in t|IsPrime(s)];
    for p in check do
      if &or[isHyperbolicInfinity(t,change,p) : change in changeP(t,p)] then
        q,pm := Explode(groupForABC(t[1],t[2],t[3],p));
        for change in changeP(t,p) do
          if #[v : v in t| v mod p eq 0 and not IsPrime(v)] eq 0 and isHyperbolicInfinity(t,change,p) then
            if q le boundq then
              if (p eq 2 and t eq [2,2,3]) or p ne 2 then
                genusX0 := genusTriangularModularCurve(t[1],t[2],t[3],p,q,pm);
                genus := genusX1(Append([t[1],t[2],t[3],p,q,pm],genusX0));
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
  // Now look for the triples that are already hyperbolic
  for t in possibleTriples do
    a,b,c,p:=Explode([t[1],t[2],t[3],t[4]]);
    for change in changeP([a,b,c],p) do
      st := "[" cat stringWithInf([a,b,c],change,p);
      st cat:= IntegerToString(p)cat "," cat IntegerToString(t[5]) cat "," cat IntegerToString(t[6])cat"]";
      Append(~genusG,st);
    end for;
  end for;
  return SetToSequence(SequenceToSet(genusG));
end function;
