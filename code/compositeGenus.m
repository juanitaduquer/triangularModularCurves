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

genusSamePrime := function(triple,power)
  degree := ;

end function;

lambda := function(s)
// Input: an integer s. Ourput: lambda(s)=zeta_s+zeta_s^{-1}
  return RootOfUnity(s)+(1/RootOfUnity(s));
end function;

primesAbove := function(t)
  a,b,c,p := Explode([t[1],t[2],t[3],t[4]]);
  E := SplittingField([MinimalPolynomial(lambda(a)),MinimalPolynomial(lambda(b)),MinimalPolynomial(lambda(c)),MinimalPolynomial(lambda(2*a)*lambda(2*b)*lambda(2*c))]);
  ring_of_int_E := RingOfIntegers(E);
  D_E := Factorization(ideal<ring_of_int_E|ring_of_int_E!p>);
  numberOfPrimes := (#D_E)*D_E[1][2];
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
    print sameTriple;
    // Add #fixed points for efficiency
    if #sameTriple ge 2 and t[1] eq 2 then
      fixedPts := [fixedPoints(2,tp[1],tp[2],tp[3],tp[4],tp[5],tp[6]) : tp in sameTriple];
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
        print list2;
      end while;
    end if;
  end while;
  return lowGenus;
end function;

listCompositeGenusSamePrimes := function(possibilities, g)
  lowGenus := <>;
  for t in possibilities do
    n := primesAbove(t);
    if n ge 2 then
      fixedPts := fixedPoints(t[1],t[1],t[2],t[3],t[4],t[5],t[6]);
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
