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

genusCompositeX1:=function(list,powers)
  a,b,c:=Explode([list[1][1],list[1][2],list[1][3]]);
  N := &*[list[i][4]^powers[i]: i in [1..#list]];
  degree := (EulerPhi(N)/2) * &*[list[i][5]^powers[i]+list[i][5]^(powers[i]-1) : i in [1..#list]];
  if &and[l[4]in[l[1],l[2],l[3]] : l in list] and &and[list[1][4] eq l[4] : l in list] and SequenceToSet(powers) eq {1} then
    // This is the rare case
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
