sameCoset := function(M1,M2)
  if [M1[1][1],M1[2][1]] eq [M2[1][1],M2[2][1]] or [M1[1][1],M1[2][1]] eq [-M2[1][1],-M2[2][1]] then
    if IsSquare(Determinant(M1)) eq IsSquare(Determinant(M2)) then
      return true;
    end if;
  end if;
  return false;
end function;

lengthOrbit := function(sigma,M)
  sigmaM := sigma*M;
  i := 1;
  while not sameCoset(sigmaM,M) and i le 10 do
    sigmaM := sigma*sigmaM;
    i:=i+1;
  end while;
  return i;
end function;

allCosets := function(p)
  G := SL(2,p);
  matrices := [];
  lists := [];
  for M in G do
    if not <M[1][1],M[2][1],IsSquare(Determinant(M))> in lists then
      Append(~lists, <M[1][1],M[2][1],IsSquare(Determinant(M))>);
      Append(~matrices, M);
    end if;
  end for;
  return matrices;
end function;

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

genusX1:= function(t)
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
