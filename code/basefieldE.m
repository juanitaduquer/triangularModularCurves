ks := function(a,b,c : E := true);
  m := Lcm([a,b,c]);
  startks := [k : k in [1..2*m-1] | k mod a in [1,a-1] and k mod b in [1,b-1] and 
                               k mod c in [1,c-1]];  // if slow, use CRT
  if not E then return startks; end if;  // gives F
  return [k : k in startks | 
     (k mod (2*a) in [a+1,a-1] and k mod (2*b) in [1,2*b-1] and k mod (2*c) in [1,2*c-1]) or 
     (k mod (2*b) in [b+1,b-1] and k mod (2*c) in [1,2*c-1] and k mod (2*a) in [1,2*a-1]) or 
     (k mod (2*c) in [c+1,c-1] and k mod (2*a) in [1,2*a-1] and k mod (2*b) in [1,2*b-1]) or 
     (k mod (2*a) in [a+1,a-1] and k mod (2*b) in [b+1,b-1] and k mod (2*c) in [c+1,c-1])];
end function;
       
lambdaminpol := function(s);
  K<z> := CyclotomicField(s);
  return MinimalPolynomial(z+z^(-1));
end function;

intrinsic BaseFieldE(a::RngIntElt, b::RngIntElt, c::RngIntElt) -> FldNum
  {Returns the field E = E(a,b,c).}

  QQ := Rationals();
  Estep := QQ;
  l2s := [];
  for s in [a,b,c] do
    f := Factorization(lambdaminpol(s),Estep)[1][1];
    if Degree(f) gt 1 then
      Estep := ext<Estep | f>;
      l2s := ChangeUniverse(l2s, Estep);
      Append(~l2s, Estep.1);
    else
      Append(~l2s, Roots(f,Estep)[1][1]);
    end if;
  end for;
  
  l2spol := Polynomial([-(l2s[1]+2)*(l2s[2]+2)*(l2s[3]+2),0,1]);
  f := Factorization(l2spol, Estep)[1][1];
  if Degree(f) gt 1 then
    EA := ext<Estep | f>;
    l2s := ChangeUniverse(l2s, EA);
    Append(~l2s, EA.1);
  else
    EA := Estep;
    Append(~l2s, Roots(f,EA)[1][1]);
  end if;
  
  EAabs0 := AbsoluteField(EA);
  l2s := ChangeUniverse(l2s, EAabs0);  
  try
    EAabs, iota := Polredabs(EAabs0);
    l2s := [iota(l2) : l2 in l2s];
  catch e;
  end try;
  return EAabs, l2s;
end intrinsic;

lambdaminpol := function(s);
  K<z> := CyclotomicField(s);
  return MinimalPolynomial(z+z^(-1));
end function;

intrinsic GroupForABCUsingAb(a::RngIntElt,b::RngIntElt,c::RngIntElt,p::RngIntElt) -> SeqEnum
  {Returns the size q of the residue field of a prime of E(a,b,c) above p and 1 or -1 if the associated group is PSL_2(Fq) or PGL_2(Fq) respectively.}

	QQ := RationalsAsNumberField();
	ZZ := Integers(QQ);
	m := Lcm([a,b,c]);
	Cl, mCl := RayClassGroup(2*m*ZZ, [1]);
	H := sub<Cl | [(k*ZZ)@@mCl : k in ks(a,b,c)]>;
	q, mq := quo<Cl | H>;
	phi := Inverse(mq)*mCl;
	A := AbelianExtension(phi);
  decompE := DecompositionType(A,p*ZZ);

	H := sub<Cl | [(k*ZZ)@@mCl : k in ks(a,b,c : E := false)]>;
	q, mq := quo<Cl | H>;
	phi := Inverse(mq)*mCl;
	A := AbelianExtension(phi);
  decompF := DecompositionType(A,p*ZZ);

  degE := decompE[1][1];
  degF := decompF[1][1];
  if degF eq degE then
    return [p^degE,1];
  end if;
  return [p^degE,-1];    
end intrinsic;
