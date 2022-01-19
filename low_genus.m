load "matrices.m";

lambda := function(s)
// Input: an integer s. Ourput: lambda(s)=zeta_s+zeta_s^{-1}
  return RootOfUnity(s)+(1/RootOfUnity(s));
end function;

lambda_zeta := function(zeta,m,s)
// Input: 2m-th root of 1, an integer s.
// Ourput: lambda(s)=zeta_s+zeta_s^{-1}, where zeta_s is computed from the root of 1.
  return Parent(zeta)!(zeta^((2*m) div s)+(zeta^((2*m) div s))^(-1));
end function;

//*****************************//
//    Triple conditions        //
//*****************************//
is_hyperbolic := function(a,b,c)
  // Given a triple (a,b,c), it returns true if the triple is hyperbolic.
  if (1/a+1/b+1/c-1) lt 0 then
    return true;
  else
    return false;
  end if;
end function;

is_commutative := function(a,b,c)
// Given a triple (a,b,c), it returns true if the triple is commutative and false otherwise.
  beta := lambda(2*a)^2 +lambda(2*b)^2 + lambda(2*c)^2 -lambda(2*a)*lambda(2*b)*lambda(2*c)-4;
  if beta eq 0 then
    return true;
  end if;
  return false;
end function;

is_projective := function(a,b,c)
// Given a triple (a,b,c), it returns true if the triple is projective and false otherwise.
  exceptional_triples:=[[2,3,3],[3,3,3],[3,4,4],[2,3,4],[2,5,5],[5,5,5],[3,3,5],[3,5,5],[2,3,5]];
  if [a,b,c] in exceptional_triples then
    return false;
  elif is_commutative(a,b,c) then
    return false;
  end if;
  return true;
end function;

//*****************************//
//     Group of definition     //
//*****************************//

// SetDebugOnError(true);
group_for_abc := function(a,b,c,p,bound)
// Input: a hyperbolic projective triple [a,b,c] and an integer bound
// Output: q leq bound (if possible) such that G is as in Theorem A (Clark&Voight)
  m := Lcm([a,b,c]);
  m div:= p^Valuation(m,p);
  power := Order(p,2*m);
  bigPower := p^power;
  k := GF(bigPower);
  zeta_2m := Roots(CyclotomicPolynomial(2*m),k)[1][1];
  F := sub <k|lambda_zeta(zeta_2m,m,2*a),lambda_zeta(zeta_2m,m,2*b),lambda_zeta(zeta_2m,m,2*c)>;
  E := sub <k|lambda_zeta(zeta_2m,m,a),lambda_zeta(zeta_2m,m,b),lambda_zeta(zeta_2m,m,c),lambda_zeta(zeta_2m,m,2*a)*lambda_zeta(zeta_2m,m,2*b)*lambda_zeta(zeta_2m,m,2*c)>;
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
  error "Not an admissible triple";
end function;

ramification_triple := function(a,b,c,p,q,pm)
// Computes the ramification of the cover X_0(a,b,c;p)->P^1
  if a ne 2 then
    return e_x(a,q)+e_x(b,q)+e_x(c,q);
  else
    if pm eq 1 then
      if p mod 4 eq 1 then
        return (q-1)/2+e_x(b,q)+e_x(c,q);
      else
        return (q+1)/2+e_x(b,q)+e_x(c,q);
      end if;
    else
      if p mod 4 eq 1 then
        return (q-1)/2+e_x(b,q)+e_x(c,q);
      end if;
      // Now any option can happen. It all depends on the charpoly being reducible or not
      // This is the same as det is a square or not.
      Mat := matrices_triple([a,b,c],q,pm);
      sigma2 := Mat[1];
      d := Determinant(sigma2);
      if IsSquare(d) then
        return (q-1)/2+e_x(b,q)+e_x(c,q);
      end if;
      return (q+1)/2+e_x(b,q)+e_x(c,q);
    end if;
  end if;
end function;

//*****************************//
//           Bounds            //
//*****************************//

q_bound := function(a,b,c)
  chi := 1-(1/a+1/b+1/c);
  return Ceiling(4/chi+1);
end function;

c_bound := function(a,b,q)
  lhs := 1-1/a-4/(q-1) -1/b;
  if lhs le 0 then
    return q+1;
  else
    return Floor(1/lhs+1);
  end if;
end function;

q_max := function(g)
  return 2*42*(g+1)+1;
end function;

//*****************************//
//          Low genus          //
//*****************************//

genus_triangular_modular_curve := function(a,b,c,p,bound)
  group := group_for_abc(a,b,c,p,bound);
  print "Found group";
  q := group[1];
  pm := group[2];
  return (1/2)*(-2*(q+1)+ramification_triple(a,b,c,p,q,pm)+2), q, pm;
end function;

list_bounded_genus := function(boundG)
  list:=[];
  boundq := q_max(boundG);
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
          cbound := c_bound(a,b,q);
          for k in [j..#possibilities] do
            c:=possibilities[k];
            if c le cbound and is_hyperbolic(a,b,c) and is_projective(a,b,c) and (2*a*b*c) mod p ne 0 then
              print a,b,c;
              g,qPower,pm:=genus_triangular_modular_curve(a,b,c,p,boundq);
              if q eq qPower then
                if g eq boundG then
                  Append(~list,[a,b,c,p,q,pm]);
                end if;
              end if;
            end if;
          end for;
        end for;
      end for;
    end if;
  end for;
  return list;
end function;
