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
  return (1/2)*(-2*(q+1)+ramification_triple(a,b,c,p,q,pm)+2);
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
            if c le cbound and is_hyperbolic(a,b,c) and is_projective(a,b,c)  and (2*a*b*c) mod p ne 0 then
              print a,b,c;
              g:=genus_triangular_modular_curve(a,b,c,p,boundq);
              if g le boundG then
                Append(~list,[a,b,c,p,q]);
              end if;
            end if;
          end for;
        end for;
      end for;
    end if;
  end for;
  return list;
end function;

// L:=[
//   [2, 3, 7, 3, 27, 1], [2, 3, 7, 41, 41, 1], [2, 3, 7, 71, 71, 1], [2, 3, 7, 97, 97, 1], [2, 3, 7, 113, 113, 1],
//   [2, 3, 7, 127, 127, 1], [2, 3, 8, 23, 23, -1], [2, 3, 8, 31, 31, 1], [2, 3, 8, 41, 41, -1], [2, 3, 8, 73, 73, -1],
//   [2, 3, 8, 97, 97, 1], [2, 3, 9, 2, 8, 1], [2, 3, 9, 17, 17, 1], [2, 3, 9, 73, 73, 1], [2, 3, 10, 3, 9, -1],
//   [2, 3, 10, 19, 19, 1], [2, 3, 10, 41, 41, 1], [2, 3, 10, 61, 61, 1], [2, 3, 11, 11, 11, 1], [2, 3, 11, 23, 23, 1],
//   [2, 3, 12, 11, 11, -1], [2, 3, 12, 37, 37, -1], [2, 3, 12, 7, 49, 1], [2, 3, 13, 5, 25, 1], [2, 3, 13, 3, 27, 1],
//   [2, 3, 14, 13, 13, -1], [2, 3, 14, 29, 29, 1], [2, 3, 14, 43, 43, -1], [2, 3, 15, 31, 31, 1], [2, 3, 16, 17, 17, -1],
//   [2, 3, 17, 2, 16, 1], [2, 3, 17, 17, 17, 1], [2, 3, 18, 37, 37, 1], [2, 3, 19, 19, 19, 1], [2, 3, 20, 19, 19, -1],
//   [2, 3, 22, 23, 23, -1], [2, 3, 24, 5, 25, -1], [2, 3, 26, 3, 27, -1], [2, 3, 30, 31, 31, -1], [2, 4, 5, 19, 19, -1],
//   [2, 4, 5, 29, 29, -1], [2, 4, 5, 31, 31, 1], [2, 4, 5, 7, 49, 1], [2, 4, 5, 61, 61, -1], [2, 4, 6, 11, 11, -1],
//   [2, 4, 6, 17, 17, -1], [2, 4, 6, 19, 19, -1], [2, 4, 6, 29, 29, -1], [2, 4, 6, 31, 31, -1], [2, 4, 6, 37, 37, -1],
//   [2, 4, 7, 7, 7, 1], [2, 4, 7, 13, 13, -1], [2, 4, 7, 29, 29, -1], [2, 4, 8, 7, 7, -1], [2, 4, 8, 5, 25, -1],
//   [2, 4, 9, 17, 17, 1], [2, 4, 9, 19, 19, -1], [2, 4, 10, 3, 9, -1], [2, 4, 10, 11, 11, -1], [2, 4, 11, 11, 11, -1],
//   [2, 4, 12, 5, 25, 1], [2, 4, 13, 13, 13, -1], [2, 4, 14, 13, 13, -1], [2, 4, 16, 17, 17, -1], [2, 4, 17, 17, 17, 1],
//   [2, 5, 5, 2, 4, 1], [2, 5, 5, 3, 9, 1], [2, 5, 5, 31, 31, 1], [2, 5, 5, 41, 41, 1], [2, 5, 6, 5, 5, -1],
//   [2, 5, 6, 11, 11, 1], [2, 5, 6, 19, 19, -1], [2, 5, 6, 31, 31, -1], [2, 5, 8, 3, 9, -1], [2, 5, 11, 11, 11, 1],
//   [2, 5, 12, 11, 11, -1], [2, 5, 15, 2, 16, 1], [2, 6, 6, 5, 5, -1], [2, 6, 6, 19, 19, -1], [2, 6, 7, 13, 13, 1],
//   [2, 6, 8, 7, 7, -1], [2, 6, 9, 19, 19, -1], [2, 6, 10, 11, 11, -1], [2, 6, 12, 13, 13, -1], [2, 6, 13, 13, 13, 1],
//   [2, 7, 7, 7, 7, 1], [2, 7, 8, 7, 7, -1], [2, 7, 9, 2, 8, 1], [2, 8, 8, 17, 17, 1], [2, 8, 10, 3, 9, -1],
//   [2, 10, 10, 11, 11, -1], [2, 10, 11, 11, 11, -1], [2, 12, 12, 13, 13, -1], [3, 3, 4, 17, 17, 1], [3, 3, 4, 31, 31, 1],
//   [3, 3, 5, 5, 5, 1], [3, 3, 5, 3, 9, 1], [3, 3, 5, 11, 11, 1], [3, 3, 5, 19, 19, 1], [3, 3, 5, 31, 31, 1],
//   [3, 3, 6, 5, 25, 1], [3, 3, 7, 2, 8, 1], [3, 3, 7, 13, 13, 1], [3, 3, 9, 19, 19, 1], [3, 3, 13, 13, 13, 1],
//   [3, 3, 15, 2, 16, 1], [3, 4, 4, 3, 3, -1], [3, 4, 4, 7, 7, 1], [3, 4, 4, 17, 17, 1], [3, 4, 5, 3, 9, 1],
//   [3, 4, 6, 5, 5, -1], [3, 4, 7, 7, 7, 1], [3, 4, 12, 13, 13, -1], [3, 5, 5, 2, 4, 1], [3, 5, 5, 5, 5, 1],
//   [3, 5, 5, 11, 11, 1], [3, 6, 6, 13, 13, 1], [3, 6, 8, 7, 7, -1], [3, 7, 7, 7, 7, 1], [3, 7, 7, 2, 8, 1],
//   [3, 8, 8, 3, 9, -1], [4, 4, 4, 17, 17, 1], [4, 4, 5, 3, 9, 1], [4, 4, 6, 13, 13, -1], [4, 5, 6, 5, 5, -1],
//   [4, 6, 6, 7, 7, -1], [4, 8, 8, 3, 9, -1], [5, 5, 5, 5, 5, 1], [5, 5, 5, 11, 11, 1], [6, 6, 7, 7, 7, -1],
//   [7, 7, 7, 2, 8, 1]
// ];
//
// for t in L do
//   a:=t[1];
//   b:=t[2];
//   c:=t[3];
//   p:=t[4];
//   print a,b,c,p;
//   group:=group_for_abc(a,b,c,p,10000000000);
//   print group;
// end for;
// for t in L do
//   print t;
//   list:=q_for_abc(t[1],t[2],t[3],t[4],10000000);
//   if [list[1],list[2]] ne [t[5],t[6]] then
//     if t[1]*t[2]*t[3] mod t[4] ne 0 then
//       print"Problem";
//       print t;
//     end if;
//   end if;
// end for;

// for t in L do
//   if genus_triangular_modular_curve(t[1],t[2],t[3],t[5]) ne 0 then
//     print t;
//   end if;
// end for;
