fixed_points := function(x,a,b,c,p,q,pm)
  if not x eq 2 and 2*a*b*c mod p ne 0 then
    if (q+1) mod x eq 0 then
      return 0;
    elif (q-1) mod x eq 0 then
      return 2;
    elif q mod x eq 0 then
      return 1;
    end if;
  elif pm eq 1 then
    if q mod 4 eq 1 then
      return 2;
    else
      return 0;
    end if;
  end if;
  if pm eq -1 then
    P:=PassportRepresentatives(PGL(2,q):abc:=[a,b,c]);
  else
    P:=PassportRepresentatives(PSL(2,q):abc:=[a,b,c]);
  end if;
  if #P[1][1][1] ge 2 then
    return 2;
  end if;
  return 0;
end function;


genus_two_primes_2 := function(t1,t2)
  a,b,c,p1,q1,pm1 := Explode([t1[1],t1[2],t1[3],t1[4],t1[5],t1[6]]);
  p2,q2,pm2 := Explode([t2[4],t2[5],t2[6]]);
  assert a eq t2[1] and b eq t2[2] and c eq t2[3];
  fix_a := fixed_points(b,a,b,c,p1,q1,pm1)*fixed_points(b,a,b,c,p2,q2,pm2);
  fix_b := fixed_points(b,a,b,c,p1,q1,pm1)*fixed_points(b,a,b,c,p2,q2,pm2);
  fix_c := fixed_points(c,a,b,c,p1,q1,pm1)*fixed_points(c,a,b,c,p2,q2,pm2);
  ram_a := (a-1)*((q1+1)*(q2+1)-fix_a)/a;
  ram_b := (b-1)*((q1+1)*(q2+1)-fix_b)/b;
  ram_c := (c-1)*((q1+1)*(q2+1)-fix_c)/c;
  return (1/2)*(-2*(q1+1)*(q2+1)+ram_a+ram_b+ram_c +2);
end function;

ram :=function(x,q)
  if (q-2) mod x eq 0 then
    return (x-1)*(q-2)/x;
  elif (q-1) mod x eq 0 then
    return (x-1)*(q-1)/x;
  elif q mod x eq 0 then
    return (q-1)*q/x;
  end if;
end function;

genus_prime_square := function(a,b,c,p,pm)
  q := p^4+p^3;
  return (1/2)*(-2*(q+1)+ram(a,q)+ram(b,q)+ram(c,q)+2);
end function;




// For 2 primes
new_genus_0 := [];
new_genus_1 := [];
new_genus_2 := [];
problem := [];
for i in [1..#l] do
  t1:=l[i];
  for j in [i..#l] do
    t2:=l[j];
    if not t1 eq t2 then
      if ((t1[1] eq t2[1]) and  (t1[2]eq t2[2]) and (t1[3] eq t2[3]) ) then
        print t1,t2;
        g:=genus_two_primes_2(t1,t2);
        if not Floor(g) eq g then
          Append(~problem,[t1[1],t1[2],t1[3],t1[4],t1[5],t2[4],t2[5]]);
        end if;
        print t1[1],t1[2],t1[3],g ;
        if g eq 0 then
          Append(~new_genus_0,[t1[1],t1[2],t1[3],t1[4],t1[5],t2[4],t2[5]]);
        elif g eq 1 then
          Append(~new_genus_1,[t1[1],t1[2],t1[3],t1[4],t1[5],t2[4],t2[5]]);
        elif g eq 2 then
          Append(~new_genus_2,[t1[1],t1[2],t1[3],t1[4],t1[5],t2[4],t2[5]]);
        end if;
      end if;
    end if;
  end for;
end for;


// For 3 primes

genus_3_primes := function(a,b,c,p1,p2,p3,q1,q2,q3,pm1,pm2,pm3,fx1,fx2,fx3)
  fix_a := fx1*fx2*fx3;
  fix_b := fixed_points(b,a,b,c,p1,q1,pm1)*fixed_points(b,a,b,c,p2,q2,pm2)*fixed_points(b,a,b,c,p3,q3,pm3);
  fix_c := fixed_points(c,a,b,c,p1,q1,pm1)*fixed_points(c,a,b,c,p2,q2,pm2)*fixed_points(c,a,b,c,p3,q3,pm3);
  ram_a := (a-1)*((q1+1)*(q2+1)*(q3+1)-fix_a)/a;
  ram_b := (b-1)*((q1+1)*(q2+1)*(q3+1)-fix_b)/b;
  ram_c := (c-1)*((q1+1)*(q2+1)*(q3+1)-fix_c)/c;
  return (1/2)*(-2*(q1+1)*(q2+1)*(q3+1)+ram_a+ram_b+ram_c +2);
end function;


new_genus_0 := [];
new_genus_1 := [];
new_genus_2 := [];
problem := [];
for i in [1..#l] do
  t1:=l[i];
  for j in [i..#l] do
    t2:=l[j];
    for k in [j..#l] do
      t3:=l[k];
      if (not t1 eq t2) and (not t1 eq t3) and (not t3 eq t2) then
        if ((t1[1] eq t2[1]) and  (t1[2]eq t2[2]) and (t1[3] eq t2[3]) and (t3[1] eq t2[1]) and  (t3[2]eq t2[2]) and (t3[3] eq t2[3])) then
          print t1,t2, t3;
          g:=genus_3_primes(t1[1],t1[2],t1[3],t1[4],t2[4],t3[4],t1[5],t2[5],t3[5],t1[6],t2[6],t3[6],t1[7],t2[7],t3[7]);
          if (not Floor(g) eq g) or (g le -1) then
            Append(~problem,[t1[1],t1[2],t1[3],t1[4],t2[4],t3[4]]);
          end if;
          print t1[1],t1[2],t1[3],g ;
          if g eq 0 then
            Append(~new_genus_0,[t1[1],t1[2],t1[3],t1[4],t2[4],t3[4]]);
          elif g eq 1 then
            Append(~new_genus_1,[t1[1],t1[2],t1[3],t1[4],t2[4],t3[4]]);
          elif g eq 2 then
            Append(~new_genus_2,[t1[1],t1[2],t1[3],t1[4],t2[4],t3[4]]);
          end if;
        end if;
      end if;
    end for;
  end for;
end for;
