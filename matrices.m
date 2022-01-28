
allRootsList := function(order,F)
  // Returns all elements of F of order order and the field where they are defined
  list:=[];
  q:=#F;
  for elt in F do
    if not IsZero(elt) then
      oElt := Order(elt);
      if oElt eq order then
        if not elt^(-1) in list then
          Append(~list,elt);
        end if;
      end if;
    end if;
  end for;
  if #list eq 0 then
    F:=GF(q^2);
    q:=q^2;
    for elt in F do
      if not IsZero(elt) then
        oElt := Order(elt);
        if oElt eq order then
          if not elt^(-1) in list then
            Append(~list,elt);
          end if;
        end if;
      end if;
    end for;
  end if;
  return list, q;
end function;


orderPXL := function(M,q, bound)
// Returns the order of the matrix when thought in PXL
  matrix:=M;
  // if matrix[1][1] eq matrix[2][2] and matrix[1][2] eq matrix[2][1] and matrix[1][2] eq 0 then
  //   return -1;
  // end if;
  for ord in [1..bound] do
    matrix:=matrix*M;
    if matrix[1][1] eq matrix[2][2] and matrix[1][2] eq matrix[2][1] and matrix[1][2] eq 0 then
      return ord+1;
    end if;
  end for;
  return -1;
end function;

// returns a list of representatives of all possible conjugacy classes (possibly redundant).
// WARNING: When a is 2, it does not work always!!!!!
// We assume that we work in PSL_2(q').
possibilities := function(order,q,pm)
  if pm eq -1 then
    F := GF(q^2);
    q := q^2;
  else F:=GF(q);
  end if;
  R<x> := PolynomialRing(F);
  G := PGL(2,q);
  poly := R!CyclotomicPolynomial(2*order);
  // Split semisimple:
  // Here, we get two distinct eigenvalues and charpoly= x^2-(u+v)+1
  // Because det(M)=1, the only option is that M^order=+/- I in SL_2(q')
  if (q-1) mod order eq 0 then
    list := [];
    roots,size := allRootsList(order*2,F);
    for i in [1..#roots] do
      trace := roots[i]+roots[i]^(-1);
      M := Matrix([[0,-1],[1,trace]]);
      Append(~list, M);
    end for;
    return <list, #F>;

  // The nonsplit semisimple case
  // In this case the matrix is not diagonalizable and has different eigenvalues
  elif (q+1) mod order eq 0 or order eq 2 then
    factors := Factorization(poly);
    quadratic_factors := [];
    for factor in factors do
      if Degree(factor[1]) eq 2 then
        Append(~quadratic_factors, factor[1]);
      end if;
    end for;
    list := [];
    for factor in quadratic_factors do
      coeff := Coefficients(factor);
      M := Matrix([[0,-coeff[1]],[1,-coeff[2]]]);
      if orderPXL(M,q,order) eq order then
        Append(~list, M);
      end if;
    end for;
    return <list, #F>;

  // The unipotent case:
  // There is a repeated root u and the matrix is not diagonalizable.
  // The matrix has to be conjugate to [[1,1],[0,1]]
  elif q mod order eq 0 then
    return <[Matrix([[1,1],[0,1]])], q>;
  end if;
end function;

isSemisimple := function(a,q)
  if (q-1) mod a eq 0  or (q+1) mod a eq 0 then
    return true;
  end if;
  return false;
end function;

matricesTriple := function(triple,q,pm)
  semisimple := false;
  i := 1;
  orderTriple := [1,2,3];
  while not semisimple and i le 3 do
    if isSemisimple(triple[i],q) then
      Insert(~triple,1,triple[i]);
      Remove(~triple, i+1);
      Insert(~orderTriple,1,i);
      Remove(~orderTriple, i+1);
      semisimple := true;
    end if;
    i := i+1;
  end while;

  if semisimple then
    La := possibilities(triple[1],q,pm);
    List_a := La[1];
    size_a := La[2];
    A := List_a[1];
    Lb := possibilities(triple[2],q,pm);
    List_b := Lb[1];
    size_b := Lb[2];
    G := SL(2,GF(Max(size_b,size_a)));
    identity := G!Matrix([[1,0],[0,1]]);
    for B in List_b do
      for P in G do
        BP := P*(G!B)*P^(-1);
        matrices := [G!A,BP,identity];
        ord := orderTriple;
        ParallelSort(~ord,~matrices);
        C := identity;
        i := 1;
        while i le 3 and matrices[i] ne identity do
          C := matrices[i]^(-1)*C;
          i := i+1;
        end while;
        i := i+1;
        while i le 3 do
          C := C*matrices[i]^(-1);
          i := i+1;
        end while;
        if orderPXL(C,q,triple[3]) eq triple[3] then
          matrices := [G!A,BP,C];
          ord := orderTriple;
          ParallelSort(~ord,~matrices);
          return matrices;
        end if;
      end for;
    end for;
  else
    List_a,size_a := possibilities(triple[1],q,pm);
    A := List_a[1];
    List_b,size_b := possibilities(triple[2],q,pm);
    B := List_b[1];
    G :=SL(2,GF(Max(size_b,size_a)));
    for P in G do
      BP := P*(G!B)*P^(-1);
      C := ((G!A)*BP)^(-1);
      if orderPXL(C,q,triple[3]) eq triple[3] then
        matrices := [G!A,BP,C];
        return matrices;
      end if;
    end for;
  end if;
  error "No matrices";
end function;


boundFieldDefinition := function(triple,q,pm)
  count_possibilities := 0;
  semisimple:=false;
  i:=1;
  orderTriple:=[1,2,3];
  while not semisimple and i le 3 do
    if isSemisimple(triple[i],q) then
      Insert(~triple,1,triple[i]);
      Remove(~triple, i+1);
      Insert(~orderTriple,1,i);
      Remove(~orderTriple, i+1);
      semisimple:=true;
    end if;
    i := i+1;
  end while;

  if semisimple then
    La := possibilities(triple[1],q,pm);
    List_a := La[1];
    size_a := La[2];
    A := List_a[1];
    Lb := possibilities(triple[1],q,pm);
    List_b := La[1];
    size_b := La[2];
    G:=GL(2,GF(Max(size_b,size_a)));
    identity := G!Matrix([[1,0],[0,1]]);
    for B in List_b do
      for P in G do
        BP := P*(G!B)*P^(-1);
        matrices := [G!A,BP,identity];
        ord := orderTriple;
        ParallelSort(~ord,~matrices);
        C := identity;
        i := 1;
        while i le 3 and matrices[i] ne identity do
          C:=matrices[i]^(-1)*C;
          i:=i+1;
        end while;
        i:=i+1;
        while i le 3 do
          C:=C*matrices[i]^(-1);
          i:=i+1;
        end while;
        if orderPXL(C,q,triple[3]) eq triple[3] then
          matrices:= [G!A,BP,C];
          ord:=orderTriple;
          ParallelSort(~ord,~matrices);
          count_possibilities := count_possibilities+1;
        end if;
      end for;
    end for;
  else
    List_a,size_a:=possibilities(triple[1],q,pm);
    A := List_a[1];
    List_b,size_b:=possibilities(triple[2],q,pm);
    B:= List_b[1];
    G:=SL(2,GF(Max(size_b,size_a)));
    for P in G do
      BP := P*(G!B)*P^(-1);
      C:=((G!A)*BP)^(-1);
      if orderPXL(C,q,triple[3]) eq triple[3] then
        matrices:= [G!A,BP,C];
        count_possibilities := count_possibilities +1;
      end if;
    end for;
  end if;
  return count_possibilities;
end function;
