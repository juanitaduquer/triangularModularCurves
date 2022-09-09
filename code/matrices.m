
allRootsList := function(order,F)
  // Returns all elements of F of order order and the field where they are defined
  list := [];
  for elt in F do
    if not IsZero(elt) then
      if Order(elt) eq order then
        Append(~list,elt);
      end if;
    end if;
  end for;
  return list;
end function;

orderPXL := function(M,bound)
// Returns the order of the matrix when thought in PXL
  matrix := M;
  for ord in [1..bound] do
    if matrix[1][1] eq matrix[2][2] and matrix[1][2] eq matrix[2][1] and matrix[1][2] eq 0 then
      return ord;
    end if;
    matrix *:= M;
  end for;
  return -1;
end function;

possibilities := function(order,q,pm)
  // returns a list of representatives of all possible conjugacy classes of order order.
  list := [];
  F := GF(q);
  if pm eq 1 then
    if q mod order eq 0 then
      p := Factorization(q)[1][1];
      // We get two classes, [[1,1],[0,1]], and [[1,x],[0,1]], where x is a non square
      for x in F do
        if x ne F!0 and not IsSquare(x) then
          return [Matrix([[F!1,F!x],[F!0,F!1]]),Matrix([[F!1,F!1],[F!0,F!1]])];
        end if;
      end for;
    end if;
    if (q+1) mod order eq 0 then
      R<x> := PolynomialRing(F);
      poly1 := R!(CyclotomicPolynomial(order));
      poly2 := R!(x^order+1);
      factorsCoeff := Factorization(poly1) cat Factorization(poly2);
      factors := SequenceToSet([f[1] : f in factorsCoeff | Degree(f[1]) eq 2]);
      for factor in factors do
        M := Matrix([[0,-F!Coefficient(factor,0)],[1,-F!Coefficient(factor,1)]]);
        if orderPXL(M,q,order+1) eq order then
          c1:=Coefficient(factor,0);
          c2:=Coefficient(factor,1);
          conjugateInList := false;
          for T in list do
            if IsSquare(c1/Determinant(T)) then
              _,x := IsSquare(c1/Determinant(T));
              if -c2 eq x*Trace(T) or -c2 eq -x*Trace(T) then
                conjugateInList := true;
              end if;
            end if;
          end for;
          if not conjugateInList then
            Append(~list, M);
          end if;
        end if;
      end for;
    end if;
    if (q-1) mod order eq 0 then
      constants := allRootsList(2*order,F);
      for c in constants do
        M := Matrix([[c,F!0],[F!0,c^(-1)]]);
        if orderPXL(M,q,order+1) eq order and not Matrix([[c^(-1),F!0],[F!0,c]]) in list and not Matrix([[-c^(-1),F!0],[F!0,-c]]) in list and not Matrix([[-c,F!0],[F!0,-c^(-1)]]) in list then
          Append(~list, M);
        end if;
      end for;
    end if;
    return list;
  else
    if q mod order eq 0 then
      return [Matrix([[F!1,F!1],[F!0,F!1]])];
    end if;
    if (q+1) mod order eq 0 then
      for c1 in F do
        if not IsZero(c1) then
          for c2 in F do
            M := Matrix([[0,c1],[1,c2]]);
            if orderPXL(M,q,order+1) eq order then
              conjugateInList := false;
              for T in list do
                if IsSquare(-c1/Determinant(T)) then
                  _,x := IsSquare(-c1/Determinant(T));
                  if c2 eq x*Trace(T) or c2 eq -x*Trace(T) then
                    conjugateInList := true;
                  end if;
                end if;
              end for;
              if not conjugateInList then
                Append(~list, M);
              end if;
            end if;
          end for;
        end if;
      end for;
    end if;
    if (q-1) mod order eq 0 then
      constants := allRootsList(order,F);
      for c in constants do
        M := Matrix([[F!1,F!0],[F!0,F!c]]);
        conjugateInList := false;
        for T in list do
          if IsSquare(c/Determinant(T)) then
            _,x := IsSquare(c/Determinant(T));
            if c+1 eq x*Trace(T) or c+1 eq -x*Trace(T) then
              conjugateInList := true;
            end if;
          end if;
        end for;
        if not conjugateInList then
          Append(~list, M);
        end if;
      end for;
    end if;
    return list;
  end if;
end function;

matricesTriple := function(triple,q,pm)
  if pm eq 1 then
    G := SL(2,q);
  else
    G := GL(2,q);
  end if;
  found := false;
  listA := possibilities(triple[1],q,pm);
  listB := possibilities(triple[2],q,pm);
  i := 1;
  while not found and i le #listA do;
    A := listA[i];
    for B in listB do
      for P in G do
        BP := P*(G!B)*P^(-1);
        C := BP^(-1)*A^(-1);
        if orderPXL(C,q,triple[3]+1) eq triple[3] then
          return [A,BP,C];
        end if;
      end for;
    end for;
    i := i+1;
  end while;
  error "No matrices";
end function;

allMatricesTriple := function(triple,q,pm)
  list := [];
  if pm eq 1 then
    G := SL(2,q);
  else
    G := GL(2,q);
  end if;
  listA := possibilities(triple[1],q,pm);
  for A in listA do
    listB := possibilities(triple[2],q,pm);
    for B in listB do
      for P in G do
        BP := P*(G!B)*P^(-1);
        C := BP^(-1)*A^(-1);
        if orderPXL(C,q,triple[3]+1) eq triple[3] then
          if &and[orderPXL(tri[2]*BP^(-1),q,2) ne 1 : tri in list | tri[1] eq A] then
            Append(~list, [A,BP,C]);
          end if;
        end if;
      end for;
    end for;
  end for;
  return list;
  error "No matrices";
end function;
