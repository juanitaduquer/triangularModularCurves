SetDebugOnError(true);
OrderDeltasNN := function(Delta,NN)

end function;

CheckHyperbolic := function(a,b,c,p)
  checked := [];
  for es in [es : es in CartesianPower([1,p],3)|es ne <1,1,1>] do
    print es;
    ae,be,ce := Explode([a*es[1],b*es[2],c*es[3]]);
    if not Set([ae,be,ce]) in checked and IsHyperbolicTriple(ae,be,ce) then
      Append(~checked, Set([ae,be,ce]));
      Delta := TriangleGroup(ae,be,ce);
      E := BaseField(QuaternionAlgebra(Delta));
      ZZE := Integers(E);
      pps := Factorization(p*ZZE);
      for pp in [pp[1] : pp in pps ] do
        NN := pp^2;
        proj, sigmas, g,_ := ProjectiveRamificationType(Delta,NN);
        if proj and [Order(sigma):sigma in sigmas] ne [ae,be,ce] then
          return false;
        end if;
        // if [a,b,c] eq OrderDeltasNN(Delta,NN) then
        //   return false;
        // end if;
      end for;
    end if;
  end for;
  return true;
end function;

CheckHyperbolic(3,3,3,3);

// aaaaaaaaaaaaaa
// No proj triples outside of prime level
CheckHyperbolic(2,3,3,3);

CheckHyperbolic(2,3,4,3);

CheckHyperbolic(2,3,5,2);

CheckHyperbolic(2,3,5,5);
