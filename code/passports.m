load "listsPrimeLowGenus.m";

output := "PassportsOutput.txt";

genusPassport := function(t,genus)
  a,b,c,p,q,l := Explode(t);
  if l eq 1 then
    G := PSL(2,q);
  else
    G := PGL(2,q);
  end if;
  pass := PassportRepresentatives(G : abc := [a,b,c]);
  if #pass ne 1 then
    print "error",t;
  end if;
  partition := pass[1][1];
  ramification := 0;
  for i in partition do
    for j in i do
      ramification := ramification + (j[1]-1)*(j[2]);
    end for;
  end for;
  if genus ne ((1/2)*(-2*(q+1)+ramification+2)) then
    print "error",t;
  end if;
  Write(output, Sprint(pass[1][2], "Magma"));
  Write(output, ";");
  Write(output, "\n");
  return true;
end function;

Write(output, "******************************************");
Write(output, "Genus 0");
Write(output, "******************************************");
Write(output, "\n");
for t in genus0X0 do
  Write(output, Sprint(t));
  Write(output, ";");
  Write(output, "\n");
  genusPassport(t,0);
  Write(output, "\n");
end for;
Write(output, "******************************************");
Write(output, "Genus 1");
Write(output, "******************************************");
Write(output, "\n");
for t in genus1X0 do
  Write(output, Sprint(t));
  Write(output, ";");
  Write(output, "\n");
  genusPassport(t,1);
  Write(output, "\n");
end for;
