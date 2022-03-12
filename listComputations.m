load "lowGenus.m";
load "x1.m";

// X_0(a,b,c;NN)
genus0 := listBoundedGenus(0);
genus1 := listBoundedGenus(1);
genus2 := listBoundedGenus(2);

print "Computed all the prime level low genus";

ggenus0:=[Append(t,0):t in genus0];
ggenus1:=[Append(t,1):t in genus1];
ggenus2:=[Append(t,2):t in genus2];
compositeGenus0diff := listCompositeGenusDifferentPrimes(ggenus0,0);
compositeGenus1diff := listCompositeGenusDifferentPrimes(ggenus1 cat ggenus0,1);
compositeGenus2diff := listCompositeGenusDifferentPrimes(ggenus2 cat ggenus1 cat ggenus0,2);

compositeGenus0sameRat := listCompositeGenusSameRationalPrimes(ggenus0,0);
compositeGenus1sameRat := listCompositeGenusSameRationalPrimes(ggenus1 cat ggenus0,1);
compositeGenus2sameRat := listCompositeGenusSameRationalPrimes(ggenus2 cat ggenus1 cat ggenus0,2);

compositeGenus0same := listCompositeGenusSamePrimes(ggenus0,0);
compositeGenus1same := listCompositeGenusSamePrimes(ggenus1 cat ggenus0,1);
compositeGenus2same := listCompositeGenusSamePrimes(ggenus2 cat ggenus1 cat ggenus0,2);

print "Computed all the composite level low genus";

nonCocompactGenus0 := listNonCocompact(genus0,0);
nonCocompactGenus1 := listNonCocompact(genus1,1);
nonCocompactGenus2 := listNonCocompact(genus2,2);

print "Computed all the non-cocompact low genus";

// X_1(a,b,c;NN)
genus0X1 := listFixedGenusX1(ggenus0,0);
genus1X1 := listFixedGenusX1(ggenus1 cat ggenus0,1);
genus2X1 := listFixedGenusX1(ggenus2 cat ggenus1 cat ggenus0,2);

compositeDiff0X1 := listCompositeGenusX1(genus0X1,0);
compositeSameRat0X1 := listCompositeGenusSameRationalPrimesX1(genus0X1,0);
compositeSame0X1 := listCompositeGenusSamePrimesX1(genus0X1,0);

compositeDiff1X1 := listCompositeGenusX1(genus0X1 cat genus1X1,1);
compositeSameRat1X1 := listCompositeGenusSameRationalPrimesX1(genus0X1 cat genus1X1,1);
compositeSame1X1 := listCompositeGenusSamePrimesX1(genus0X1 cat genus1X1,1);

compositeDiff2X1 := listCompositeGenusX1(genus0X1 cat genus1X1 cat genus2X1,2);
compositeSameRat2X1 := listCompositeGenusSameRationalPrimesX1(genus0X1 cat genus1X1 cat genus2X1,2);
compositeSame2X1 := listCompositeGenusSamePrimesX1(genus0X1 cat genus1X1 cat genus2X1,2);

nonCocompactGenus0X1 := listNonCocompactX1(genus0,0);
nonCocompactGenus1X1 := listNonCocompactX1(genus1,1);
nonCocompactGenus2X1 := listNonCocompactX1(genus2,2);

print "For X_0(a,b,c;NN) there is a total of";
print (#genus0 + #compositeGenus0diff +#compositeGenus0sameRat + #compositeGenus0same + #nonCocompactGenus0), "curves of genus 0";
print (#genus1 + #compositeGenus1diff +#compositeGenus1sameRat + #compositeGenus1same + #nonCocompactGenus1), "curves of genus 1";
print (#genus2 + #compositeGenus2diff +#compositeGenus2sameRat + #compositeGenus2same + #nonCocompactGenus2), "curves of genus 2";


print "For X_1(a,b,c;NN) there is a total of";
print (#genus0X1 + #compositeDiff0X1 +#compositeSameRat0X1 + #compositeSame0X1 + #nonCocompactGenus0), "curves of genus 0";
print (#genus1X1 + #compositeDiff1X1 +#compositeSameRat1X1 + #compositeSame1X1 + #nonCocompactGenus1), "curves of genus 1";
print (#genus2X1 + #compositeDiff2X1 +#compositeSameRat2X1 + #compositeSame2X1 + #nonCocompactGenus2), "curves of genus 2";
