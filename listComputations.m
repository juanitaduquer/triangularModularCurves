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
nonCocompactGenus1 := listNonCocompact(genus1 cat genus0,1);
// nonCocompactgenus2 := listNonCocompact(genus2 cat genus1 cat genus0,2);

print "Computed all the non-cocompact low genus";

// X_1(a,b,c;NN)
genus0X1 := listFixedGenusX1(ggenus0,0);
genus1X1 := listFixedGenusX1(ggenus1 cat ggenus0,1);
genus2X1 := listFixedGenusX1(ggenus2 cat ggenus1 cat ggenus0,2);

print "Computed all the X1 low genus";
