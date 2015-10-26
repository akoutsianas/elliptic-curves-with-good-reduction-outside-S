__author__ = 'akoutsianas'

l1,l2,l3 = PolynomialRing(QQ,'l1,l2,l3').gens()
E = HyperellipticCurve(t*(t-1)*(t-l1)*(t-l2)*(t-l3))
ik1,ik2,ik3 = E.absolute_igusa_invariants_kohel()
iw1,iw2,iw3 = E.absolute_igusa_invariants_wamelen()
