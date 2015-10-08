K = NumberField(x-1,'a')
t = polygen(K,'t')
# M = K.extension(t**2-69,'b')
# c2 = M.gen()
# t = polygen(M,'y')
# L = M.extension(t**3 - 12*t - 7,'c')
# Labs = K.extension(x**6 - 6*x**5 + 168*x**4 + 4664*x**3 - 6519*x**2 - 859554*x + 8039358,'d')
L = K.extension(t**3 - 129*t - 344,'b')
# SK = sum([K.primes_above(p) for p in [2,3,23]],[])
SK = sum([K.primes_above(p) for p in [2,5,43]],[])
SL = sum([L.primes_above(p) for p in SK],[])
SunitL = L.S_unit_group(S=SL)
Gl,Gm = Norm_subgroup_division_field(SK,SL)
Glunit = [g for g in Gl if g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
# B = 1161
B = 428
# jinv = QQ(620663201409024)/QQ(3404825447)
jinv = Integer(1849)

#this is for
# B = 5946
# L = K.extension(t**2 - 97,'b')
# SK = sum([K.primes_above(p) for p in [2,3,97]],[])
# jinv = Integer(-32768)

Sl = support_of_G(Gl,10)[0]
Sm = support_of_G(Gm,10)[0]
p = ZZ(59)
P = Primes()
C = CremonaDatabase()
#while p <= 100:
N = [2**i * 3**j for i,j in cartesian_product_iterator([xrange(9),xrange(6)])]
# N = [2**e for e in range()]
ED = C.list(N)
EC21 = [e for e in ED if not e.two_division_polynomial().is_irreducible()]
EC2 = [E for E in EC21 if len(E.two_division_polynomial().factor()) == 2]

JC2 = []
for E in EC2:
    if E.j_invariant() not in JC2:
        JC2.append(E.j_invariant())

JC21 = []
for E in EC21:
    if E.j_invariant() not in JC21:
        JC21.append(E.j_invariant())
# print 'p=%s,J=%s'%(p,JC21)
# p = P.next(p)

JL = []
for E in EC2:
    M = E.two_division_polynomial().splitting_field('a')
    if len(M.embeddings(L)) > 0:
        # print M.absolute_discriminant().factor()
        if E.j_invariant() not in JL:
            JL.append(E.j_invariant())
EC3S3 = [e for e in ED if e.two_division_polynomial().is_irreducible()]
EC3 = [E for E in EC3S3 if E.two_division_polynomial().discriminant().is_square()]
JC3 = []
for E in EC3:
    if E.j_invariant() not in JC3:
        JC3.append(E.j_invariant())

ES3 = [E for E in EC3S3 if not E.two_division_polynomial().discriminant().is_square()]
JS3 = []
for E in ES3:
    if E.j_invariant() not in JS3:
        JS3.append(E.j_invariant())
# cubics = cubic_extensions(K,SK)
from sage.schemes.elliptic_curves.ell_egros import (egros_from_jlist, egros_get_j)