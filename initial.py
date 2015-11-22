### Over Q

# K = NumberField(x-1,'a')
# y = polygen(K,'t')
# M = K.extension(y**2 + 3,'b')
# c2 = M.gen()
# t = polygen(M,'y')
# L = M.extension(t**3 + c2,'c')
# SK = sum([K.primes_above(p) for p in [2,3]],[])
# SL = sum([L.primes_above(p) for p in SK],[])
# SunitL = L.S_unit_group(S=SL)
# Gl,Gm = Norm_subgroup_division_field(SK,SL)
# B = 1083


### Over quadratic

M = NumberField(x**2-x-1,'a')
t = polygen(M,'t')
a = M.gen()
# L = M.extension(t**2-2*a,'c')
# L = M.extension(t**3 - 186*t + 124*a - 62,'c')
# B = 126
L = M.extension(t**3 - 93*t + 124,'c')
B = 1624
SM = sum([M.primes_above(p) for p in [62]],[])
SL = sum([L.primes_above(p) for p in SM],[])
SunitL = L.S_unit_group(S=SL)
Gl,Gm = Norm_subgroup_division_field(SM,SL)