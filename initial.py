#I want to use pari in order to speed up sieve
#S = {2,3,5} i=1

K = NumberField(x-1,'b')
y = polygen(K)
M = K.extension(y**2-5,'c2')
t = polygen(M,'t')
L = M.extension(t**3 - 12*t - 14,'c3')
# c2 = M.gen()
# c3 = L.gen()
# Gl = [L(-1), (-1/10*c2 - 1/2)*c3**2 + (3/10*c2 + 1/2)*c3 + 13/10*c2 + 9/2, -1/5*c2*c3**2 + (1/10*c2 - 3/2)*c3 + 3/5*c2 - 2,
#       -2/5*c2*c3 - 7/10*c2 - 1/2]
# Gm = [L(-1), (1/10*c2 + 1/2)*c3**2 + (-3/10*c2 - 1/2)*c3 - 13/10*c2 - 7/2, (1/2*c2 - 1/2)*c3**2 + (-c2 + 2)*c3 - 3*c2 + 2,
#       -4/5*c3**2 + (-1/5*c2 + 7/5)*c3 + 7/10*c2 + 59/10]
bounds = [2, 122, 71, 44]
bounds_Sl = [39,39]