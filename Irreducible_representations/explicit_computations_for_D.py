#General

def signature_of_D(D):

    signature = []
    for d in D.divisors():
        if d.is_square():
            d1 = ZZ(sqrt(d))
            d2 = ZZ(D/d)
            # print 'd1,d2',d1,d2
            if gcd(d1,d2) == 1:
                # print 'd1.prime',d1.prime_divisors()
                if len([1 for p in d1.prime_divisors() if (p%2== 1 and legendre_symbol(d2,p) == -1) or (p == 2 and d2%8 != 1)]) == 0:
                    signature.append([d1,d2])
    return signature


#Quadratic case

#We make explicit the computations of Theorem 1 of Freitas and Siksek for K = Q(sqrt(2))

def irreducible_representations(D,curve = 1):

    K = NumberField(x**2 - D,'r2')
    r = K.class_number()
    t = polygen(QQ)
    g = t**(12*r)-1
    G = K.embeddings(K)
    tau = [f for f in G if f(K.gen()) != K.gen()][0]
    e1 = K.units()[0]
    A1 = (tau(e1)**12 - 1).absolute_norm()
    A2 = (e1**12-1).absolute_norm()
    B = lcm(A1,A2)
    # print 'B',B.factor()

    red_Primes = [p for p in ZZ(B).prime_divisors() if p>=11 and p != 13]


    temp_red_Primes = []
    q = 3
    while q < 50:
        if legendre_symbol(D,q) == -1:

            #Here we make the assumption that q\nmid p

            for Q in K.primes_above(q):
                red_Q_Primes = []
                if q >= 11 and q != 13:
                    red_Q_Primes.append(q)
                GFq = Q.residue_field()
                for a in range(q):
                    if curve == 1:
                        # EmodQ = EllipticCurve([0,GFq(2*a),0,GFq(2),0])
                        EmodQ = EllipticCurve([0,GFq(2*a),0,GFq(a**2-D),0])
                    else:
                        EmodQ = EllipticCurve([0,GFq(2*a),0,GFq(D),0])
                    aQE = Q.norm() + 1 - EmodQ.order()
                    f = t**2-aQE*t+Q.absolute_norm()
                    for p in ZZ(g.resultant(f)).prime_divisors():
                        # print 'g.resultant(f)',g.resultant(f).factor()
                        if p>=11 and p!=13 and p not in red_Q_Primes:
                            red_Q_Primes.append(p)
                temp_red_Primes.append(prod(red_Q_Primes))
        q = Primes().next(ZZ(q))
    for p in ZZ(gcd(temp_red_Primes)).prime_divisors():
        if p not in red_Primes:
            red_Primes.append(p)
    red_Primes.sort()
    return red_Primes


def Np(D):

    D1 = D/2**(D.valuation(2))
    if D%4 == 1:
        return [2**5 * D1**2,2**6 * D1**2]
    if D%4 == 3:
        return [2**8 * D1**2]
    if D%32 == 0:
        return [2**11 * D1**2]
    if D%8 == 0:
        return [2**5 * D1**2]
    if D%2 == 0:
        return [2**8 * D1**2]


def compute_Bfq(q,aqf):

    b = RR(2*sqrt(q.norm())).floor()
    normq = q.norm()
    A = []
    for a in range(-b,b+1):
        if (normq + 1 -a)%4 == 0:
            A.append(a)
    print 'A',A
    Bfq = normq * ((normq+1)**2 - aqf**2)*prod([a-aqf for a in A])
    return Bfq


def isogeny_classes(curves):

    represent = []

    for E in curves:
        if len([1 for rep in represent if E.is_isogenous(rep)]) == 0:
            represent.append(E.global_minimal_model())

    isogenies = [[E] for E in represent]

    for E in curves:
        i = [i for i,E0 in enumerate(represent) if E.is_isogenous(E0)][0]
        isogenies[i].append(E)

    return represent,isogenies


def compute_Aqf1f2(q,aqf1,aqf2):

    Nq = q.absolute_norm()
    q_rational = ZZ(Nq).prime_divisors()[0]
    GF = q.residue_field()

    Aqf1f2 = 1
    for a in range(q_rational):
        if q_rational != 2:
            if legendre_symbol(2,q_rational) == -1:
                aqE1 = EllipticCurve([0,2*GF(a),0,GF(a**2-2),0]).order()
                aqE2 = EllipticCurve([0,2*GF(a),0,GF(2),0]).order()
                Aqf1f2 *= gcd(aqE1-aqf1,aqE2 - aqf2)
            else:
                Aqf1f2 *= gcd((Nq+1)**2-aqf1,(Nq+1)**2 - aqf2)
                if Aqf1f2 == 0:
                    print q_rational
    return Aqf1f2*q_rational


def bound_p_over_K(F,primes_array,hecke1,hecke2):

    return gcd([compute_Aqf1f2(F.ideal(Q[1],Q[2]),aqf1,aqf2) for Q,aqf1,aqf2 in zip(primes_array,hecke1,hecke2)])

#Over Q

#Method I as it is explained in Bugead-Mignotte-Siksek


def bound_p_over_Q(d1,d2,B,tmod4):
    r"""

    INPUT:
        - ``d1,d2`` : the signature of the equation
        - ``B`` : a positive integer
        - ``tmod4`` : the value of ``t`` modulo 4. when ``t`` is even both 0 and 2 are valid.

    OUTPUT:
        For each newform of level `N = Lrad(D)` as in Proposition 6.2 of Bugead-Mignotte-Siksek paper
        returns the newform `f` and the gcd of `B_\ell(f)` for `\ell\leq B`.
    """

    if (d1*d2)%2 == 1:
        if d2%8 == 1 and tmod4 == 1:
            L = 2
        else:
            L = 2**5

    if d1%2 == 0:
        L = 1

    if d2.valuation(2) == 1:
        L = 2**6
    elif d2%16 == 12 and tmod4 == 1:
        L = 2
    elif d2%16 == 4 and tmod4 == 3:
        L = 2**3
    elif d2.valuation(2) == 3:
        L = 2**4
    elif d2.valuation(2) == 4 or d2.valuation(2) == 5:
        L = 2**2
    elif d2.valuation(2) == 6:
        L = 1/2
    elif d2.valuation(2) >= 7:
        L = 1

    # print 'L',L
    # N = L * radical(d1*d2)
    print 'N',L * radical(d1*d2)

    exceptional_cases = []
    for f in Newforms(L * radical(d1*d2),names = 'a'):
        Bf = bound_p_over_Q_for_f(f,d1,d2,B,tmod4)
        print 'Bf',Bf
        if Bf == 0:
            exceptional_cases.append([f,0])
        else:
            exceptional_cases.append([f,ZZ(Bf)])

    return exceptional_cases


def bound_p_over_Q_for_f(f,d1,d2,B,tmod4):
    r"""

    INPUT:
        - ``f`` : a classical newform
        - ``d1,d2`` : the signature of the equation
        - ``B`` : a positive integer
        - ``tmod4`` : the value of ``t`` modulo 4. when ``t`` is even both 0 and 2 are valid.

    OUTPUT:
        Return the gcd of `B_\ell(f)` as in Proposition 7.1 of Bugead-Mignotte-Siksek paper for all primes
        less than ``B``.
    """

    l = ZZ(3)
    Bf = []
    while l <= B:
        if (d1*d2)%l != 0:
            Bf.append(compute_Bl2f_over_Q(f,l,d1,d2,tmod4))
        l = Primes().next(l)
    return gcd(Bf)


def compute_Bl2f_over_Q(f,l,d1,d2,tmod4):
    r"""

    INPUT:
        - ``f`` : a classical newform
        - ``l`` : a rational prime
        - ``d1,d2`` : the signature of the equation
        - ``tmod4`` : the value of ``t`` modulo 4. when ``t`` is even both 0 and 2 are valid.

    OUTPUT:
        Return `B_\ell(f)` as in Proposition 7.1 of Bugead-Mignotte-Siksek paper.
    """
    GF = Integers(l)
    af = f[l]
    Bl2f = 1

    #Odd d1 and d2

    if (d1*d2)%2 == 1:
        if d2%4 == 3:
            for t in GF:
                if t**2 != d2:
                    aE = l+1 - EllipticCurve([0,2*t,0,GF(d2),0]).order()
                    Bl2f = lcm((aE - af).norm(),Bl2f)
        elif d2%8 == 5:
            for t in GF:
                if t**2 != d2:
                    aE = l+1 - EllipticCurve([0,2*t,0,t**2 - GF(d2),0]).order()
                    Bl2f = lcm((aE - af).norm(),Bl2f)
        elif d2%8 == 1:
            if tmod4 == 0 or tmod4 == 2:
                for t in GF:
                    if t**2 != d2:
                        aE = l+1 - EllipticCurve([0,2*t,0,t**2 - GF(d2),0]).order()
                        Bl2f = lcm((aE - af).norm(),Bl2f)
            else:
                for t in GF:
                    if t**2 != d2:
                        aE = l+1 - EllipticCurve([GF(1),(t-1)/GF(4),0,(t**2 - GF(d2))/GF(64),0]).order()
                        Bl2f = lcm((aE - af).norm(),Bl2f)

    #Even d1 and odd d2

    if d1%2 == 0:
        for t in GF:
            if t**2 != d2:
                aE = l+1 - EllipticCurve([GF(1),(t-1)/GF(4),0,(t**2 - GF(d2))/GF(64),0]).order()
                Bl2f = lcm((aE - af).norm(),Bl2f)

    #Odd d1 and even d2
    if d2.valuation(2) == 1:
        for t in GF:
            if t**2 != d2:
                aE = l+1 - EllipticCurve([0,2*t,0,GF(d2),0]).order()
                Bl2f = lcm((aE - af).norm(),Bl2f)
    elif 2 <= d2.valuation(2) and d2.valuation(2) <= 5:
        for t in GF:
            if t**2 != d2:
                aE = l+1 - EllipticCurve([0,t,0,GF(d2)/4,0]).order()
                Bl2f = lcm((aE - af).norm(),Bl2f)
    elif d2.valuation(2) >= 6:
        for t in GF:
            if t**2 != d2:
                aE = l+1 - EllipticCurve([GF(1),(t-1)/4,0,GF(d2)/GF(64),0]).order()
                Bl2f = lcm((aE - af).norm(),Bl2f)

    if legendre_symbol(d2,l) == 1:
        Bl2f = lcm(((l+1)**2-af**2).norm(),Bl2f)

    if f.base_ring().degree() > 1:
        Bl2f *= l

    return ZZ(Bl2f)


def multiFrey_over_Q(F,d1,d2,B,tmod4):
    r"""

    INPUT:
     - ``F`` : a list of newforms where Bl2f = 0
     - ``d1,d2`` : the signature of the equation
     - ``B`` : a positive integer
      - ``tmod4`` : the value of ``t`` modulo 4. when ``t`` is even both 0 and 2 are valid.

     OUTPUT:
        It applies the multi-Frey approach using `E_t` and `E` or `E^\prime`
        curves I have defined.
    """
    if (d1*d2)%2 == 1:
        if d2%4 == 3:
            N = 2**6 * radical(d1*d2)
            P = 3*5*11*13
        if d2%8 == 5:
            N = 2**5 *radical(d1*d2)
            P = 1

    G = Newforms(N)

    l = ZZ(3)
    while l<=B:
        GF = Integers(l)
        #computing Bf
        Bf = []
        if (d1*d2)%2 == 1:
            if d2%4 == 3:
                for t in GF:
                    if t**2 != d2:
                        aE = l+1 - EllipticCurve([0,2*t,0,GF(d2),0]).order()
                        Bl2f *= (aE - af)



#For D%4 == 3 and p>= 17

def no_solutions_D_mod4_3(D):

    if D%4 != 3:
        raise ValueError('Wrong input for D')

    N1 = 2**6 * prod(D.prime_factors())
    N2 = 2**5 * prod(D.prime_factors())
    Eigen1 = Newforms(N1,names = 'a1')
    Eigen2 = Newforms(N2,names = 'a2')
    print Eigen2,Eigen1

    for f1 in [Eigen1[0]]:
        for f2 in [Eigen2[0]]:
            q = ZZ(3)
            while q < 100:
                if D%q != 0:
                    GF = FiniteField(q)
                    Af1f2 = ZZ(1)
                    for a in range(q):
                        aqf1 = f1[q]
                        aqf2 = f2[q]
                        if (a**2 - D)%q != 0:
                            aqE1 = EllipticCurve([0,2*GF(a),0,GF(a**2-D),0]).order()
                            aqE2 = EllipticCurve([0,2*GF(a),0,GF(D),0]).order()
                            Baqf1 = (aqE1-aqf1).absolute_norm()
                            Caqf2 = (aqE2-aqf2).absolute_norm()
                        else:
                            Baqf1 = ((q+1)**2 - aqf1**2).absolute_norm()
                            Caqf2 = ((q+1)**2 - aqf2**2).absolute_norm()
                        Af1f2 *= gcd(Baqf1,Caqf2)
                    print ZZ(Af1f2).prime_factors()
        print 'q',q
        q = Primes().next(q)

    return 1

#Triples of small solutions and small p

def solutions_for_small_primes(D,primes, reduce = True):
    r"""

    INPUT:
        - ``D`` : a list of positive non-square integers
        - ``primes`` : a list of odd rational primes
        - ``reduce`` : use of Bouyer-Streng algorithm to reduce Thue equations

    OUTPUT:
        All solutions of `a^2-d=b^p` for `d` in ``D`` and `p` in ``primes``.

    EXAMPLE:

        sage: solutions_for_small_primes([2,3],[3,5,7])
            [[-1, -1, 2], [1, -1, 2], [2, 1, 3], [-2, 1, 3]]
    """
    solutions = []
    for d in D:
        for p in primes:
            for triple in solutions_for_fix_D_and_p(ZZ(d),ZZ(p),reduce):
                if triple not in solutions:
                    solutions.append(triple)
    return solutions


def solutions_for_fix_D_and_p(D,p,reduce):
    r"""

    INPUT:
        - ``D`` : a  non-square integer
        - ``p`` : an odd rational primes
        - ``reduce`` : use of Bouyer-Streng algorithm to reduce Thue equations

    OUTPUT:
        All solutions of `a^2-D=b^p`.

    EXAMPLE:

        sage: solutions_for_fix_D_and_p(17,3,True)
            [[-1, -1, 2], [1, -1, 2], [2, 1, 3], [-2, 1, 3]]
    """
    D2 = D.squarefree_part()
    D1 = sqrt(D/D2)
    if D2%4 == 1:
        x = polygen(QQ)
        K = NumberField(x**2-x+(1 - D2)/4,'r')
        sqrtD2 = 2 * K.gen() - 1
    else:
        K = QuadraticField(D2,'r')
        sqrtD2 = K.gen()

    s1,s2 = K.embeddings(K)
    ep = K.units()[0]

    P = K.ideal(2 * D).prime_factors()
    A = []
    for v in cartesian_product_iterator([xrange(p)] * len(P)):
        a = prod([pr**e for pr,e in zip(P,v)])
        if (s1(a) + s2(a)).divides(K.ideal(2* D1 * sqrtD2)):
            N = s1(a) * s2(a)
            if not len([1 for pr in P if N.valuation(pr)%p != 0]) > 0:
                if a not in A:
                    A.append(a)

    if K.class_number() == 1:
        B = [K.ideal(1)]
    else:
        rep = K.class_group().gens_values()[0]
        B = [K.ideal(1)]
        for e in range(1,K.class_number()):
            B.append(rep**e)

    Gpr = []
    for a in A:
        for b in B:
            w = a * b**(-p)
            if w.is_principal():
                Gpr.append(w.gens_reduced()[0])

    Gamma = []
    for g in Gpr:
        for j in range(-(p-1)/2,(p+1)/2):
            Gamma.append(g * ep**j)

    t = polygen(K)
    print 'ready for Thue'
    triples = []
    # print 'Gamma',Gamma
    for g in Gamma:
        # print 'g',g
        f = ((s1(g) * (t + s1(K.gen()))**p - s2(g) * (t + s2(K.gen()))**p)/(2*sqrtD2)).change_ring(QQ)
        # return f,D1
        print 'f',f
        d = lcm([a.denominator() for a in f.list()])
        # print 'd',d
        if reduce == True and f.degree() != 2:
            fred, T,u= reduce_polynomial(d * f,f.degree(),transformation = True)
            A = T.determinant()**f.degree() * u * D1 * d
            if A not in ZZ:
                return []
            # print 'A',A
        else:
            fred = f *d
            T = identity_matrix(QQ,2,2)
            u = 1
            A = D1 * d

        # print 'T',T
        # print 'u',u
        # print 'A',A
        print 'fred',fred
        for [U1,V1] in pari(fred).thueinit().thue(A).sage():
            # print 'U1,V1',U1,V1
            (U,V) = T*vector([U1,V1])/T.determinant()
            if U in ZZ and V in ZZ:
                U = ZZ(U)
                V = ZZ(V)
                # print 'U,V',U,V
                x = ((s1(g) * (U + V * s1(K.gen()))**p + s2(g) * (U + V * s2(K.gen()))**p))/2
                # print 'x',x
                if x in ZZ:
                    yp = ZZ(x**2 - D)
                    if yp.is_perfect_power():
                        y,q = yp.perfect_power()
                        if y.abs() == 1:
                            if [ZZ(x),y,D] not in triples:
                                triples.append([ZZ(x),y,D])
                        if q%p == 0:
                            l = ZZ(q/p)
                            if [ZZ(x),y**l,D] not in triples:
                                triples.append([ZZ(x),y**l,D])
        # print 'triples',triples
    return triples


def small_solutions(B,D):

    solutions = []
    for d in D:
        x = 0
        while x < B:
            yp = x**2 - d
            if yp.abs() == 1:
                solutions.append([x,d])
            elif yp.is_perfect_power():
                y,q = yp.perfect_power()
                if q%2 == 1 or len(q.factor()) > 1:
                    if [x,d] not in solutions:
                        solutions.append([x,d])
            x += 1
    return solutions



