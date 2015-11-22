def find_tau_S3(L):
    r"""

    INPUT:
        - ``L`` : a `S_3` extension which is defined over its quadratic subfield

    OUTPUT:
        All elements of order 2 of the Galois group

    EXAMPLE::

        sage:

    """
    M = L.base_field()
    tau = find_tau(M)

    T = []
    for t in L.embeddings(L):
        if len([1 for g in M.gens() if t(g) == tau(g)]) == len(M.gens()):
            T.append(t)
    return T


def smaller_R(Gl,Gm):
    r"""

    INPUT:
        - ``Gl`` : a list of generators where `\lambda` lies
        - ``Gm`` : a list of generators where `\mu` lies

    OUTPUT:
        A `R` such that `\frac{1}{R}\leq\mid\lambda\mid_{\mathfrak p}\leq R` for all infinite `\mathfrak p` in the support of ``Gl``

    """

    infinite_primes = sum(support_of_G(G,200),[])


def exponents_for_G_mod_I(I,G):
    gens_orders = I.idealstar().gens_orders()
    G_exp  = []
    for g in G:
        g_exponent = lcm([gen_order/gcd(gen_order,g_order) for gen_order,g_order in zip(gens_orders,I.ideallog(g))])
        G_exp.append(g_exponent)
    return G_exp


def modified_sieve_for_p_in_support_of_Gl_S3(prime,p2,Gm,Sl,bounds,bound_prime,R,infinite_primes):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field K which a power of a single prime `\mathfrak p`
        - ``Gm`` : a list of generators of a subgroup of `K^*`
        - ``Sl`` : a list of finite primes
        - ``bounds`` : a list of upper bounds for the exponents of the generators(including torsion)

    OUTPUT:
        All `\lambda` of the solutions of the S-unit equation `\lambda+\mu=1` such that `\mu\in G_m`, `I` divides
        `\lambda` and `\lambda` is a ``Sl`` unit.

    EXAMPLE::

        sage: L = QuadraticField(17,'b')
        sage: b = L.gen()
        sage: Gl = [L(-1), -8*b + 33, -3/4*b + 13/4]
        sage: SL = [L.ideal(-1/2*b + 3/2),L.ideal(-1/2*b - 3/2),L.ideal(-b)]
        sage: sieve_for_p_in_support_of_Gl(SL[0]^5,Gl,SL,398)
            [0]
    """
    if Gm == []:
        raise ValueError('Gl is empty')
    L = Gm[0].parent()
    sigma = find_sigma(L)
    SunitL = L.S_unit_group(S=Sl)
    # prime ,prime_exp = I.factor()[0]
    sigma_prime = sigma(prime)
    primel = sigma(sigma_prime)
    Gl = [sigma(sigma(g)) for g in Gm]
    tau = [tau for tau in find_tau_S3(L) if len([1 for g in Gl if g * tau(g) == 1]) == len(Gl)][0]
    tau_prime = tau(prime)
    # print '[mu*sigma(sigma(tau(mu))) for mu in Gm]',[mu*sigma(sigma(tau(mu))) for mu in Gm]

    #here we need to make a change of generators such that all the generators have 0 valuation at p
    Gm0 = [Gm[0]**i for i in range(Gm[0].multiplicative_order())]

    exp = 1
    I = prime
    while I.idealstar().order() == 1:
        exp += 1
        I *= prime
    finish = False
    while not finish and exp <= bound_prime:
        orders = I.idealstar().gens_orders()
        # print 'orders',orders

        #we create the congruence relations for the exponents with respect to the ideal p**n
        M = matrix(ZZ,len(Gm[1:]),len(orders),[I.ideallog(g) for g in Gm[1:]])
        # print 'M',M
        Gm0log = matrix(ZZ,[I.ideallog(m0) for m0 in Gm0])
        # print 'new_Gm0log',new_Gm0log
        GCD = [gcd(list(col)+[m]+list(m0)) for col,m,m0 in zip(M.columns(),orders,Gm0log.columns())]
        # print 'GCD',GCD
        prime_orders = [c/g for c,g in zip(orders,GCD)]
        # print 'prime_orders',prime_orders
        prime_M = matrix(ZZ,[col/g for col,g in zip(M.columns(),GCD)]).transpose()
        # print 'prime_M',prime_M
        prime_Gm0log =matrix(ZZ,[col/g for col,g in zip(Gm0log.columns(),GCD)]).transpose()
        # print 'prime_Gm0log',prime_Gm0log
        # print 'max(prime_orders)',max(prime_orders)
        # print 'sqrt(max(bounds))',RR(sqrt(max(bounds)))
        # print 'exponents_for_G_mod_I(I,Gm[1:])',max(exponents_for_G_mod_I(I,Gm[1:]))
        Gm_exp = exponents_for_G_mod_I(I,Gm[1:])


        #Check if we have to increase the exponent
        if max(Gm_exp) > sqrt(max(bounds)):
            finish = True
        else:
            exp += 1
            I *= prime

    precision = infinite_primes[0].codomain().precision()
    A = matrix(RealField(prec = precision),[[log(s(g).abs()) if is_real_place(s) else 2*log(s(g).abs()) for g in Gm[1:]] for s in infinite_primes])
    A /= log(R)
    # print 'A',A
    # AD = A * diagonal_matrix(ZZ,Gm_exp)
    # print 'AD',AD
    # print 'A',A

    maxprime_order = max(prime_orders)
    Gm_exp = exponents_for_G_mod_I(I,Gm[1:])
    # print 'Gm_exp',Gm_exp
    import time
    Sunits = []
    n = len(infinite_primes)

    for m0,prime_m0log in zip(Gm0[1:],prime_Gm0log[1:]):
        # print 'm0',m0
        start = time.time()
        # print 'prime_m0log',prime_m0log
        congruence_bounds = [xrange(exp) if 2*b >= exp else xrange(-b,b) for exp,b in zip(Gm_exp,bounds[1:])]
        Bprime = [0 if 2*b >= exp else 1 for exp,b in zip(Gm_exp,bounds[1:])]
        print 'congruence_bounds',congruence_bounds
        print 'Bprime',Bprime
        print 'The number of congruences I have to check %s'%(prod([len(c) for c in congruence_bounds]))
        elements = []
        vectors_m0 = []
        valuations = []
        start_congruence = time.time()
        # return 1
        for v in cartesian_product_iterator(congruence_bounds):
            v = vector(v)
            if vector([((v*col)+t0)%t for t,t0,col in zip(prime_orders,prime_m0log,prime_M.columns())]).is_zero():
                # print 'v',v
                vectors_m0.append(v)
                # count += 1

        end_congruence = time.time()
        print 'time for congruence %s'%(end_congruence - start_congruence)
        cong_percent = QQ(len(vectors_m0))/QQ(prod([len(c) for c in congruence_bounds]))
        print 'percent for congruence = %s'%(cong_percent.n(21))
        # print 'number of cases I have to check=%s'%(count*prod([2*b+1 if i == 0 else 1 for b,i in zip(B,Bprime)]))
        D = [len(c) if bpr == 0 else 1 for bpr,c in zip(Bprime,congruence_bounds)]
        Dlcm = lcm(D)
        print 'D',D
        vectors = reduce_number_of_v0_S3(prime,Gm,Gl,m0,sigma(sigma(m0)),D,vectors_m0,Bprime)
        B = [QQ(b/Dlcm).floor()+1 if len(c) !=0 else 1 for b in bounds[1:]]
        print 'B',B
        print 'final number of cases = %s'%(len(vectors)*prod([2*b if bpr == 0 else 1 for bpr,b in zip(Bprime,B)]))
        # return vectors_m0
        val0 = vector([g.valuation(sigma(p2)) for g in Gm[1:]])
        print val0
        V0 = []
        Vn0 = []
        for v in vectors:
            if v*val0%Dlcm == 0:
                V0.append(v)
            else:
                Vn0.append(v)
        print 'V0',len(V0)
        print 'Vn0',len(Vn0)
        # return 1
        # max_Am0 = max([(A*v).norm() for v in vectors_m0])
        # vectors_m1 = []
        #
        # for v in cartesian_product_iterator([xrange(-b,b) if i != congruence_bounds.index(max(congruence_bounds)) else xrange(b) for i,b in enumerate(B)]):
        #     if (AD * vector(v)).norm() <= sqrt(n) + max_Am0:
        #         vectors_m1.append(v)
        # v1_percent = len(vectors_m1)/prod([2*b+1 if i == 0 else xrange(1) for b,i in zip(B,Bprime)])
        #
        # print 'percent for v',(v1_percent * cong_percent).n(21)
        # print 'number of final cases',len(vectors_m1) * len(vectors_m0)
        # return vectors_m0,vectors_m1,valuations
        # for v0 in vectors_m0:
        #     start_for_loop_v0 = time.time()
        #     vectors = []
        #     for v in vectors_m1:
        #         if (A*v0 + AD * vector(v)).norm() <= sqrt(n):
        #             vectors.append(v)

        start_loop = time.time()
        if len(vectors) != 0:
            print 'if count != 0'
            p5 = L.prime_above(5)
            # M = matrix(ZZ,)

            Gm_powers = [g**Dlcm if b == 0 else 1 for g,b in zip(Gm[1:],Bprime)]
            Gm_powers_sigma_square = [sigma(sigma(g))**Dlcm if b == 0 else 1 for g,b in zip(Gm[1:],Bprime)]

            count_big = 0
            count_small = 0
            sum = 1
            for v1 in cartesian_product_iterator([xrange(-b,b) if i == 0 else xrange(1) for b,i in zip(B,Bprime)]):
                start_for_v1 = time.time()
                # V = []
                v1 = vector(v1)
                # for v0 in V0:
                #     if (A*(v1+v0)).norm() <= sqrt(n):
                #         sum += 1
                # print 'v1-2',v1
                # count_big += 1
                mu1 = prod([g**e for g,e in zip(Gm_powers,v1)])
                mu1_sigma = prod([g**e for g,e in zip(Gm_powers_sigma_square,v1)])
                for v0 in V0:
                    # print 'v0',v0
                    # v0 = vector(v0)
                    start_v0 = time.time()
                    mu0 = m0 * prod([g**e for g,e in zip(Gm[1:],v0)])
                    mu0_sigma = sigma(sigma(mu0))
                    if mu0_sigma * mu1_sigma - mu0 * mu1 * mu0_sigma * mu1_sigma == 1:
                        count_small += 1
                        print 'percent last loop',QQ(count_small)/QQ(count_big)
                        if is_S_unit_element(SunitL,1 - mu0 * mu1) or is_S_unit_element(SunitL,1 - 1/(mu0 * mu1)):
                            if mu0 * mu1 not in Sunits:
                                Sunits.append(mu0 * mu1)
                    # end_v0 = time.time()
                    # print 'time for each v0 %s'%(end_v0-start_v0)
                end_for_v1 = time.time()
                print 'time for each v1 = %s'%(end_for_v1 - start_for_v1)

        end_loop = time.time()
        print 'time for one loop %s'%(end_loop-start_loop)
        print 'sum',sum
        return Sunits, exp


def reduce_number_of_v0_S3(prime,Gm,Gl,m0,l0,D,V0,Bprime):
    import time
    # Gmfree = Gm[1:]
    L = prime.ring()
    K = L.base_field().base_field()
    sigma = find_sigma(L)
    # Gl = [sigma(sigma(1/g)) for g in Gm]
    suppGm = support_of_G(Gm,10)[0]
    DM = diagonal_matrix(ZZ,D)
    Dlcm = lcm([d for d,bpr in zip(D,Bprime) if bpr == 0])
    # print 'Dlcm',Dlcm

    rational_primes = []
    for P in suppGm:
        p = P.absolute_norm().factor()[0][0]
        if p not in rational_primes:
            rational_primes.append(p)

    Prs = Primes()
    p = Integer(2)
    find_p2, find_p3, find_p6= [False]*3
    # print find_p2,find_p3,find_p6

    while (not find_p2) or (not find_p3) or (not find_p6):
        # print 'p',p
        # print find_p2,find_p3,find_p6
        if p not in rational_primes:
            if p % Dlcm == 1:
                # print 'p',p
                for P in K.primes_above(p):
                    if len(L.primes_above(P)) == 2 and not find_p2:
                        find_p2 = True
                        p2 = p
                    elif len(L.primes_above(P)) == 3 and not find_p3:
                        find_p3 = True
                        p3 = p
                    elif len(L.primes_above(P)) == 6 and not find_p6:
                        find_p6 = True
                        p6 = p
                p = Prs.next(p)
            else:
                p = Prs.next(p)
        else:
            p = Prs.next(p)


    P = [p2,p3,p6]
    Q = [p2**L.prime_above(p2).residue_class_degree(),p3**L.prime_above(p3).residue_class_degree(),p6**L.prime_above(p6).residue_class_degree()]
    i = Q.index(max(Q))
    P.pop(i)
    Q.pop(i)
    if Q[0] > Q[1]:
        Q.reverse()
        P.reverse()
    print 'P,Q',P,Q

    start_V1 = time.time()
    V1 = [vector(v1) for v1 in cartesian_product_iterator([xrange(Dlcm/d) if bpr == 0 else xrange(1) for d,bpr in zip(D,Bprime)])]
    vectors = sum([[v0+v1*DM for v1 in V1] for v0 in V0],[])
    end_V1 = time.time()
    # print 'time for V1',end_V1 - start_V1

    print 'vectors',len(vectors)
    for P in [L.prime_above(p) for p in P]:
        # print 'new prime',P.absolute_norm().factor()[0][0]
        OP = P.idealstar(flag = 2)
        gen = OP.gens_values()[0]
        gen_order = P.ideallog(gen)[0]
        # print 'gen_order',gen_order
        order = OP.gens_orders()[0]
        # print 'order',order

        M_Gmfree = matrix(ZZ,len(Gm[1:]),1,[P.ideallog(g)[0]%Dlcm for g in Gm[1:]])
        M_Glfree = matrix(ZZ,len(Gl[1:]),1,[P.ideallog(g)[0]%Dlcm for g in Gl[1:]])
        logm0 = vector(P.ideallog(m0))
        logl0 = vector(P.ideallog(l0))
        # print 'M_Gmfree',M_Gmfree
        # print 'M_Glfree',M_Glfree
        # print 'logm0',logm0
        # print 'logl0',logl0

        # Gmfree_exp = exponents_for_G_mod_I(P,Gmfree)
        # Glfree_exp = exponents_for_G_mod_I(P,Glfree)

        # for v in V0:
        # print 'Gmfree_exp',Gmfree_exp
        # print 'Glfree_exp',Glfree_exp
        # print 'orders',orders
        # print 'gen',gen
        # return 1
        dif = []
        for g in gen.powers(order)[1:]:
            if ((P.ideallog(g)[0] * gen_order)%Dlcm,(gen_order * P.ideallog(1-g)[0])%Dlcm) not in dif:
                dif.append(((P.ideallog(g)[0] * gen_order)%Dlcm,(gen_order * P.ideallog(1-g)[0])%Dlcm))
        # print 'len(dif)',len(dif)
        # for v in dif:
        #     if v[0] == 7 or v[0] == 30:
        #         print v
        V = []
        for v in vectors:
            # print '(v * M_Gmfree + logm0) = %s,(v * M_Glfree + logl0) = %s',(v * M_Gmfree)[0],(v * M_Glfree )[0]
            if ((v * M_Gmfree + logm0)[0]%Dlcm,(v * M_Glfree + logl0)[0]%Dlcm) in dif:
                if v not in V:
                    V.append(v)
        vectors = V
        print 'vectors',len(vectors)
        # return dif,vectors

    return vectors


# def sieve_with_outside_primes_S3(Gm,Gl):



def testegros(SQ):

    from sage.schemes.elliptic_curves.ell_egros import egros_from_j_1728
    SK = K.primes_above(prod(SQ))
    # print 'SK',SK
    curvesK = [E.change_ring(QQ).minimal_model() for E in egros_from_1728_over_K(K,SK)]
    curvesQ = [E for E in egros_from_j_1728(SQ)]

    print 'number over K',len(curvesK)
    print 'number over Q',len(curvesQ)

    # return curvesK,curvesQ
    if len(curvesK) != len(curvesQ):
        raise ValueError('They have found different number of curves')
    for E in curvesK:
        if E not in curvesQ:
            print 'I find this not in both',E

    return curvesK,curvesQ


#we don't use this in C2 case
def sieve_for_p_in_support_of_Gl_C2(I,Gm,Sl,bounds):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field K which a power of a single prime `\mathfrak p`
        - ``Gm`` : a list of generators of a subgroup of `K^*`
        - ``Sl`` : a list of finite primes
        - ``bounds`` : a list of upper bounds for the exponents of the generators(including torsion)

    OUTPUT:
        All `\lambda` of the solutions of the S-unit equation `\lambda+\mu=1` such that `\mu\in G_m`, `\mathfrak p`
        is in the support of  `G_m`, `I` divides `\lambda` and `\lambda` is a ``Sl`` unit.

    EXAMPLE::

        sage: L = QuadraticField(17,'b')
        sage: b = L.gen()
        sage: Gl = [L(-1), -8*b + 33, -3/4*b + 13/4]
        sage: SL = [L.ideal(-1/2*b + 3/2),L.ideal(-1/2*b - 3/2),L.ideal(-b)]
        sage: sieve_for_p_in_support_of_Gl(SL[0]^5,Gl,SL,398)
            [0]
    """
    if Gm == []:
        raise ValueError('Gl is empty')
    L = Gm[0].parent()
    tau = find_tau(L)
    SunitL = L.S_unit_group(S=Sl)
    prime ,prime_exp = I.factor()[0]
    # print 'prime_exp',prime_exp
    tau_prime = tau(prime)
    # print 'prime,tau_prime',prime,tau_prime

    #here we need to make a change of generators such that all the generators have 0 valuation at p
    new_Gm0, new_Gm ,k= a_basis_with_0_order_at_p(prime,Gm)
    print 'k',k
    reduce_bounds = [e for i,e in enumerate(bounds) if i != k]

    #we create the congruence relations for the exponents with respect to the ideal p**n
    orders = I.idealstar().gens_orders()
    M = matrix(ZZ,len(new_Gm),len(orders),[I.ideallog(g) for g in new_Gm])
    new_Gm0log = [I.ideallog(m0) for m0 in new_Gm0]

    Sunits = []
    # print 'reduce_bounds',reduce_bounds
    for m0log in new_Gm0log:

        #we divide the congruence relations with the gcd of the coefficients
        GCD = [gcd(list(col)+[m,m0]) for col,m,m0 in zip(M.columns(),orders,m0log)]
        print 'GCD',GCD
        prime_M = matrix(ZZ,[col/g for col,g in zip(M.columns(),GCD)]).transpose()
        prime_orders = [c/g for c,g in zip(orders,GCD)]
        prime_m0log = [c/g for c,g in zip(m0log,GCD)]
        maxorder = max(prime_orders)
        if k != 0:
            congruence_bounds = [xrange(maxorder) if 2*b >= maxorder else xrange(-b,b) for b in reduce_bounds[1:]]
            Bpr = [0 if 2*b >= maxorder else 1 for b in reduce_bounds[1:]]
            B = [QQ(b/len(c)).floor()+1 if len(c) !=0 else 1 for b,c in zip(bounds[1:],congruence_bounds[1:])]
            new_Gm_exp = [g**len(c) if b == 0 else 1 for g,c,b in zip(new_Gm,congruence_bounds,Bpr)]
            # congruence_bound = [min(max(prime_orders),t) for t in reduce_bounds[1:]]
            # Bprime = [(QQ(b/c)).floor() for c,b in zip(congruence_bound,reduce_bounds[1:])]
        else:
            congruence_bounds = [xrange(maxorder) if 2*b >= maxorder else xrange(-b,b) for b in reduce_bounds[1:]]
            Bpr = [0 if 2*b >= maxorder else 1 for b in reduce_bounds[1:]]
            B = [QQ(b/len(c)).floor()+1 if len(c) !=0 else 1 for b,c in zip(bounds[1:],congruence_bounds[1:])]
            new_Gm_exp = [g**len(c) if b == 0 else 1 for g,c,b in zip(new_Gm,congruence_bounds,Bpr)]
            # congruence_bound = [min(max(prime_orders),t) for t in reduce_bounds]
            # Bprime = [(QQ(b/c)).floor() for c,b in zip(congruence_bound,reduce_bounds)]
        # print 'congruence_bound',congruence_bounds
        # print 'Bprime',Bprime
        # print 'prime_M',prime_M
        # print 'prime_m0log',prime_m0log
        # print 'prime_orders',prime_orders

        # return prime_M,prime_m0log,prime_orders,new_Gm0, new_Gm

        count2 = 0
        count = 0
        elements = []
        valuations = []
        for v in cartesian_product_iterator(congruence_bounds):
            v = vector(v)
            if vector([((v*col)+m0)%m for m,col,m0 in zip(prime_orders,prime_M.columns(),prime_m0log)]).is_zero():
                mu = m0log * prod([g**e for g,e in zip(new_Gm,v)])
                if mu != 1:
                        elements.append(mu)
                        count += 1
        # return count,count2
        # print 'count',count
        # print 'percent=%s'%((count/prod(congruence_bound)).n(21))
        # print 'number of case I have to check=%s'%(count*prod([2*b for b in Bprime]))

        #we determine the solutions
        if count != 0:
            for v in cartesian_product_iterator([xrange(-b,b) if i == 0 else xrange(1) for b,i in zip(B,Bpr)]):
                m = prod([g**e for g,e in zip(new_Gm_exp,v)])
                for g in elements:
                    l = 1-m*g
                    if is_S_unit_element(SunitL,l):
                        if l not in Sunits:
                            Sunits.append(l)
    return Sunits#,prime,tau_prime,prime_exp

