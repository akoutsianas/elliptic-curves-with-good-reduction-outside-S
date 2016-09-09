def trivial_Tp_infinite_place(Bounds, place, Gens, delta):
    r"""

    INPUT:
        - ``Bounds`` : a list of upper bounds for the exponents of the generators
        - ``place`` (ring morphism): an infinite place `\mathfrak p` of a number field `K`
        - ``Gens`` : a list `[g_1,g_2,\cdots,g_n]` of elements of `K^*` which are linear independent
        - ``delta`` : a real positive number

    OUTPUT:
        True, if we are able to prove that the inequality `\mid \zeta\displaystyle\prod_{i=1}^{n}g_i^{a_i}-1\mid_{\mathfrak p}<\delta` does not have a non-trivial solution( as it is defined in the paragraph 3.1 of the reference) with `\max(\mid a_i\mid)\leq B` and `\zeta` a root of unity, otherwise False.

    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999

    EXAMPLE::

        sage: t = polygen(QQ)
        sage: L.<a> = (t^3+45*t+135).splitting_field()
        sage: SL = sum([L.primes_above(p) for p in [2,5,7]],[])
        sage: G = [247/4433463*a^5+2044/4433463*a^4+38657/4433463*a^3+253334/4433463*a^2+175325/1477821*a-61106/492607]
        sage: finite,real,complex = support_of_G(Gl,100)
        sage: R0 = evaluate_R0(88,Gl,finite+real+complex,100)
        sage: R1 = R0^(1/20)
        sage: trivial_Tp_infinite_place(88,complex[0],G,1/R1)
            True
    """
    K = place.domain()
    precision = place.codomain().precision()

    if is_real_place(place):
        delta_prime = -log(1 - delta)
    else:
        delta_prime = -log(1 - sqrt(delta)) / 2

    # when the absolute value of at least two generators is the same

    find_same_abs = False
    for i in range(len(Gens)):
        for j in range(i+1, len(Gens)):
            if place(Gens[i]).abs() == place(Gens[j]).abs():
                find_same_abs = True

    if find_same_abs:
        G = []
        bounds = []
        for i, g in enumerate(Gens):
            exists = False
            for j, g2 in enumerate(G):
                if place(g2).abs() == place(g).abs():
                    bounds[j] += Bounds[i]
                    exists = True
            if not exists:
                G.append(g)
                bounds.append(Bounds[i])
    else:
        G = Gens
        bounds = Bounds

    C = 1
    t = len(G)
    C_upper = 2 ** 1000  # arbitrary choice

    A = copy(identity_matrix(ZZ, t))

    if precision < log(C) / log(2):
        place = higher_precision(place, 2 * precision)

    y = zero_vector(ZZ, t)
    finish = False
    while not finish:
        if is_real_place(place):
            A[t - 1] = vector([(log(place(g).abs()) * C).round() for g in G])
            if A[t - 1, t - 1].is_zero():
                i, x = [[i, a] for i, a in enumerate(A[t - 1]) if not a.is_zero()][0]
                A[t - 1, t - 1] = x
                A[t - 1, i] = 0
                temp = bounds[i]
                bounds[i] = bounds[t - 1]
                bounds[t - 1] = temp
        else:
            A[t - 1] = vector([(log(place(g).abs()) * 2 * C).round() for g in G])
            if A[t - 1, t - 1].is_zero():
                i, x = [[i, a] for i, a in enumerate(A[t - 1]) if not a.is_zero()][0]
                A[t - 1, t - 1] = x
                A[t - 1, i] = 0
                temp = bounds[i]
                bounds[i] = bounds[t - 1]
                bounds[t - 1] = temp
        if not A.is_singular():
            l = minimal_vector(A.transpose(), y)
            if l <= sum([b ** 2 for b in bounds[:t - 1]]) + (sum([b for b in bounds]) / RR(2) + C * delta_prime) ** 2:
                C *= 10
                if C > C_upper:
                    return False
            else:
                return True
        else:
            C += 1
    return False


def trivial_Tp_finite_place(B, prime, M0, M, M0_logp, M_logp, delta, precision):
    r"""

    INPUT:
        - ``B`` : an upper bound for the exponents
        - ``prime`` : a prime ideal `\mathfrak p` of a number field `K`
        - ``M0`` : a list of elements in `K^*`
        - ``M`` : a list `[m_1,m_2,\cdots,m_n]` of elements of `K^*` which are linear independent
        - ``delta`` : a real positive number
        - ``precision`` : the precision

    OUTPUT:
         True, if we are able to prove that the inequality `\mid m_0\displaystyle\prod_{i=1}^{n}m_i^{a_i}-1\mid_{\mathfrak p}<\delta`
         does not have a non-trivial solution( as it is defined in the paragraph 3.2 of the reference) with
         `\max(\mid a_i\mid)\leq B` for all `m_0` in ``M0``, otherwise False.

    COMMENT:
        Should hold `\mid m_i\mid_{\mathfrak p}=1` for all `i=0,1,\cdots,n`.

    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999

    EXAMPLE::

        sage: t = polygen(QQ)
        sage: L.<a> = (t^3-45*t+135).splitting_field()
        sage: R0 = 1.4219031303e69
        sage: R1 = 1.9418581520e17
        sage: prime = L.ideal(7,3734/40719*a^5+10174/17451*a^4-670069/122157*a^3-1069720/122157*a^2+22387486/122157*a-52724345/122157)
        sage: M = [-347/122157*a^5-293/17451*a^4+2451/13573*a^3+29717/122157*a^2-82063/13573*a+1806725/122157,-1510/122157*a^5-458/5817*a^4+89627/122157*a^3+50500/40719*a^2-2974004/122157*a+6910454/122157]
        sage: trivial_Tp_finite_place(88,prime,-1,M,1/R1,40)
            True
    """
    if len([m for m in M + M0 if m.valuation(prime) != 0]) > 0:
        raise ValueError('There is an element without non zero valuation at prime')
    K = prime.ring()
    theta = K.gen()
    e = prime.absolute_ramification_index()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()

    delta_prime = -log(delta) / (e * f * log(p))
    if delta_prime < 1:
        return False, M0_logp, M_logp, precision
    M_logp_emb = [embedding_to_Kp(m, prime, precision) for m in M_logp]
    M0_logp_emb = [embedding_to_Kp(m0_logp, prime, precision) for m0_logp in M0_logp]
    n = e * f
    s = len(M)
    u = round((1 + s / n) * log(B) / log(p))

    # nothing changes if we take the valuation of the global field instead of its completion
    ordp_Disc = (K.disc([theta ** i for i in range(K.degree())])).valuation(p)

    c5 = delta_prime - ordp_Disc/2

    for k in range(len(M0_logp_emb)):
        m0_logp_emb = M0_logp_emb[k]
        c6 = min([min([a.valuation(p) for a in v]) for v in M_logp_emb + [m0_logp_emb]])
        c7 = c5 - c6
        lam = p ** c6
        T = [[v[i] / lam for i in range(n)] for v in M_logp_emb]
        T0 = [m0_logp_emb[i] / lam for i in range(n)]

        finish = False
        while not finish:
            if u <= precision:
                if u > c7:
                    return False, M0_logp, M_logp, precision
                A11 = copy(identity_matrix(ZZ, s))
                A12 = copy(zero_matrix(ZZ, s, n))
                A21 = copy(zero_matrix(s, n))
                A22 = p ** u * copy(identity_matrix(ZZ, n))
                y = vector(ZZ, n + s)
                for i in range(s):
                    A21[i] = vector([mod(a, p ** u) for a in T[i]])
                for i in range(n):
                    y[s + i] = -mod(T0[i], p ** u)
                A = block_matrix([[A11, A12], [A21.transpose(), A22]])
                l = minimal_vector(A.transpose(), y)
                if l > s * B ** 2:
                    finish = True
                else:
                    u += 1
            else:
                precision *= 2
                M_logp = [log_p(m, prime, precision) for m in M]
                M_logp_emb = [embedding_to_Kp(m, prime, precision) for m in M_logp]
                M0_logp = [log_p(m0, prime, precision) for m0 in M0]
                M0_logp_emb = [embedding_to_Kp(m0_logp, prime, precision) for m0_logp in M0_logp]
                m0_logp_emb = M0_logp_emb[k]
                c5 = delta_prime - ordp_Disc / 2
                c6 = min([min([a.valuation(p) for a in v]) for v in M_logp_emb + [m0_logp_emb]])
                c7 = c5 - c6
                lam = p ** c6
                T = [[v[i] / lam for i in range(n)] for v in M_logp_emb]
                T0 = [m0_logp_emb[i] / lam for i in range(n)]

    return True, M0_logp, M_logp, precision


def find_sigma(L):
    r"""
    INPUT:
        - ``L`` : a relative `p` degree Galois extension `L/M`, where `p` is a prime number

    OUTPUT:
        An generator `\sigma` of `Gal(L/M)`.

    EXAMPLE::

        sage: M.<a> = QuadraticField(-7)
        sage: t = polygen(M)
        sage: L.<b> = M.extension(t^3 - 15*t - 5*a)
        sage: find_sigma(L)
            Relative number field endomorphism of Number Field in b with defining
            polynomial x^3 - 15*x - 5*a over its base field
              Defn: b |--> -1/3*b^2 + (1/6*a - 1/2)*b + 10/3
                    a |--> a
    """
    if L.relative_degree() not in Primes():
        raise ValueError('The degree of the relative extension is not a prime number.')
    if not L.is_galois_relative():
        raise ValueError('The relative extension is not galois')
    M = L.base_field()
    temp = [s for s in L.embeddings(L) if len([1 for g in M.gens() if s(g) == g]) == len(M.gens())]

    return [s for s in temp if not len([1 for g in L.gens() if s(g) == g]) == len(L.gens())][0]


def find_tau(L):
    r"""

    INPUT:
        ``L``: a relative quadratic extension

    OUTPUT:
        A generator of the Galois group of ``L`` over its base field

    EXAMPLE::

        sage: L.<l1> = QuadraticField(2)
        sage: find_tau(L)
            Ring endomorphism of Number Field in l1 with defining polynomial x^2 - 2
                Defn: l1 |--> -l1
    """

    if L.relative_degree() != 2:
        raise ValueError('L is not a relative quadratic extension')
    K = L.base_field()
    for s in L.automorphisms():
        if len([g for g in L.base_field().gens() if s(g) == g]) == len(L.base_field().gens()):
            if len([g for g in L.gens() if s(g) == g]) != len(L.gens()):
                return s


def simple_loop_with_M0_M1(M0,M1,S):
    r"""

    INPUT:
        - ``M0`` : a list of elements of a number field `K`
        - ``M1`` : a list of elements of a number field `K`
        - ``S`` : a list of prime ideals of `K`

    OUTPUT:
        All elements `\mu_0\mu_1` with `\mu_0\in M_0` and `\mu_1\in M_1` such that `\mu_0\mu_1-1` is
        an `S`-unit.

    COMMENT:
        The key idea of the algorithm is that the matrices coming from the function ``.matrix(QQ)`` for
        each element of ``M0`` and ``M1`` commute. So, we can simultaneously diagonalise all of them.

    REFERENCE:
        A. Koutsianas - Applications of `S`-unit Equations to the Arithmetic of Elliptic Curves. PhD Thesis,
        University of Warwick, 2016.
    """

    if len(M0) == 0 or len(M1) == 0:
        raise ValueError('Either M0 or M1 is empty.')

    Sunit_group = M0[0].parent().S_unit_group(S = S)
    field_degree = M0[0].parent().absolute_degree()

    SM = []
    for pr in S:
        p = pr.ideal_below()
        if p not in SM:
            SM.append(p)
    SunitM_group = SM[0].ring().S_unit_group(S = SM)


    SQQ = []
    for pr in S:
        p = pr.absolute_norm().factor()[0][0]
        if p not in SQQ:
            SQQ.append(p)
    #
    # M0_low_degree = []
    # for m0 in M0:
    #     if m0.absolute_minpoly().degree() != field_degree:
    #         M0_low_degree.append(m0)
    #         M0.remove(m0)
    #
    # M1_low_degree = []
    # for m1 in M1:
    #     if m1.absolute_minpoly().degree() != field_degree:
    #         M1_low_degree.append(m1)
    #         M1.remove(m1)
    #
    # i = 0
    # while M0[i] in M0_low_degree:
    #     i += 1
    #
    # U = M0[i].matrix(QQ).eigenmatrix_right()[1]
    # Uinverse = U.inverse()
    # eigenvectors = M0[i].matrix(QQ).eigenvectors_right()
    # return U,M0[i].matrix(QQ)

    #we check the exceptional cases

    sunits = []
    d = 500
    # print 'M1s'
    # M1_matrices = []
    # for m1 in M1[:d]:
    #     if m1 not in M1_low_degree:
    #         M1_matrices.append(diagonal_matrix((Uinverse * m1.matrix(QQ) * U).diagonal()))
    #     for m0 in M0_low_degree:
    #         if is_S_unit_element(Sunit_group,1-m0*m1):
    #             sunits.append(m0*m1)
    # print 'M0s'
    # M0_matrices = []
    # for m0 in M0[:d]:
    #     if m0 not in M0_low_degree:
    #         M0_matrices.append(diagonal_matrix((Uinverse * m0.matrix(QQ) * U).diagonal()))
    #     for m1 in M1_low_degree:
    #         if is_S_unit_element(Sunit_group,1-m0*m1):
    #             sunits.append(m0*m1)
    #
    # Diag0 = []
    # Diag1 = []
    # for m0mat in M0_matrices[:d]:
    #     Diag0.append(vector(m0mat.diagonal()))
    #
    # for m1mat in M1_matrices[:d]:
    #         Diag1.append(vector(m1mat.diagonal()))

    import time
    start = time.time()
    print 'start matrices'

    M0inverse = [1/m0 for m0 in M0]
    for m0 in M0inverse[:d]:
        for m1 in M1[:d]:
            startmesa = time.time()
            if QQ((m0-m1).absolute_minpoly()(1)).prime_to_S_part(SQQ).abs() == 1:
                if is_S_unit_element(Sunit_group,1-m0*m1):
                    sunits.append(m0*m1)
            endmesa = time.time()


    # videntity = vector([1]*field_degree)
    # for m0,v0 in zip(M0[:d],Diag0):
    #     for m1,v1 in zip(M1[:d],Diag1):
    #         startmesa = time.time()
    #         if QQ(prod(videntity-v1.pairwise_product(v0))).prime_to_S_part(SQQ).abs() == 1:
    #             if is_S_unit_element(Sunit_group,1-m0*m1):
    #                 sunits.append(m0*m1)
    #         endmesa = time.time()
    #         # print 'time for each case ',endmesa - startmesa



    # for m0,m0mat in zip(M0[:d],M0_matrices[:d]):
    #     for m1,m1mat in zip(M1[:d],M1_matrices[:d]):
    #         if QQ(prod((I-m0mat*m1mat).diagonal())).prime_to_S_part(SQQ).abs() == 1:
    #             if is_S_unit_element(Sunit_group,1-m0*m1):
    #                 sunits.append(m0*m1)
    end = time.time()
    print 'time with matrices', end - start

    print 'start usual check'
    start = time.time()
    for m0 in M0[:d]:
        for m1 in M1[:d]:
            startmesa = time.time()
            if is_S_unit_element(Sunit_group,1-m0*m1):
                sunits.append(m0*m1)
            endmesa = time.time()
            # print 'time for each case without',endmesa - startmesa
    end = time.time()
    print 'time without matrices', end - start

    return 1


##Quadratic case


def choice_of_delta(place, G, bounds):
    r"""

    INPUT:
        - ``place`` (ring morphism) : an inifinite prime of a number field `K`
        - ``G`` : a list of generators of a multiplicative subgroup of `K^*`
        - ``bounds`` : a list of upper bounds for each generator

    OUTPUT:
        The value of the expression `e^{-\mid\Sum_ib_i\mid\log\mid g_i\mid_{\mathfrak p}\mid}` for `g_i` and `b_i` in ``G``
        and ``bounds`` respectively.

    EXAMPLE::

        sage
    """

    # return exp(-sum([(log(place(g).abs())).abs() * b for g,b in zip(G,bounds) if place(g).abs() != 1]))
    return exp(-sum([(log(place(g).abs())).abs() * b for g, b in zip(G, bounds) if
                     g.is_integral() and g.absolute_norm().abs() == 1]))


def reduce_bound_for_unit_generators_C2(Gl, Gm, bound_Gl, bound_Gm, R):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``Gm`` : a list of generators of the group where `\mu` lies
        - ``bound_Gl`` : a list of upper bounds for each generator of ``Gl``
        - ``bound_Gm`` : a list of upper bounds for each generator of ``Gm``

    OUTPUT:
        A list of upper bounds for each generator such that the bounds are smaller for the generators which are units

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions for `\mathfrak p` be an infinite prime

    EXAMPLE::

        sage:

    """
    L = Gl[0].parent()
    infinite_primes = sum(support_of_G(Gl, 200)[1:], [])

    # we find which generators are units
    units_index = [i for i, g in enumerate(Gl) if
                   g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i, g in enumerate(Gl) if i in units_index]
    if Glunit == []:
        return bound_Gl, R
    c1_units = c_constants(Glunit, 200)[0]

    # we are going to reduce the bound for units using Smart's ideas
    Bold = max([b for i, b in enumerate(bound_Gl) if i in units_index])

    # we find logRlprime
    logRlprime = max([sum(
            [b * log(p(g).abs()).abs() for b, g in zip(bound_Gl, Gl) if g not in Glunit]) if is_real_place(p) else sum(
            [2 * b * log(p(g).abs()).abs() for b, g in zip(bound_Gl, Gl) if g not in Glunit]) for p in infinite_primes])

    # we make an arbitrary choice of an initial delta
    delta_old = 1 / R
    delta_new = sqrt(delta_old)

    # we reduce the bounds for the units
    reduce_bounds = bound_Gl
    while True:
        # return bound_Gm[1:],infinite_primes[0],Gm[1:],delta_new
        if len([1 for place in infinite_primes if
                trivial_Tp_infinite_place(bound_Gm[1:], place, Gm[1:], delta_new)]) == len(infinite_primes):
            Bold = min((c1_units * log(delta_new).abs() + c1_units * logRlprime).floor(), Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_old)
            reduce_bounds = [min(b, Bold) if i in units_index else b for i, b in enumerate(bound_Gl)]
            # print 'reduce_bounds',reduce_bounds
        else:
            return reduce_bounds, 1 / delta_old ** 2


def sieve_in_C2(Gl, Gm, B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``Gm`` : a list of generators of the group where `\mu` lies
        - ``B`` : an upper bound for the absolute value of the exponents of the solutions

    OUTPUT:
        A listof `\lambda` of the solutions of the `S`-unit equation `\lambda +\mu = 1` up to the action of `S_3` whose
        absolute value of the exponents is less than ``B``.

    EXAMPLE::

        sage:
    """
    import time
    if Gl == [] or Gm == []:
        raise ValueError('Either Gl or Gm is empty')

    L = Gl[0].parent()
    tau = find_tau(L)
    Sl = support_of_G(Gl, 40)[0]
    Sm = support_of_G(Gm, 40)[0]
    SmnotSl = [p for p in Sm if p not in Sl]
    infinite_primes = L.places(prec=200)

    # we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()] + [B] * (len(Gl) - 1)
    bound_Gm = [Gm[0].multiplicative_order()] + [B] * (len(Gm) - 1)

    Sunits = []
    Smunit_group = L.S_unit_group(S=Sm)

    #the case Gl has at most one generator of the free part

    if len(Gl) == 1:
        for i in range(bound_Gl[0]):
            l = Gl[0]**i
            if is_S_unit_element(Smunit_group, 1 - l):
                if l not in Sunits:
                    Sunits.append(l)
        return Sunits

    if len(Gl) == 2:
        for v in cartesian_product_iterator([xrange(bound_Gl[0]), xrange(-bound_Gl[1], bound_Gl[1] + 1)]):
            l = prod([g ** e for g, e in zip(Gl, v)])
            if is_S_unit_element(Smunit_group, 1 - l):
                if l not in Sunits:
                    Sunits.append(l)
        return Sunits
    print 'bound_Gl-1', bound_Gl
    print 'bound_Gm-1', bound_Gm

    start = time.time()
    # we pick only one of the two split primes
    Slreduce = []
    for p in Sl:
        if (not p in Slreduce) and not (tau(p) in Slreduce):
            Slreduce.append(p)

    # for each prime in Slreduce we get a reduced upper bound for the valuation of lambda using Smart's idea

    bound_Slreduce = []
    for p in Slreduce:
        bound_Slreduce.append(reduce_the_bound_for_p_in_support_of_Gl_C2(p, Gm, B))

    # we get new upper bounds for the exponents

    bound_Sm = [0] * len(Sm)
    for i, p in enumerate(Sm):
        if p in Slreduce:
            bound_Sm[i] = bound_Slreduce[Slreduce.index(p)]
        elif tau(p) in Slreduce:
            bound_Sm[i] = bound_Slreduce[Slreduce.index(tau(p))]
        else:
            bound_Sm[i] = reduce_the_bound_for_p_in_support_of_Gl_C2(p, Gl, B)

    print 'boundSlreduce', bound_Slreduce, Slreduce
    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Slreduce, bound_Slreduce, bound_Gl)
    bound_Gm = bounds_for_exponents_from_bounds_for_primes(Gm, Sm, bound_Sm, bound_Gm)
    print 'bound_Gl-2', bound_Gl
    print 'bound_Gm-2', bound_Gm

    R = max([exp(sum([(log(s(g).abs())).abs() * b if is_real_place(s) else (2 * log(s(g).abs())).abs() * b for g, b in
                      zip(Gl, bound_Gl)])) for s in infinite_primes])
    bound_Gl, R = reduce_bound_for_unit_generators_C2(Gl, Gm, bound_Gl, bound_Gm, R)

    print 'bound_Gl-3', bound_Gl
    print 'bound_Gm-3', bound_Gm

    # we use triangle inequality to reduce the bound

    old_bound = copy(bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl, p, bound_Gl, R)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl, p, bound_Gl, R)

    print 'bound_Gl-4', bound_Gl
    print 'bound_Gm-4', bound_Gm
    print 'bound_Sl', bound_Slreduce
    print 'bound_Sm', bound_Sm

    Sunits = []

    # Since we have reduced as much as we can, now we are able to make a simple loop to find the rest of the solutions

    Smunit_group = L.S_unit_group(S=Sm)
    for v in cartesian_product_iterator([xrange(bound_Gl[0]), xrange(bound_Gl[1] + 1)] + [xrange(-b, b + 1) for b in bound_Gl[2:]]):
        l = prod([g ** e for g, e in zip(Gl, v)])
        if is_S_unit_element(Smunit_group, 1 - l):
            if l not in Sunits:
                Sunits.append(l)

    # we throw away 0 and 1

    while 0 in Sunits:
        Sunits.remove(0)
    while 1 in Sunits:
        Sunits.remove(1)

    return Sunits


def sieve_for_p_not_in_support_of_Gl_C2(p, Gl, SL, bounds):
    r"""

    INPUT:
        - ``p`` : an ideal of a number field `K`
        - ``Gl`` : a list of generators of a subgroup of `K^*`
        - ``SL`` : a list of finite
        - ``bound`` : a list of upper bounds for the exponents of the solutions

    OUTPUT:
        All `\lambda` of solutions of the S-unit equation `\lambda+\mu=1` such that `p` divides
        `\mu` and `p` is not in the support of ``Gl``.

    EXAMPLE::

        sage: L = QuadraticField(17,'b')
        sage: b = L.gen()
        sage: Gl = [L(-1), -8*b + 33, -3/4*b + 13/4]
        sage: p = [L.ideal(-1/2*b + 3/2),L.ideal(-1/2*b - 3/2),L.ideal(-b)]
        sage: sieve_for_p_not_in_support_of_Gl(SL[2]^2,Gl,SL,398)
            [7/16*b + 33/16, -1/8*b + 9/8, 1/8*b - 9/8, -5/4*b + 21/4, -8*b + 33, 8*b - 33, -9/32*b + 49/32,
             528*b + 2177, -23/256*b + 273/256, -528*b + 2177, 9/32*b + 49/32, 8*b + 33, -8*b - 33, 5/4*b + 21/4,
             1/8*b + 9/8, -1/8*b - 9/8, -7/16*b + 33/16, -1207/64*b + 4977/64, 23/256*b + 273/256, -3/4*b - 13/4,
             -1, 3/4*b - 13/4, 1207/64*b + 4977/64]
    """
    if Gl == []:
        raise ValueError('Gl is empty')
    L = Gl[0].parent()
    Glfree = [g for g in Gl if g.multiplicative_order() == Infinity]
    g0 = [g for g in Gl if g.multiplicative_order() != Infinity][0]
    SunitL = L.S_unit_group(S=SL)

    # we create the congruence relations for the exponents with respect to the ideal p**n
    orders = p.idealstar().gens_orders()
    # print 'orders',orders
    M = matrix(ZZ, len(Gl), len(orders), [p.ideallog(g) for g in Gl])

    # we divide the congruence relations with the gcd of the coefficients
    GCD = [gcd(list(col) + [m]) for col, m in zip(M.columns(), orders)]
    # print 'GCD=',GCD
    C = matrix(ZZ, [col / g for col, g in zip(M.columns(), GCD)]).transpose()
    # print 'C',C
    prime_orders = [c / g for c, g in zip(orders, GCD)]
    maxorder = max(prime_orders)
    # print 'prime_orders',prime_orders

    # we need a bound for the exponents of the solutions mod p**n
    congruence_bounds = [xrange(bounds[0])] + [xrange(maxorder) if 2 * b >= maxorder else xrange(-b, b) for b in
                                               bounds[1:]]
    Bpr = [0 if 2 * b >= maxorder else 1 for b in bounds[1:]]
    # print 'congruence_bounds',congruence_bounds

    # we determine the solutions module p
    count = 0
    elements = []
    for v in cartesian_product_iterator(congruence_bounds):
        v = vector(v)
        if vector([(v * col) % m for m, col in zip(prime_orders, M.columns())]).is_zero():
            elements.append(prod([g ** e for g, e in zip(Gl, v)]))
            count += 1
    # print 'count',count
    # print 'percent',(count/prod(congruence_bound)).n(21)

    # we determine the global solutions

    Sunits = []
    B = [QQ(b / len(c)).floor() + 1 if len(c) != 0 else 1 for b, c in zip(bounds[1:], congruence_bounds[1:])]
    # print 'B',B
    Gl_exp = [g ** len(c) if b == 0 else 1 for g, c, b in zip(Gl[1:], congruence_bounds[1:], Bpr)]
    count = 0
    for v in cartesian_product_iterator([xrange(-b, b) if i == 0 else xrange(1) for b, i in zip(B, Bpr)]):
        # print 'v',v
        l = prod([g ** e for g, e in zip(Gl_exp, v)])
        # print 'case',count
        count += 1
        for i, g in enumerate(elements):
            # print 'i',i
            mu = 1 - l * g
            if is_S_unit_element(SunitL, mu):
                if (1 - mu) not in Sunits:
                    Sunits.append(1 - mu)
    # print 'percent',(count/(g0.multiplicative_order()*congruence_bound**len(Glfree))).n(21)
    return Sunits


def reduce_the_bound_for_p_in_support_of_Gl_C2(prime, Gm, B):
    r"""

    INPUT:
        - ``prime`` : a prime ideal which lies in the support of `G_\lambda`
        - ``Gm`` : a list of generators of the group ``G_\mu``
        - ``B`` : an upper bound for the exponents of the solutions `\lambda ,\mu`

    OUTPUT:
        A reduced upper bound for the valuation of `\lambda` at the prime ideal ``prime``.

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions.

    EXAMPLE::

        sage:

    """
    Blow = 1
    Bupp = B
    Bmid = RR((Blow + Bupp) / 2).floor()

    L = prime.ring()
    Labs = L.absolute_field('a')
    eLLabs = L.embeddings(Labs)[0]
    prime_abs = eLLabs(prime)
    Gm_abs = [eLLabs(g) for g in Gm]
    p = prime_abs.absolute_norm().factor()[0][0]
    f = prime_abs.residue_class_degree()
    precision = 200

    # we evaluate the new basis of Gm of elements with zero valuation at prime and their p-adic logarithms
    new_Gm0_abs, new_Gm_abs, k = a_basis_with_0_order_at_p(prime_abs, Gm_abs)
    new_Gm_abs_logp = [log_p(m, prime_abs, precision) for m in new_Gm_abs]
    new_Gm0_abs_logp = [log_p(m0, prime_abs, precision) for m0 in new_Gm0_abs]

    while Bupp - Blow > 1:

        trivial, new_Gm0_abs_logp, new_Gm_abs_logp, precision = trivial_Tp_finite_place(B, prime_abs, new_Gm0_abs,
                                                                                        new_Gm_abs, new_Gm0_abs_logp,
                                                                                        new_Gm_abs_logp,
                                                                                        p ** (-Bmid * f), precision)
        if trivial:
            Bupp = Bmid
        else:
            Blow = Bmid
        Bmid = (QQ((Blow + Bupp) / 2)).floor()
    return Bupp


def bounds_for_exponents_from_bounds_for_primes(G, primes, primes_bounds, exp_bounds):
    r"""

    INPUT:
        - ``G`` : a list of generators of a finitely generated subgroup of `K^*`
        - ``primes`` : a list of primes which lie in the support of ``G``
        - ``primes_bounds`` : a list of upper bounds for the absolute value of the valuation of the elements of ``G`` with respect to each prime in ``P``
        - ``exp_bounds`` : a list of initial bounds for the generators

    OUTPUT:
        A list with new upper bounds for the absolute value of the exponents of the generators ``G`` taking into account ``BP``

    EXAMPLE::

        sage:
    """
    infinite_primes = sum(support_of_G(G, 200)[1:], [])

    # we find for which generators the exponents will change
    GS = [g for g in G if len([1 for p in primes if g.valuation(p) != 0]) > 0]
    # print 'GS',GS
    GSenu = [G.index(g) for g in GS]

    GSenu_bounds = [b for i, b in enumerate(exp_bounds) if G[i] in GS]
    # print 'primes_bounds',primes_bounds
    # print 'GSenu',GSenu
    # print 'GSenu_bounds',GSenu_bounds
    A = matrix(ZZ, len(primes), [[g.valuation(p) for g in GS] for p in primes])
    # B = matrix(RR,len(infinite_primes),[[log(s(g).abs()) if is_real_place(p) else 2*log(s(g).abs()) for g in GS] for p in infinite_primes])
    # AB = block_matrix([[A],[B]])
    # print 'A',A
    # we find the new exponents and return a list with the new exponents

    # if X is empty we use simply inequalities to reduce the bound

    X = Set(range(A.dimensions()[0])).subsets(len(GS)).list()

    if X == []:
        for i, gen in enumerate(GSenu):
            # print 'gen=%s, i=%s'%(gen,i)
            index_bound = exp_bounds[gen]
            # print 'index_bound',index_bound
            for j, v in enumerate(A.rows()):
                # print 'S=%s'%(sum([b*a.abs() for b,a,k in zip(GSenu_bounds,v,range(len(v))) if k != i]))
                S = sum([b * a.abs() for b, a, k in zip(GSenu_bounds, v, range(len(v))) if k != i])
                low_b = ((S + primes_bounds[j]) / v[i]).floor()
                # print 'low_b',low_b
                if low_b < exp_bounds[gen]:
                    exp_bounds[gen] = low_b
                    # print 'exp_bounds',exp_bounds
        return exp_bounds

    # if X is not empty we use a submatrix of A

    new_exponents = copy(exp_bounds)
    min_exp_bounds = +Infinity
    for g in X:
        M = A[g.list(), :]
        if M.rank() == len(GS):
            # print 'M',M
            Minv_abs = M.inverse().apply_map(abs)
            x = matrix(primes_bounds)[:, g.list()]
            x = x.transpose()
            # print 'x',x
            v = (Minv_abs * x).apply_map(floor)
            # print 'v',v
            for i in range(len(exp_bounds)):
                if i in GSenu:
                    exp_bounds[i] = min(v[GSenu.index(i)][0], exp_bounds[i])
            if sum(exp_bounds) < min_exp_bounds:
                new_exponents = exp_bounds
    return new_exponents


def elliptic_curves_with_good_reduction_with_a_rational_Weierstrass_point(K, S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``SK`` : a list of prime ideal of ``K``

    OUTPUT:
        All curves with good reduction outside ``SK`` and at least one rational order 2 point

    EXAMPLE::

        sage:
    """
    import time

    if K == QQ:
        K = NumberField(x - 1, 'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    # we through away the canditate 2-division fields whose relative discriminant does not have even valuation at
    # the primes above 2 which are not in SK

    start = time.time()
    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        quadratic_fields = []
        for M in quadratic_extensions(K, SK + primes_above_2_not_in_SK):
            if len([1 for p in primes_above_2_not_in_SK if M.relative_discriminant().valuation(p) % 2 != 0]) == 0:
                quadratic_fields.append(M)
    else:
        quadratic_fields = quadratic_extensions(K, SK)

    for p in K.primes_above(2):
        if p not in SK:
            SK.append(p)

    # using Hilbert symbol we choose with which fields we are going to work with

    # N = len(C2_extensions)
    A = copy(zero_matrix(ZZ, len(quadratic_fields)))
    B = [0] * len(quadratic_fields)
    D = [K(1)]
    for i in range(len(quadratic_fields)):
        d1 = quadratic_fields[i].defining_polynomial().discriminant()
        D.append(d1)
        for j in range(i, len(quadratic_fields)):
            d2 = quadratic_fields[j].defining_polynomial().discriminant()
            A[i, j] = (K.hilbert_symbol(d1, d2) + 1) / 2
            if A[i, j] == 1:
                if i != j:
                    B[i] += 1
                    B[j] += 1
                else:
                    B[i] += 1

    # The case of two isogenous curves without full 2-torsion

    final_fields = []

    for i in range(len(quadratic_fields)):
        if A[i, i] != 0:
            final_fields.append(quadratic_fields[i])
            D.remove(quadratic_fields[i].defining_polynomial().discriminant())
            for j in range(i, len(quadratic_fields)):
                if A[i, j] == 1:
                    if i != j:
                        B[i] -= 1
                        B[j] -= 1
                        A[i, j] = 0
                    else:
                        B[i] -= 1
                        A[i, i] = 0
            for j in range(i):
                if A[j, i] == 1:
                    if i != j:
                        B[i] -= 1
                        B[j] -= 1
                        A[j, i] = 0
                    else:
                        B[i] -= 1
                        A[i, i] = 0

    # The rest cases

    while not A.is_zero():
        m = max([b for b in B])
        if m != 0:
            maxedges = B.index(m)
            final_fields.append(quadratic_fields[maxedges])
            D.remove(quadratic_fields[maxedges].defining_polynomial().discriminant())
            for j in range(maxedges, len(quadratic_fields)):
                if A[maxedges, j] == 1:
                    if maxedges != j:
                        B[maxedges] -= 1
                        B[j] -= 1
                        A[maxedges, j] = 0
                    else:
                        B[maxedges] -= 1
                        A[maxedges, maxedges] = 0
            for j in range(maxedges):
                if A[j, maxedges] == 1:
                    if maxedges != j:
                        B[maxedges] -= 1
                        B[j] -= 1
                        A[j, maxedges] = 0
                    else:
                        B[maxedges] -= 1
                        A[maxedges, maxedges] = 0

    #we check if we have to solve more S-unit equation

    for d1 in D:
        for d2 in D:
            for d3 in D:
                if (-d1*d2*d3).is_square() and K.hilbert_symbol(d1,d2)==1 and K.hilbert_symbol(d1,d3)==1 and K.hilbert_symbol(d1,d3)==1:
                    if d1 != 1:
                        M = [L for L in quadratic_fields if L.relative_discriminant() == d1][0]
                        if M not in final_fields:
                            final_fields.append(M)
                    if d2 != 1:
                        M = [L for L in quadratic_fields if L.relative_discriminant() == d2][0]
                        if M not in final_fields:
                            final_fields.append(M)
                    if d3 != 1:
                        M = [L for L in quadratic_fields if L.relative_discriminant() == d3][0]
                        if M not in final_fields:
                            final_fields.append(M)

    J = []
    for L in final_fields:
        print 'L',L
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK, SL)
        print 'Gl',len(Gl)-1
        bound = reduce_the_bound(L, Gl, Gm, 200)
        print 'bound',bound
        for l in sieve_in_C2(Gl, Gm, bound):
            j = j_invariant(l)
            if j in K:
                if j not in J:
                    J.append(j)

    J = [K(j) for j in J]
    Jfinal = []
    for j in J:
        if j not in Jfinal:
            Jfinal.append(j)

    if K.absolute_degree() == 1:
        Jfinal = [QQ(j) for j in Jfinal]
        curves = egros_from_jlist_over_K(Jfinal,QQ,[ZZ(p.norm()) for p in S])
    else:
        curves = egros_from_jlist_over_K(Jfinal,K,S)
    curves_final = curves

    for E1 in curves:
        for E in [iso.codomain() for iso in E1.isogenies_prime_degree(2)]:
            if E.torsion_order()%2 == 0:
                if len([1 for E2 in curves_final if E.is_isomorphic(E2)]) == 0:
                    curves_final.append(E)

    return curves_final


##Cubic case


def find_reduce_S_C3(G):
    r"""

    INPUT:
        - ``G`` : a list of generators for a multiplicative group when we work with the `C_3` case.

    OUTPUT:
        A list of prime ideals in the support of ``G`` such that contains two out of the three primes above a prime in
        the base field such that the sum of the valuation of the generators in the third prime is equal to the opposite
        of the sum of the valuations of the generators with respect to the other two primes.

    EXAMPLE::

        sage:
    """
    L = G[0].parent()
    sigma = find_sigma(L)
    S = support_of_G(G, 20)[0]
    reduce_S = []
    while S != []:
        p1 = S[0]
        p2 = sigma(p1)
        p3 = sigma(p2)
        sum1, sum2, sum3 = [sum([g.valuation(p) for g in G]) for p in [p1, p2, p3]]
        if sum1 == sum2:
            reduce_S.append(p1)
        elif sum1 == sum3:
            reduce_S.append(p3)
        else:
            reduce_S.append(p2)
        S.remove(p1)
        S.remove(p2)
        S.remove(p3)
    return reduce_S


def reduce_bound_for_unit_generators_C3(Gl, bounds, R):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group
        - ``bounds`` : a list of upper bounds for each generator
        - ``R`` : a real number such that `\mid\log\mid\mu\mid_{\mathfrak p}\mid\leq\log(R)` for all infinite primes `\mathfrak p`

    OUTPUT:
        A list of upper bounds for each generator such that the bounds are smaller for the generators which are units

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions for `\mathfrak p` be an infinite prime

    EXAMPLE::

        sage:

    """
    L = Gl[0].parent()
    infinite_primes = sum(support_of_G(Gl, 200)[1:], [])
    # print 'bounds',bounds

    # we find which generators are units
    units_index = [i for i, g in enumerate(Gl) if
                   g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i, g in enumerate(Gl) if i in units_index]
    c1_units = c_constants(Glunit, 200)[0]

    # we are going to reduce the bound for units using Smart's ideas
    Bold = max([b for i, b in enumerate(bounds) if i in units_index])

    # we find logRlprime
    logRlprime = max([sum([b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) if is_real_place(
        p) else sum([2 * b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) for p in
                      infinite_primes])

    # we make an arbitrary choice of an initial delta
    delta_old = 1 / R
    delta_new = sqrt(delta_old)

    # we reduce the bounds for the units
    reduce_bounds = bounds
    while True:
        if len([1 for place in infinite_primes if
                trivial_Tp_infinite_place(reduce_bounds[1:], place, Gl[1:], delta_new)]) == len(infinite_primes):
            Bold = min((c1_units * log(delta_new).abs() + c1_units * logRlprime).floor(), Bold)
            # print 'Bold',Bold
            delta_old = delta_new
            delta_new = sqrt(delta_new)
            reduce_bounds = [min(b, Bold) if i in units_index else b for i, b in enumerate(reduce_bounds)]
            # print 'reduce_bounds',reduce_bounds
        else:
            return reduce_bounds, 1 / delta_old ** 2


def reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I, Gl, Gm, bounds):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``bounds`` : a list of upper bounds for each exponent. It is the same for both groups since by construction
        it holds `m_i=\sigma(l_i^{-1})`, where `l_i` and `m_i` are the generators of `Gl` and `Gm` respectively.

    """
    L = Gl[0].parent()
    Sm = support_of_G(Gm, 20)[0]
    sigma = find_sigma(L)

    # print 'bounds',bounds

    # the part of the sieve based on Hilbert symbol

    Q = []
    for p in Sm:
        n = p.residue_field().order()
        if n == 2:
            M = matrix(Integers(n), [[tame_hilbert_symbol(gl, gm, p, n) for gm in Gm] for gl in Gl])
        else:
            M = matrix(Integers(n - 1), [[tame_hilbert_symbol(gl, gm, p, n - 1) for gm in Gm] for gl in Gl])
        Q.append(M)

    lcm_hsymbol = lcm([M.base_ring().order() for M in Q])
    # print 'lcm_hsymbol',lcm_hsymbol

    # the part of the sieve based on unramified prime and Hilbert symbol
    factors = I.factor()
    n = len(factors)
    maxorder = lcm([max((f[0] ** f[1]).idealstar().gens_orders()) for f in factors] + [lcm_hsymbol])

    congruence_bounds = [xrange(bounds[0])] + [xrange(maxorder) if 2 * b >= maxorder else xrange(-b, b + 1) for b in
                                               bounds[1:]]
    Bpr = [0 if 2 * b >= maxorder else 1 for b in bounds[1:]]
    # print 'congruence_bound=%s'%(congruence_bounds)
    count = 0
    elements_l = []
    elements_m = []
    for v in cartesian_product_iterator(congruence_bounds):
        v = vector(v)
        if len([1 for M in Q if (v * M * v).is_zero()]) == len(Q):
            # print 'v-1',v
            l = prod([g ** e for g, e in zip(Gl, v)])
            m = prod([g ** e for g, e in zip(Gm, v)])
            if len([1 for f in factors if (l + m - 1).valuation(f[0]) >= f[1]]) == n:
                # print 'v-2',v
                count += 1
                elements_l.append(l)
                elements_m.append(m)

    Sunits = []
    SmunitL = L.S_unit_group(S=Sm)
    B = [QQ(b / len(c)).floor() + 1 if len(c) != 0 else 1 for b, c in zip(bounds[1:], congruence_bounds[1:])]
    # print 'B',B
    Gl_final = [g ** len(c) if b == 0 else 1 for g, c, b in zip(Gl[1:], congruence_bounds[1:], Bpr)]
    Gm_final = [g ** len(c) if b == 0 else 1 for g, c, b in zip(Gm[1:], congruence_bounds[1:], Bpr)]
    # print 'number of final checks %s'%(count * prod([2*b+1 if br == 0 else 1 for b,br in zip(B,congruence_bounds[1:])]))
    import time
    for v in cartesian_product_iterator([xrange(-b, b) if i == 0 else xrange(1) for b, i in zip(B, Bpr)]):
        start = time.time()
        # print 'v',v
        l0 = prod([g ** e for g, e in zip(Gl_final, v)])
        m0 = prod([g ** e for g, e in zip(Gm_final, v)])
        for l1, m1 in zip(elements_l, elements_m):
            if l0 * l1 + m0 * m1 == 1:
                Sunits.append(l0 * l1)
        end = time.time()
        # print 'time for each loop %s'%(end - start)
        # return 1
    return Sunits


def sieve_for_p_in_support_of_Gl_C3(prime, Gm, Sl, bounds, bound_prime):
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
    sigma_prime = sigma(prime)

    # here we need to make a change of generators such that all the generators have 0 valuation at p
    new_Gm0, new_Gm, k = a_basis_with_0_order_at_p(prime, Gm)
    reduce_bounds = [e for i, e in enumerate(bounds) if i != k]
    new_Gl = [1 / sigma(sigma(mi)) for mi in new_Gm]
    # print 'new_Gl',new_Gl

    exp = 2
    I = prime ** 2
    while I.idealstar().order() == 1:
        exp += 1
        I *= prime

    if exp > bound_prime:
        return [], exp

    Sunits = []
    for m0 in new_Gm0:
        percent = 1
        while 20 * percent >= 1:
            orders = I.idealstar().gens_orders()

            # we create the congruence relations for the exponents with respect to the ideal p**n
            M = matrix(ZZ, len(new_Gm), len(orders), [I.ideallog(g) for g in new_Gm])
            m0log = vector(ZZ, I.ideallog(m0))
            GCD = [gcd(list(col) + [m] + [t]) for col, m, t in zip(M.columns(), orders, m0log)]
            orders = [c / g for c, g in zip(orders, GCD)]
            M = matrix(ZZ, [col / g for col, g in zip(M.columns(), GCD)]).transpose()
            m0log = vector(ZZ, [c / g for c, g in zip(m0log, GCD)])

            maxorder = max(orders)
            # Now we find which elements satisfy the congruence relation
            if k != 0:
                congruence_bounds = [xrange(maxorder)] * len(reduce_bounds[1:])
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) for B in reduce_bounds[1:]]
            else:
                congruence_bounds = [xrange(maxorder)] * len(reduce_bounds)
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) for B in reduce_bounds]

            # We find congruence solutions and we store them
            V = []
            m0_elements = []
            for v in cartesian_product_iterator(congruence_bounds):
                v = vector(v)
                if vector([((v * col) + f) % m for m, f, col in zip(orders, m0log, M.columns())]).is_zero():
                    m0_elements.append(m0 ** f * prod([g ** e for g, e in zip(new_Gm, v)]))
                    V.append(v)
            percent = QQ(len(V)) / QQ(maxorder ** len(congruence_bounds))
            if 20 * percent >= 1:
                exp += 1
                I *= prime

        # we determine the solutions

        new_Gl = [sigma(sigma(1 / g)) for g in new_Gm]
        l0_elements = [sigma(sigma(1 / t)) for t in m0_elements]
        if len(V) != 0:
            new_Gm_powers = [g ** maxorder for g, c, b in new_Gm]
            new_Gl_powers = [sigma(sigma(1 / g)) for g in new_Gm_powers]
            for v in cartesian_product_iterator(D):
                m1 = prod([g ** e for g, e in zip(new_Gm_powers, v)])
                l1 = prod([g ** e for g, e in zip(new_Gl_powers, v)])
                for m0, l0 in zip(m0_elements, l0_elements):
                    if m0 == 1:
                        m = m0 * m1
                        if m0 * m1 not in Sunits:
                            Sunits.append(m)
    return Sunits, exp


def reduce_bound_with_simple_inequalities_C3(Gl, p, bounds, R):
    r"""

    INPUT:
        ``Gl`` : a list of generators
        ``p`` : an infinite prime
        ``bounds`` : a list of upper bounds for the exponents of the generators
        ``R`` : a real number such that `\frac{1}{R}\leq \mid\mu\mid_{p}\leq R` for all infinite primes

    OUTPUT:
        A list of new upper bounds for the generators using simple inequalities

    EXAMPLE::

        sage:
    """
    if is_real_place(p):
        v = [log(p(g).abs()).abs() for g in Gl]
    else:
        v = [2 * log(p(g).abs()).abs() for g in Gl]
    # print 'v',v
    if vector(v).is_zero():
        return bounds
    max_index = v.index(max(v))
    vbar = [c for i, c in enumerate(v) if i != max_index]
    bounds_bar = [b for i, b in enumerate(bounds) if i != max_index]
    # print 'bounds_bar',bounds_bar
    # print 'S',[c*b for c,b in zip(vbar,bounds_bar)]
    S = sum([c * b for c, b in zip(vbar, bounds_bar)])

    # print 'bounds',bounds
    # print 'max_index',max_index
    low_b = QQ(S / v[max_index]).floor()
    # print 'low_b',low_b
    if low_b <= bounds[max_index]:
        for b in range(low_b, bounds[max_index] + 1):
            # print 'b',b
            # print 'v[max_index]*b - S',v[max_index]*b - S
            if v[max_index] * b - S > log(R):
                # print 'b',b
                bounds[max_index] = b
                return bounds
        return bounds
    else:
        return bounds


def sieve_in_C3(Gl, Gm, B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies.
        - ``Gm`` : a list of generators of the group where `\mu` lies.
        - ``B`` : an upper bound for the exponents

    OUTPUT:
        A listof `\lambda` of the solutions of the `S`-unit equation `\lambda +\mu = 1` up to the action of `S_3` whose
        absolute value of the exponents is less than ``B``.

    EXAMPLE::

        sage:


    """
    L = Gl[0].parent()
    Sm = Sl = S = support_of_G(Gl, 30)[0]
    infinite_primes = sum(support_of_G(Gl, 200)[1:], [])
    sigma = find_sigma(L)
    Slreduce = find_reduce_S_C3(Gl)
    # print 'Slreduce=%s'%(Slreduce)

    # we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()] + [B] * (len(Gl) - 1)
    bound_Gm = [Gm[0].multiplicative_order()] + [B] * (len(Gm) - 1)
    print 'bound_Gl-0', bound_Gl

    # for each prime in Slreduce we get a reduced upper bound for the valuation of lambda using Smart's idea

    bound_Slreduce = [0] * len(Slreduce)
    for i, prime in enumerate(Slreduce):
        bound_Slreduce[i] = bound_Slreduce[Slreduce.index(prime)] = reduce_the_bound_for_p_in_support_of_Gl_C2(prime,
                                                                                                               Gm, B)

    bound_Sl = [0] * len(Sl)
    for i, p1 in enumerate(Slreduce):
        p2 = sigma(p1)
        p3 = sigma(p2)
        bound_Sl[Sl.index(p1)] = bound_Sl[Sl.index(p2)] = bound_Sl[Sl.index(p3)] = bound_Slreduce[i]
    bound_Gm = bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    print 'bound_Gl-1', bound_Gl

    # we reduce the bound for the unit generators
    R = max([exp(sum([(log(s(g).abs())).abs() * b for g, b in zip(Gl, bound_Gl) if s(g).abs() != 1])) for s in
             infinite_primes])
    # return reduce_bound_for_unit_generators_C3(Gl,bound_Gl,R)
    bound_Gl, R = reduce_bound_for_unit_generators_C3(Gl, bound_Gl, R)
    print 'bound_Gl-2', bound_Gl
    # print 'Slreduce',Slreduce


    old_bound = copy(bound_Gl)
    # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
            # print '3-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    print 'bound_Gl-3', bound_Gl

    Sunits = []

    # we determine the solutions which are divisible by high powers of primes in Slreduce

    # print 'Slreduce',Slreduce
    for k, p in enumerate(Slreduce):
        # return p,Sl,bound_Gl,bound_Slreduce[k]
        solutions, exp1 = [], 3  # sieve_for_p_in_support_of_Gl_C3(p,Gm,Sl,bound_Gl,bound_Slreduce[k])
        Sunits += solutions
        solutions, exp2 = [], 3  # sieve_for_p_in_support_of_Gl_C3(p,[sigma(g) for g in Gm],Sl,bound_Gl,bound_Slreduce[k])
        Sunits += solutions
        bound_Slreduce[k] = max(exp1, exp2)
    for i, p1 in enumerate(Slreduce):
        p2 = sigma(p1)
        p3 = sigma(p2)
        bound_Sl[Sl.index(p1)] = bound_Sl[Sl.index(p2)] = bound_Sl[Sl.index(p3)] = bound_Slreduce[i]
    bound_Gm = bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    print 'bound_Gl-4', bound_Gl

    # we reduce the bound for the unit generators again
    bound_Gl, R = reduce_bound_for_unit_generators_C3(Gl, bound_Gl, R)
    print 'bound_Gl-5', bound_Gl

    old_bound = copy(bound_Gl)
    # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    #
    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
            # print '3-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    print 'bound_Gl-6', bound_Gl

    # we find the smallest unramified and split prime
    find_prime = False
    p = 2
    while not find_prime:
        for pL in L.primes_above(p):
            if pL not in Sl and not pL.idealstar().is_trivial():
                pK = pL.ideal_below()
                if pK.residue_class_degree() == pL.residue_class_degree():
                    I = L.ideal(pL.ideal_below())
                    find_prime = True
        p = Primes().next(ZZ(p))
    # print 'I',I

    # we do the final sieve using the unramified and split prime we found above and the Hilbert symbol
    for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I, Gl, Gm, bound_Gl):
        if l not in Sunits:
            Sunits.append(l)

    # we throw away 0 and 1

    while 0 in Sunits:
        Sunits.remove(0)
    while 1 in Sunits:
        Sunits.remove(1)

    return Sunits


def elliptic_curves_with_good_reduction_with_cubic_two_division_field(K, S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``SK`` : a list of prime ideal of ``K``

    OUTPUT:
        All curves with good reduction outside ``SK`` and at least one rational order 2 point

    EXAMPLE::

        sage:
    """
    import time

    if K == QQ:
        K = NumberField(x - 1, 'a')
        SK = [K.prime_above(p) for p in S]
        # if 2 not in S:
        #     SK.append(K.prime_above(2))
    else:
        SK = S
        # for p in K.primes_above(2):
        #     if p not in SK:
        #         SK.append(p)

    # we through away the canditate two division fields whose relative discrimiant does not have even valuation at
    # the primes above which are not in SK

    start = time.time()
    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        cubic_fields = []
        for L in cubic_extensions(K, SK + primes_above_2_not_in_SK):
            if len([1 for p in primes_above_2_not_in_SK if L.relative_discriminant().valuation(p) % 2 != 0]) == 0:
                cubic_fields.append(L)
    else:
        cubic_fields = cubic_extensions(K, SK)

    # now we have to add the primes above 2 in SK
    for p in K.primes_above(2):
        if p not in SK:
            SK.append(p)

    end = time.time()
    print 'we have %s fields to work with,' % (len(cubic_fields))
    print 'time for fields = %s' % (end - start)

    J = []
    for L in cubic_fields:
        print 'L=%s' % (L)
        SL = sum([L.primes_above(p) for p in SK], [])
        Gl, Gm = Norm_subgroup_division_field(SK, SL)
        print 'rank of Gl = %s, %s' % (len(Gl) - 1, L.S_unit_group(S=SL).rank())
        start = time.time()
        bound = reduce_the_bound(L, Gl, Gm, 200)
        end = time.time()
        print 'time for reduce bound=%s' % (end - start)
        print 'bound=%s' % (bound)
        start = time.time()
        for l in sieve_in_C3(Gl, Gm, bound):
            j = j_invariant(l)
            if j in K:
                if j not in J:
                    J.append(j)
        end = time.time()
        print 'time for sieve=%s' % (end - start)

    if K.absolute_degree == 1:
        return [QQ(j) for j in J if len(egros_from_j(QQ(j), S)) > 0]
    else:
        return [K(j) for j in J]


##S3 case

def sieve_for_p_in_support_of_Gl_S3(prime, Gm, Sl, bounds, bound_prime, R, Sm, bound_Sm,precision):
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
    sigma_prime = sigma(prime)

    # here we need to make a change of generators such that all the generators have 0 valuation at p
    new_Gm0, new_Gm, k = a_basis_with_0_order_at_p(prime, Gm)
    reduce_bounds = [e for i, e in enumerate(bounds) if i != k]
    new_Gl = [1 / sigma(sigma(mi)) for mi in new_Gm]
    # units_number = len([g for g in new_Gm if g.is_integral() and g.absolute_norm().abs() == 1])

    exp = 1
    I0 = prime
    while I0.idealstar().order() == 1:
        exp += 1
        I0 *= prime

    if exp > bound_prime:
        return [], exp

    exp_m0 = [exp] * len(new_Gm0)
    Sunits = []
    for m0 in new_Gm0:
        print 'm0',m0
        print 'bounds',bounds
        percent = 1
        I = I0
        while 20 * percent >= 1:
            orders = I.idealstar().gens_orders()

            # we create the congruence relations for the exponents with respect to the ideal p**n
            M = matrix(ZZ, len(new_Gm), len(orders), [I.ideallog(g) for g in new_Gm])
            m0log = vector(ZZ, I.ideallog(m0))
            GCD = [gcd(list(col) + [m] + [t]) for col, m, t in zip(M.columns(), orders, m0log)]
            orders = [c / g for c, g in zip(orders, GCD)]
            M = matrix(ZZ, [col / g for col, g in zip(M.columns(), GCD)]).transpose()
            m0log = vector(ZZ, [c / g for c, g in zip(m0log, GCD)])
            maxorder = max(orders)
            print 'maxorder',maxorder

            # Now we find which elements satisfy the congruence relation
            if k != 0:
                congruence_bounds = [xrange(maxorder) if maxorder <= B else xrange(-B,B+1) for B in reduce_bounds[1:]]
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) if maxorder <= B else xrange(0,1) for B in reduce_bounds[1:]]
            else:
                congruence_bounds = [xrange(maxorder) if maxorder <= B else xrange(-B,B+1) for B in reduce_bounds]
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) if maxorder <= B else xrange(0,1) for B in reduce_bounds]

            D_bounds = [len(d)/2 for d in D if len(d) != 1]
            print 'D',D
            print 'D_bounds',D_bounds

            # We find congruence solutions and we store them
            m0_elements = []
            Vcon = []
            for v in cartesian_product_iterator(congruence_bounds):
                v = vector(v)
                if vector([((v * col) + f) % m for m, f, col in zip(orders, m0log, M.columns())]).is_zero():
                    Vcon.append(v)
                    m0_elements.append(m0 * prod([g ** e for g, e in zip(new_Gm, v)]))
            percent = QQ(len(m0_elements)) / QQ(prod([len(b) for b in congruence_bounds]))

            print 'percent', RR(percent) * 100
            print 'len(m0_elements)',len(m0_elements)

            if 20 * percent >= 1:
                exp_m0[new_Gm0.index(m0)] += 1
                I *= prime
        # I am going to use Fincke-Pohst algorithm only for the unit generators and for both Gm and Gl
        if len([1 for d in D if len(d) > 1]) > 0 :
            suppGm = support_of_G(Gm, precision)
            new_Gmk = [g**maxorder for g,d in zip(new_Gm,D) if len(d) != 1]
            Am = zero_matrix(RealField(prec=precision), len(suppGm[1] + suppGm[2]+suppGm[0]), len(new_Gmk))

            i = 0
            for pr in suppGm[1]:
                logm0max = max([log(pr(t).abs()).abs() for t in m0_elements])
                # logm0max = log(pr(m0con).abs()).abs()
                logRm = log(R) + logm0max
                Am[i] = vector([log(pr(mi).abs()) for mi in new_Gmk]) / logRm
                i += 1

            for pr in suppGm[2]:
                logm0max = max([2 * log(pr(t).abs()).abs() for t in m0_elements])
                # logm0max = 2 * log(pr(m0con).abs()).abs()
                logRm = log(R) + logm0max
                Am[i] = vector([2 * log(pr(mi).abs()) for mi in new_Gmk]) / logRm
                i += 1

            for pr in suppGm[0]:
                logm0max = max([log(t.abs_non_arch(pr,prec = precision)).abs() for t in m0_elements])
                p = pr.absolute_norm().factor()[0][0]
                fpr = pr.residue_class_degree()
                logRm = bound_Sm[Sm.index(pr)] * fpr * log(p) + logm0max
                Am[i] = vector([log(mi.abs_non_arch(pr,prec = precision)) for mi in new_Gmk]) / logRm
                i += 1

            if log(det(Am.transpose() * Am).abs()) < -30:
                Q = Am.transpose() * Am
                f = len(suppGm[1] + suppGm[2]+suppGm[0])
                V1 = []
                for v in cartesian_product_iterator([xrange(-d,d+1) for d in D_bounds]):
                    v = vector(v)
                    if v*Q*v <= f:
                        V1.append(v)
            else:
                V1 = pari(Am.transpose() * Am).qfminim(len(suppGm[1] + suppGm[2]+suppGm[0]), flag=2).python()[2].columns()
            Vfinal = []

            for v in V1:
                if  len([1 for a,b in zip(D_bounds,v) if b.abs() > a]) == 0:
                    Vfinal.append(v)
                    Vfinal.append(-v)
        else:
            V1 = []
            Vfinal = []

        print 'len(V1)',len(V1)
        print 'len(Vfinal)',len(Vfinal)
        print 'number of cases before Q',len(m0_elements) * prod([len(d)+1 for d in D])
        print 'number of cases after  Q',len(m0_elements) * len(Vfinal)

        SmQ = []
        for q in Sm:
            p = q.absolute_norm().factor()[0][0]
            if p not in SmQ:
                SmQ.append(p)

        import time
        if len(m0_elements) != 0:
            M1 = [prod([ g ** e for g, e in zip(new_Gmk, v)]) for v in Vfinal]+[L(1)]
            print 'number of cases ', len(M1) * len(m0_elements)
            for  m0 in m0_elements:
                startm1 = time.time()
                for m1 in M1:
                    # startm0 = time.time()
                    a0 = QQ(sum((m0*m1).absolute_minpoly().list()))
                    if QQ(a0.prime_to_S_part(SmQ).abs()) == 1:
                        if is_S_unit_element(SunitL,1-m0 * m1):
                            Sunits.append(m0 * m1)
                endm1 = time.time()
                # print 'time for each m1',endm1 - startm1

    return Sunits, min(exp_m0)


def reduce_bound_for_unit_generators_S3(Gl, Gm, bounds, R):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``Gm`` : a list of generators of the group where `\mu` lies
        - ``bounds`` : a list of upper bounds for each generator
        - ``R`` : a real number such that `\mid\log\mid\mu\mid_{\mathfrak p}\mid\leq\log(R)` for all infinite primes `\mathfrak p`

    OUTPUT:
        A list of upper bounds for each generator such that the bounds are smaller for the generators which are units

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions for `\mathfrak p` be an infinite prime

    EXAMPLE::

        sage:

    """
    L = Gl[0].parent()
    infinite_primes_Gl = sum(support_of_G(Gl, 200)[1:], [])
    infinite_primes_Gm = sum(support_of_G(Gm, 200)[1:], [])
    length_infinite_primes = len(infinite_primes_Gl+infinite_primes_Gm)
    infinite_primes = [p for p in infinite_primes_Gl if p in infinite_primes_Gm]

    # we find which generators are units
    units_index = [i for i, g in enumerate(Gl) if
                   g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i, g in enumerate(Gl) if i in units_index]

    if len(Glunit) == 0:
        return bounds, R
    c1_units = c_constants(Glunit, 200)[0]

    # we are going to reduce the bound for units using Smart's ideas
    Bold = max([bounds[b] for b in units_index])

    # we find logRlprime
    c2inf = max([sum([b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) if is_real_place(
        p) else sum([2 * b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) for p in
                      infinite_primes])

    # we make an arbitrary choice of an initial delta
    delta_old = 1 / R
    delta_new = sqrt(delta_old)

    # we reduce the bounds for the units
    reduce_bounds = bounds
    while True:
        sm1 = len([1 for place in infinite_primes_Gm if
                  trivial_Tp_infinite_place(reduce_bounds[1:], place, Gm[1:], delta_new)])
        sm2 = len([1 for place in infinite_primes_Gl if is_real_place(place) and delta_new < 0.5])
        sl1 = len([1 for place in infinite_primes_Gl if
                  trivial_Tp_infinite_place(reduce_bounds[1:], place, Gl[1:], delta_new)])
        sl2 = len([1 for place in infinite_primes_Gm if is_real_place(place) and delta_new < 0.5])

        if sm1+sm2 == length_infinite_primes and sl1+sl2 == length_infinite_primes:
            Bold = min((c1_units * log(delta_new).abs() + c1_units * c2inf).floor(), Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_new)
            reduce_bounds = [min(b, Bold) if i in units_index else b for i, b in enumerate(reduce_bounds)]
        else:
            return reduce_bounds, 1 / delta_old ** 2


def sieve_in_S3(Gl, Gm, B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies.
        - ``Gm`` : a list of generators of the group where `\mu` lies.
        - ``B`` : an upper bound for the exponents

    OUTPUT:
        A listof `\lambda` of the solutions of the `S`-unit equation `\lambda +\mu = 1` up to the action of `S_3` whose
        absolute value of the exponents is less than ``B``.

    EXAMPLE::

        sage:


    """
    L = Gl[0].parent()
    Sl, real_infinite_primes_Sl, complex_infinte_primes_Sl = support_of_G(Gl, 200)
    Sm, real_infinite_primes_Sm, complex_infinte_primes_Sm = support_of_G(Gm, 200)
    infinite_primes = [p for p in real_infinite_primes_Sl + complex_infinte_primes_Sl if
                       p in real_infinite_primes_Sm + complex_infinte_primes_Sm]
    sigma = find_sigma(L)
    # tau = find_tau(L)

    # when we have only one generator of the free part
    if len(Gl) == 2:
        Sunits = []
        find_prime = False
        p = 2
        while not find_prime:
            for pL in L.primes_above(p):
                if pL not in Sl and pL not in Sm and not pL.idealstar().is_trivial():
                    pK = pL.ideal_below()
                    if pK.residue_class_degree() == pL.residue_class_degree():
                        I = L.ideal(pL.ideal_below())
                        find_prime = True
            p = Primes().next(ZZ(p))

        # we do the final sieve using the unramified and split prime we found above and the Hilbert symbol
        for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I, Gl, Gm, [
            L.primitive_root_of_unity().multiplicative_order()] + [B]):
            if l not in Sunits:
                Sunits.append(l)

        return Sunits

    # we have gp6 primes
    for p in Sl:
        if len(L.primes_above(p.ideal_below().ideal_below())) == 6:
            raise ValueError('There exists a prime with 6 primes!')

    # gp3 and gp6 mean the primes which have 3 and 6 congugate primes respectively

    SlnotSm_gp3 = []
    for p in Sl:
        p_below = p.ideal_below().ideal_below()
        if len(L.primes_above(p_below)) == 3:
            if p not in Sm:
                SlnotSm_gp3.append(p)

    # we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()] + [B] * (len(Gl) - 1)
    bound_Sl = [0] * len(Sl)
    bound_Sm = [0] * len(Sm)
    print 'bound Gl-0', bound_Gl

    # for each prime in SlnotSm_gp3 we get a reduced upper bound for the valuation of lambda using Smart's idea

    for prime in SlnotSm_gp3:
        e = reduce_the_bound_for_p_in_support_of_Gl_C2(prime, Gm, B)
        bound_Sl[Sl.index(prime)] = e
        if sigma(prime) in Sl:
            bound_Sl[Sl.index(sigma(prime))] = e
        else:
            bound_Sl[Sl.index(sigma(sigma(prime)))] = e

    for prime in SlnotSm_gp3:
        bound_Sm[Sm.index(sigma(prime))] = bound_Sm[Sm.index(sigma(sigma(prime)))] = bound_Sl[Sl.index(prime)]

    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    print 'bound_Gl-1', bound_Gl

    # we reduce the bound for the unit generators
    R = max([exp(sum([(2 * log(s(g).abs())).abs() * b for g, b in zip(Gl, bound_Gl) if s(g).abs() != 1])) for s in
             infinite_primes])

    bound_Gl, R = reduce_bound_for_unit_generators_S3(Gl, Gm, bound_Gl, R)
    print 'bound_Gl-2', bound_Gl

    # we reduce the bound using simple inequalities

    old_bound = copy(bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)

    print 'bound_Gl-3', bound_Gl
    print 'bound_Sl', bound_Sl
    return 1
    Sunits = []

    # we determine the solutions which are divisible by high powers of primes in SlnotSm_gp3

    for k, p in enumerate(SlnotSm_gp3):
        # return p, Sl, bound_Gl, bound_Sl[Sl.index(p)], R, Sm, bound_Sm
        # prime, Gm, Sl, bounds, bound_prime, R, Sm, bound_Sm, precision

        # if p.absolute_norm()%2 == 0:
        #     solutions = []
        #     e = 4
        # else:
        #     # return p, Sl, bound_Gl, bound_Sl[Sl.index(p)], R, Sm, bound_Sm
        #     solutions = []
        #     e = 2
        solutions, e = sieve_for_p_in_support_of_Gl_S3(p, Gm, Sl, bound_Gl, bound_Sl[Sl.index(p)],R,Sm,bound_Sm, 400)
        # print 'prime = %s, exponent = %s'%(p,e)

        Sunits += solutions
        bound_Sl[Sl.index(p)] = e
        if sigma(p) in Sl:
            bound_Sl[Sl.index(sigma(p))] = e
        else:
            bound_Sl[Sl.index(sigma(sigma(p)))] = e
        # again we get new bounds for the exponents by the new bounds we have to the primes
        # bound_Gl,R = reduce_bound_for_unit_generators_S3(Gl, Gm, bound_Gl, R)
        bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
        print 'bound_Gl-4', bound_Gl

    # we reduce the bound for the unit generators again
    # return bound_Gl,R
    bound_Gl, R = reduce_bound_for_unit_generators_S3(Gl, Gm, bound_Gl, R)
    print 'bound_Gl-5', bound_Gl

    # we reduce the bound using simple inequalities again

    old_bound = copy(bound_Gl)
    # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
            # print '3-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    print 'bound_Gl-6', bound_Gl

    # we find the smallest unramified and split prime
    find_prime = False
    p = 2
    while not find_prime:
        for pL in L.primes_above(p):
            if pL not in Sl and pL not in Sm and not pL.idealstar().is_trivial():
                pK = pL.ideal_below()
                if pK.residue_class_degree() == pL.residue_class_degree():
                    I = L.ideal(pL.ideal_below())
                    find_prime = True
        p = Primes().next(ZZ(p))

    # we do the final sieve using the unramified and split prime we found above and the Hilbert symbol

    for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I, Gl, Gm, bound_Gl):
        if l not in Sunits:
            Sunits.append(l)

    # we throw away 0 and 1

    while L(0) in Sunits:
        Sunits.remove(L(0))
    while L(1) in Sunits:
        Sunits.remove(L(1))

    return Sunits+[L(-1)]


def elliptic_curves_with_good_reduction_with_S3_two_division_field(K, S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``SK`` : a list of prime ideal of ``K``

    OUTPUT:
        All curves with good reduction outside ``SK`` and at least one rational order 2 point

    EXAMPLE::

        sage:
    """
    import time

    if K == QQ:
        K = NumberField(x - 1, 'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    # we through away the canditate two division fields whose relative discrimiant does not have even valuation at
    # the primes above which are not in SK

    start = time.time()

    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        S3_fields = []
        quadratic_subfields = []
        cubic_polynomials = []
        T = s3_extensions(K, SK + primes_above_2_not_in_SK)
        for f, L, M in zip(T[0], T[1], T[2]):
            K_abs_degree = K.absolute_degree()
            dM = M.relative_discriminant()
            L1 = K.extension(f, 'l1')
            dL1 = L1.relative_discriminant()
            t = dM ** 3 * dL1 ** 2

            if len([1 for p in primes_above_2_not_in_SK if (t.valuation(p) - 3 * dM.valuation(p)) % 4 != 0]) == 0:
                S3_fields.append(L)
                quadratic_subfields.append(M)
                cubic_polynomials.append(f)
    else:
        cubic_polynomials, S3_fields, quadratic_subfields = s3_extensions(K, SK)

    # now we have to add the primes above 2 in SK
    for p in primes_above_2_not_in_SK:
        SK = [p] + SK

    end = time.time()
    print 'We have %s fields to work with' % (len(S3_fields))
    print 'time for fields = %s' % (end - start)

    J = []
    i = 1
    for f, L in zip(cubic_polynomials, S3_fields):
        print 'L=%s' % (L)
        print 'M', L.base_field()
        SL = sum([L.primes_above(p) for p in SK], [])
        Gl, Gm = Norm_subgroup_division_field(SK, SL)
        print 'rank of Gl = %s' % (len(Gl) - 1)
        print 'rank of S-unit group = %s' % (L.S_unit_group(S=SL).rank())
        start = time.time()
        bound = 5#reduce_the_bound(L, Gl, Gm, 200)
        end = time.time()
        # return bound
        print 'time for reduce bound=%s' % (end - start)
        print 'bound=%s' % (bound)
        start = time.time()
        for l in sieve_in_S3(Gl, Gm, bound):
            j = j_invariant(l)
            if j in K:
                if j not in J:
                    J.append(j)
        end = time.time()
        print 'time for sieve=%s' % (end - start)
    from sage.schemes.elliptic_curves.ell_egros import (egros_from_jlist, egros_from_j, egros_get_j)

    while 0 in J:
        J.remove(0)
    while 1728 in J:
        J.remove(1728)

    if K.absolute_degree == 1:
        return [QQ(j) for j in J if len(egros_from_j(QQ(j), S)) > 0]
    else:
        return [K(j) for j in J]





##Non trivial Tp set using Smart's ideas

def non_trivial_Tp_finite_case(G, prime, bounds, delta, S):
    r"""

    INPUT:
        - ``G`` : a list of generators
        - ``prime`` : a prime ideal of ``K``
        - ``bounds``` : a list of positive integers which are the bounds of the exponents for ``G``
        - ``delta`` : a real number less than `1`

    OUTPUT:

        All the solutions of the inequality `|g-1|_{\mathcal{p}}<\delta` where `g` lies in ``G`` such that
        they are `S`-units

    EXAMPLE::

        sage:
    """

    new_G0, new_G, k = a_basis_with_0_order_at_p(prime, G)
    new_bounds = [b for i, b in enumerate(bounds) if i != k]

    precision = 20
    supp = support_of_G(new_G, precision)
    s = len(supp[0]) + len(supp[1]) + len(supp[2])

    primeR = [exp(sum([b * log(g.abs_non_arch(p, precision)).abs() for b, g in zip(new_bounds, new_G)])) for p in
              supp[0]]
    realR = [exp(sum([b * log(place(g).abs()).abs() for b, g in zip(new_bounds, new_G)])) for place in supp[1]]
    complexR = [exp(sum([2 * b * log(place(g).abs()).abs() for b, g in zip(new_bounds, new_G)])) for place in supp[2]]

    A = copy(zero_matrix(RealField(prec=precision), s, len(new_G)))

    i = 0
    for r, p in zip(primeR, supp[0]):
        A[i] = [log(g.abs_non_arch(p, precision)) / log(r) for g in new_G]
        i += 1
    for r, place in zip(realR, supp[1]):
        A[i] = [log(place(g).abs()) / log(r) for g in new_G]
        i += 1
    for r, place in zip(complexR, supp[2]):
        A[i] = [2 * log(place(g).abs()) / log(r) for g in new_G]
        i += 1
    Q = A.transpose() * A

    for m0 in new_G0:
        y = copy(zero_vector(RealField(prec=precision), s))
        i = 0
        for r, p in zip(primeR, supp[0]):
            y[i] = log(m0.abs_non_arch(p, precision)) / log(r)
            i += 1
        for r, place in zip(realR, supp[1]):
            y[i] = log(place(m0).abs()) / log(r)
            i += 1
        for r, place in zip(complexR, supp[2]):
            A[i] = 2 * log(place(m0).abs()) / log(r)
            i += 1
        y = -y

        Q = pari(A.transpose() * A)
        # List = Q.qfminim(pari(sqrt(s)),flag = 2)

    return List
