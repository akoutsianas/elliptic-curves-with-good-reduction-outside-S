from sage.schemes.elliptic_curves.ell_egros import (egros_from_jlist, egros_from_j, egros_get_j)

def nice_exposition_of_j(J):

    J = [QQ(j) for j in J]
    print

    for j in J:
        if j.denominator() != 1:
            print('\\frac{%s}{%s},'%(j.numerator(),j.denominator())),
        else:
            print('%s,'%(j)),

def find_field_of_j(j,L):
    y = polygen(L)
    f = (y**2-y+1)**3-j/2**8*(y**2*(y-1)**2)
    if len(f.roots())>0:
        return True
    else:
        return False


def test(j,L,Gl,Gm):
    # L = QQ
    y = polygen(L)
    # j = L(j)
    print 'j',j
    f = (y**2-y+1)**3-j/2**8*(y**2*(y-1)**2)
    # # N = f.splitting_field('a')

    # if len(f.roots()) > 0:
    #     return True
    # else:
    #     return False
    # J = []
    for r in f.roots():
        l = r[0]
        if is_in_G(r[0],Gl):
            if is_in_G(r[0],Gl) and is_in_G(1-r[0],Gm):
                print 'coordinates',list_in_G(r[0],Gl)
                return r[0]
                # print L.ideal(r[0]).factor()

                # if list_in_G(r[0],Gl)[3].abs()>3:
                #     return True
                # else:
                #     return False



def test1(P,B1,G1):
    import time
    K = P[0].ring()
    print K
    G1c1 ,G1c2, G1c3 = c_constants(G1[1:],200)
    SunitK = K.S_unit_group(S = support_of_G(P[2],10)[0])
    B_place = 0
    prec = 200
    start = time.time()
    M_logp = [sum([c * log_p(g,P[0],prec) for c,g in zip(SunitK(m).list(),SunitK.gens_values()) if c != 0]) for m in P[2]]
    M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
    end = time.time()
    print 'time for initial logp',end-start
    for m0 in P[1]:
        print 'm0'
        Bold_m0 = B1
        finish = False
        while not finish:
            Bnew_m0,increase_precision = reduction_step_finite_case(P[0],Bold_m0,P[2],M_logp,m0,G1c3,prec)

            #if we have to increase the precision we evaluate c1,c2,c3 constants again
            if not increase_precision:
                if Bnew_m0 < Bold_m0:
                    Bold_m0 = Bnew_m0
                else:
                    finish = True
            else:
                #we evaluate with higher precision G1c1, G1c2 and G1c3
                print 'increase precision'
                prec *= 2
                G1c1 ,G1c2, G1c3 = c_constants(G1[1:],prec)
                start = time.time()
                M_logp = [sum([c * log_p(g,P[0],prec) for c,g in zip(SunitK(m).list(),SunitK.gens_values()) if c != 0]) for m in P[2]]
                M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
                end = time.time()
                print 'time for increase logp',end-start
        B_place = max(B_place,Bold_m0)

def testC1(S):

    Sunits = solve_S_unit_equation(S)
    J = [QQ(0),QQ(1728)]
    for l in Sunits:
        if j_invariant(l) not in J:
            J.append(j_invariant(l))
    Jfinal = []
    curves = []
    for j in J:
        if len(egros_from_j(j,S)) > 0:
            curves += egros_from_j(j,S)
            Jfinal.append(j)
    return Jfinal,curves

def testC2():
    import time
    C = CremonaDatabase()
    o = open('Desktop/results.txt','w')
    # o = open('resultsfermat.txt','w')
    o.write('C2 - case \n\n')
    o.close()
    P = Primes()
    p = Integer(23)
    data = []
    while p <= 23:
    # for p in [Integer(89)]:
        S = [2,3,p]
    #     print 'p',p

        #We compare with Cremona's database
        # N = [2**i * 3**j * p**k for i,j,k in cartesian_product_iterator([xrange(9),xrange(3),xrange(3)])]
        # N = [p**i for i in range(9)]

        # ED = C.list(N)

        # EC21 = [e for e in ED if not e.two_division_polynomial().is_irreducible()]
        # EC2 = [E for E in EC21 if len(E.two_division_polynomial().factor()) == 2]

        # JC2 = []
        # for E in EC2:
        #     if E.j_invariant() not in JC2:
        #         JC2.append(E.j_invariant())
        #
        Jdata = []
        # for E in EC21:
        #     if E.j_invariant() not in Jdata:
        #         Jdata.append(E.j_invariant())

        # print 'Jdata',Jdata
        M = NumberField(x**2-x-1,'a')
        S = M.primes_above(31)
        print 'S',S
        start = time.time()
        J = elliptic_curves_with_good_reduction_with_a_rational_Weierstrass_point(M,S)
        end = time.time()
        t = RR(end - start)
        min = (t/60).floor()
        sec = (t-min*60).floor()
        S = M.primes_above(31)
        if min != 0:
            o = open('Desktop/results.txt','a')
            # o = open('resultsfermat.txt','a')
            o.write('f = %s, S = %s, time %smin %ss\n'%(M.defining_polynomial(),str(S),str(min),str(sec)))
            o.write('J = %s\n'%(str(J)))

            JdatanotJ = []
            for j in Jdata:
                if j not in J:
                    JdatanotJ.append(j)
            if JdatanotJ != []:
                o.write('We miss this %s j-invariants.\n'%(str(JdatanotJ)))
            else:
                o.write('We get all j-invariants.\n')

            JnotJdata = []
            for j in J:
                if j not in Jdata:
                    JnotJdata.append(j)
            if JnotJdata != []:
                o.write('We get this more %s j-invariants.\n'%(str(JnotJdata)))
        else:
            o = open('Desktop/results.txt','a')
            # o = open('resultsfermat.txt','a')
            o.write('f = %s, S = %s, time %ss\n'%(M.defining_polynomial(),str(S),str(sec)))
            o.write('J = %s\n'%(str(J)))

            JdatanotJ = []
            for j in Jdata:
                if j not in J:
                    JdatanotJ.append(j)
            if JdatanotJ != []:
                o.write('We miss this %s j-invariants.\n'%(str(JdatanotJ)))
            else:
                o.write('We get all j-invariants.\n')

            JnotJdata = []
            for j in J:
                if j not in Jdata:
                    JnotJdata.append(j)
            if JnotJdata != []:
                o.write('We get this more %s j-invariants.\n'%(str(JnotJdata)))
        o.write('\n')
        o.close()
        p = P.next(p)
    # o.close()
    return 1


def testC3():
    import time
    C = CremonaDatabase()
    o = open('Desktop/results.txt','w')
    # o = open('resultsfermat.txt','w')
    o.write('C3 - case \n\n')
    o.close()
    P = Primes()
    p = Integer(31)
    data = []
    while p <= p:
    # for p in [Integer(89)]:
    #     S = [3,p]
    #     print 'p',p

        #We compare with Cremona's database
        # N = [3**j * p**k for j,k in cartesian_product_iterator([xrange(6),xrange(3)])]
        # N = [p**i for i in range(9)]

        # ED = C.list(N)
        #
        # EC3S3 = [e for e in ED if e.two_division_polynomial().is_irreducible()]
        # EC3 = [E for E in EC3S3 if E.two_division_polynomial().discriminant().is_square()]
        Jdata = []
        # for E in EC3:
        #     if E.j_invariant() not in Jdata:
        #         Jdata.append(E.j_invariant())

        M = NumberField(x**2- x - 1,'a')
        S = M.primes_above(p)
        print 'S',S
        start = time.time()
        J = elliptic_curves_with_good_reduction_with_cubic_two_division_field(M,S)
        end = time.time()
        t = RR(end - start)
        min = (t/60).floor()
        sec = (t-min*60).floor()
        S = M.primes_above(p)
        if min != 0:
            o = open('Desktop/results.txt','a')
            # o = open('resultsfermat.txt','a')
            o.write('f = %s, S = %s, time %smin %ss\n'%(M.defining_polynomial(),str(S),str(min),str(sec)))
            o.write('J = %s\n'%(str(J)))

            JdatanotJ = []
            for j in Jdata:
                if j not in J:
                    JdatanotJ.append(j)
            if JdatanotJ != []:
                o.write('We miss this %s j-invariants.\n'%(str(JdatanotJ)))
            else:
                o.write('We get all j-invariants.\n')

            JnotJdata = []
            for j in J:
                if j not in Jdata:
                    JnotJdata.append(j)
            if JnotJdata != []:
                o.write('We get this more %s j-invariants.\n'%(str(JnotJdata)))
        else:
            o = open('Desktop/results.txt','a')
            # o = open('resultsfermat.txt','a')
            o.write('f = %s, S = %s, time %ss\n'%(M.defining_polynomial(),str(S),str(sec)))
            o.write('J = %s\n'%(str(J)))

            JdatanotJ = []
            for j in Jdata:
                if j not in J:
                    JdatanotJ.append(j)
            if JdatanotJ != []:
                o.write('We miss this %s j-invariants.\n'%(str(JdatanotJ)))
            else:
                o.write('We get all j-invariants.\n')

            JnotJdata = []
            for j in J:
                if j not in Jdata:
                    JnotJdata.append(j)
            if JnotJdata != []:
                o.write('We get this more %s j-invariants.\n'%(str(JnotJdata)))
        o.write('\n')
        o.close()
        p = P.next(p)
    # o.close()
    return 1


def testS3():
    import time
    C = CremonaDatabase()
    o = open('Desktop/results.txt','w')
    # o = open('resultsfermat.txt','w')
    o.write('S3 - case \n\n')
    o.close()
    P = Primes()
    p = Integer(31)
    data = []
    while p <= 31:
        Jdata = []
        M = NumberField(x**2-x-1,'a')
        S = M.primes_above(p)
        start = time.time()
        J = elliptic_curves_with_good_reduction_with_S3_two_division_field(M,S)
        end = time.time()
        t = RR(end - start)
        min = (t/60).floor()
        sec = (t-min*60).floor()
        S = M.primes_above(p)
        if min != 0:
            o = open('Desktop/results.txt','a')
            # o = open('resultsfermat.txt','a')
            o.write('S = %s, time %smin %ss\n'%(str(S),str(min),str(sec)))
            o.write('J = %s\n'%(str(J)))

            JdatanotJ = []
            for j in Jdata:
                if j not in J:
                    JdatanotJ.append(j)
            if JdatanotJ != []:
                o.write('We miss this %s j-invariants.\n'%(str(JdatanotJ)))
            else:
                o.write('We get all j-invariants.\n')

            JnotJdata = []
            for j in J:
                if j not in Jdata:
                    JnotJdata.append(j)
            if JnotJdata != []:
                o.write('We get this more %s j-invariants.\n'%(str(JnotJdata)))
        else:
            o = open('Desktop/results.txt','a')
            # o = open('resultsfermat.txt','a')
            o.write('S = %s, time %ss\n'%(str(S),str(sec)))
            o.write('J = %s\n'%(str(J)))

            JdatanotJ = []
            for j in Jdata:
                if j not in J:
                    JdatanotJ.append(j)
            if JdatanotJ != []:
                o.write('We miss this %s j-invariants.\n'%(str(JdatanotJ)))
            else:
                o.write('We get all j-invariants.\n')

            JnotJdata = []
            for j in J:
                if j not in Jdata:
                    JnotJdata.append(j)
            if JnotJdata != []:
                o.write('We get this more %s j-invariants.\n'%(str(JnotJdata)))
        o.write('\n')
        o.close()
        p = P.next(p)
    # o.close()
    return 1

def DeWeger_theorem_for_test(S):
    r"""

    OUTPUT:
        ``S`` - 
    """


def speed_S3_sieve(Gl,Gm):

    L = Gl[0].parent()
    Sl, real_infinite_primes_Sl, complex_infinte_primes_Sl = support_of_G(Gl,200)
    Sm, real_infinite_primes_Sm, complex_infinte_primes_Sm = support_of_G(Gm,200)
    infinite_primes = [p for p in real_infinite_primes_Sl+complex_infinte_primes_Sl if p in real_infinite_primes_Sm+complex_infinte_primes_Sm]
    sigma = find_sigma(L)

    #gp3 and gp6 mean the primes which have 3 and 6 congugate primes respectively

    SlnotSm_gp3 = []
    for p in Sl:
        p_below = p.ideal_below().ideal_below()
        if len(L.primes_above(p_below)) == 3:
            if p not in Sm:
                SlnotSm_gp3.append(p)

    bound_Gl = [2, 122, 71, 44]
    bound_Sl = [39,39]
    Sunits = []

    #we determine the solutions which are divisible by high powers of primes in SlnotSm_gp3

    for k,p in enumerate(SlnotSm_gp3):
        solutions,i = sieve_for_p_in_support_of_Gl_C3(p,Gm,Sl,bound_Gl,bound_Sl[Sl.index(p)])

        Sunits += solutions
        bound_Sl[Sl.index(p)] = i
        if sigma(p) in Sl:
            bound_Sl[Sl.index(sigma(p))] = i
        else:
            bound_Sl[Sl.index(sigma(sigma(p)))] = i
        #again we get new bounds for the exponents by the new bounds we have to the primes
        bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl,Sl,bound_Sl,bound_Gl)
        print 'bound_Gl-4',bound_Gl

    #we reduce the bound for the unit generators again
    bound_Gl , R = reduce_bound_for_unit_generators_S3(Gl,Gm,bound_Gl,R)
    print 'bound_Gl-5',bound_Gl

    #we reduce the bound using simple inequalities again

    old_bound = copy(bound_Gl)
    # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm,p,bound_Gl,R)
    # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm,p,bound_Gl,R)
        # print '3-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    print 'bound_Gl-6',bound_Gl

    #we find the smallest unramified and split prime
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

    #we do the final sieve using the unramified and split prime we found above and the Hilbert symbol

    for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I,Gl,Gm,bound_Gl):
        if l not in Sunits:
            Sunits.append(l)

    #we throw away 0 and 1

    while L(0) in Sunits:
        Sunits.remove(L(0))
    while L(1) in Sunits:
        Sunits.remove(L(1))

    return Sunits

# 17 Orlescote Road, CV4 7BG, Coventry - Ros address
