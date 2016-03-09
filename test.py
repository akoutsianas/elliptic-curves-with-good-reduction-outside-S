from sage.schemes.elliptic_curves.ell_egros import (egros_from_jlist, egros_from_j, egros_get_j)

def test(j):
    # L = QQ
    y = polygen(QQ)
    # j = L(j)
    print 'j',j
    f = (y**2-y+1)**3-j/2**8*(y**2*(y-1)**2)
    # N = f.splitting_field('a')
    f = f.change_ring(L)
    for r in f.roots():
        print 'i',is_in_G(r[0],Gl)
        if is_in_G(r[0],Gl):
            if is_in_G(r[0],Gl) and is_in_G(1-r[0],Gm):
                print list_in_G(r[0],Gl),list_in_G(1-r[0],Gm)
        #         print (r[0]).valuation(prime)
        #         return r[0]
    #                 return r[0]#[SunitL(r[0]) for r in f.roots()][0].value()
    return N

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
    p = Integer(31)
    data = []
    while p <= 31:
    # for p in [Integer(89)]:
    #     S = [2,3,p]
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
    # for p in [Integer(89)]:
    #     S = [2,p]
    #     print 'p',p
    #
    #     We compare with Cremona's database
    #     N = [2**i * p**k for i,k in cartesian_product_iterator([xrange(9),xrange(6)])]
        # N = [p**i for i in range(9)]

        # ED = C.list(N)

        # EC3S3 = [e for e in ED if e.two_division_polynomial().is_irreducible()]
        #
        # ES3 = [E for E in EC3S3 if not E.two_division_polynomial().discriminant().is_square()]
        Jdata = []
        # for E in ES3:
        #     if E.j_invariant() not in Jdata:
        #         Jdata.append(E.j_invariant())

        # print 'Jdata',Jdata
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


def test3(J):
    J_L = []
    for j in J:
        y = polygen(QQ)
        f = (y**2-y+1)**3-j/2**8*(y**2*(y-1)**2)
        H = f.splitting_field('s')
        if len(H.embeddings(L)) == 6 and j not in J_L:
            J_L.append(j)
    return J_L


def test4(vectors,G,infinite_primes,R):
    precision = infinite_primes[0].codomain().precision()
    A = matrix(RealField(prec = precision),[[log(s(g).abs()) if is_real_place(s) else 2*log(s(g).abs()) for g in G] for s in infinite_primes])
    A /= log(R)
    # print 'A',A
    n = len(infinite_primes)
    count = 0
    for v in vectors:
        x = A*v
        if x.norm()**2 <= 2*n:
            count += 1
    return count,A

def speedtest():

    import time
    start = time.time()
    for i in range(10**8):
        if i%432 ==0:
            print i
    end = time.time()
    print 'time',end-start

# 17 Orlescote Road, CV4 7BG, Coventry - Ros address
