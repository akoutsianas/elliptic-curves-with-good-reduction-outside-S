def reduce_boundsC2(K,Gl,Gm,precision):

    B = reduce_the_bound(K,Gl,Gm,precision)
    if Gl == [] or Gm == []:
        raise ValueError('Either Gl or Gm is empty')

    L = Gl[0].parent()
    tau = find_tau(L)
    Sl = support_of_G(Gl,40)[0]
    Sm = support_of_G(Gm,40)[0]
    SmnotSl = [p for p in Sm if p not in Sl]
    infinite_primes = L.places(prec = 200)

    #we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()]+[B]*(len(Gl)-1)
    bound_Gm = [Gm[0].multiplicative_order()]+[B]*(len(Gm)-1)

    # print 'bound_Gl-0',bound_Gl
    # print 'bound_Gm-0',bound_Gm

    Sunits = []
    Smunit_group = L.S_unit_group(S=Sm)

    if len(Gl) <= 2:
        return bound_Gl,bound_Gm

    # print 'bound_Gl-1',bound_Gl
    # print 'bound_Gm-1',bound_Gm

    #we pick only one of the two split primes
    Slreduce = []
    for p in Sl:
        if (not p in Slreduce) and not (tau(p) in Slreduce):
            Slreduce.append(p)

    #for each prime in Slreduce we get a reduced upper bound for the valuation of lambda using Smart's idea

    bound_Slreduce = []
    for p in Slreduce:
        bound_Slreduce.append(reduce_the_bound_for_p_in_support_of_Gl_C2(p,Gm,B))

    # we get new upper bounds for the exponents

    bound_Sm = [0]*len(Sm)
    for i,p in enumerate(Sm):
        if p in Slreduce:
            bound_Sm[i] = bound_Slreduce[Slreduce.index(p)]
        elif tau(p) in Slreduce:
            bound_Sm[i] = bound_Slreduce[Slreduce.index(tau(p))]
        else:
            bound_Sm[i] = sum([g.valuation(p).abs() * b for g,b in zip(Gm,bound_Gm)])

    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl,Slreduce,bound_Slreduce,bound_Gl)
    bound_Gm = bounds_for_exponents_from_bounds_for_primes(Gm,Sm,bound_Sm,bound_Gm)

    # print 'bound_Gl-2',bound_Gl
    # print 'bound_Gm-2',bound_Gm

    R = max([exp(sum([(log(s(g).abs())).abs() * b if is_real_place(s) else (2*log(s(g).abs())).abs() * b for g,b in zip(Gl,bound_Gl)])) for s in infinite_primes])

    bound_Gl , R = reduce_bound_for_unit_generators_C2(Gl,Gm,bound_Gl,bound_Gm,R)

    # print 'bound_Gl-3',bound_Gl
    # print 'bound_Gm-3',bound_Gm

    #we use triangle inequality to reduce the bound

    old_bound = copy(bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl,p,bound_Gl,R)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl,p,bound_Gl,R)

    # print 'bound_Gl-4',bound_Gl
    # print 'bound_Gm-4',bound_Gm

    return bound_Gl,bound_Gm

def boundsC2():

    import time

    K = QQ
    o = open('Desktop/results.txt','w')
    # o = open('resultsfermat.txt','w')
    o.write('C2 - case \n\n')
    o.close()
    P = Primes()
    pr = Integer(61)
    if K == QQ:
        K = NumberField(x-1,'a')
    while pr <= 100:
        S = [2,3,pr]
        if K.absolute_degree() == 1:
            SK = [K.prime_above(p) for p in S]
        else:
            SK = S

        o = open('Desktop/results.txt','a')
        o.write('S = %s\n\n'%(str(S)))
        o.close()

        #we through away the canditate 2-division fields whose relative discrimiant does not have even valuation at
        #the primes above which are not in SK

        primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
        if len(primes_above_2_not_in_SK) > 0:
            quadratic_fields = []
            for M in quadratic_extensions(K,SK+primes_above_2_not_in_SK):
                if len([1 for p in primes_above_2_not_in_SK if M.relative_discriminant().valuation(p) % 2 != 0])  == 0:
                    quadratic_fields.append(M)
        else:
            quadratic_fields = quadratic_extensions(K,SK)

        for p in K.primes_above(2):
            if p not in SK:
                SK.append(p)

        C2_extensions = []
        for M in quadratic_fields:
            SM = sum([M.primes_above(p) for p in SK],[])
            Gl,Gm = Norm_subgroup_division_field(SK,SM)
            C2_extensions.append([M,Gl,Gm])

        # we determine which S-unit equations we have to solve

        N = len(C2_extensions)
        A = copy(zero_matrix(ZZ,N))
        B = [0]*N
        for i in range(N):
            d1 = C2_extensions[i][0].defining_polynomial().discriminant()
            for j in range(i,N):
                d2 = C2_extensions[j][0].defining_polynomial().discriminant()
                A[i,j] = (K.hilbert_symbol(d1,d2)+1)/2
                if A[i,j] == 1:
                    if i != j:
                        B[i] += 1
                        B[j] += 1
                    else:
                        B[i] += 1
        J = []
        #The case when they may exist two isogenous curves with the same 2-division field

        for i in range(N):
            if A[i,i] != 0:
                M,Gl,Gm = C2_extensions[i]
                print('M = ',M.defining_polynomial())
                start = time.time()
                bounds = reduce_boundsC2(M,Gl,Gm,200)
                end = time.time()
                sec = RR(end - start)
                print('Gl = ',Gl)
                print('Gm = ',Gm)
                o = open('Desktop/results.txt','a')
                o.write('field = %s, time = %ss, Bl = %s, Bm = %s\n'%(M.defining_polynomial(),str(sec.floor()),str(bounds[0]),str(bounds[1])))
                o.write('Gl = %s\n'%(Gl))
                o.write('Gm = %s\n\n'%(Gm))
                o.close()

                for j in range(i,N):
                    if A[i,j] == 1:
                        if i != j:
                            B[i] -= 1
                            B[j] -= 1
                            A[i,j] = 0
                        else:
                            B[i] -= 1
                            A[i,i] = 0
                for j in range(i):
                    if A[j,i] == 1:
                        if i != j:
                            B[i] -= 1
                            B[j] -= 1
                            A[j,i] = 0
                        else:
                            B[i] -= 1
                            A[i,i] = 0

        #The rest cases

        while not A.is_zero():
            m = max([b for b in B])
            if m != 0:
                maxedges = B.index(m)

                #Here we evaluate the curves with respect to C2_extensions[maxedges]

                M,Gl,Gm = C2_extensions[maxedges]
                print('M = ',M.defining_polynomial())
                start = time.time()
                bounds = reduce_boundsC2(M,Gl,Gm,200)
                end = time.time()
                sec = RR(end-start)
                print('Gl = ',Gl)
                print('Gm = ',Gm)
                o = open('Desktop/results.txt','a')
                o.write('field = %s, time = %ss, Bl = %s, Bm = %s\n'%(M.defining_polynomial(),str(sec.floor()),str(bounds[0]),str(bounds[1])))
                o.write('Gl = %s\n'%(Gl))
                o.write('Gm = %s\n\n'%(Gm))
                o.close()

                for j in range(maxedges,N):
                    if A[maxedges,j] == 1:
                        if maxedges != j:
                            B[maxedges] -= 1
                            B[j] -= 1
                            A[maxedges,j] = 0
                        else:
                            B[maxedges] -= 1
                            A[maxedges,maxedges] = 0
                for j in range(maxedges):
                    if A[j,maxedges] == 1:
                        if maxedges != j:
                            B[maxedges] -= 1
                            B[j] -= 1
                            A[j,maxedges] = 0
                        else:
                            B[maxedges] -= 1
                            A[maxedges,maxedges] = 0

        pr = P.next(pr)
        o = open('Desktop/results.txt','a')
        o.write('\n\n\n')
        o.close()
    return 0


# def boundsC3():

