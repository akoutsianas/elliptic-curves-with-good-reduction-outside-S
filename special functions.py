def base_norm_condition(K,L,SK,SL):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``L`` : a finite extension of ``K``
        - ``SK`` : a list of primes ideals of ``K``
        - ``SL`` : a list with all prime ideals of ``L`` above the primes in ``SK``
        
    OUTPUT:
        - ``gens`` : a list with the generators of the kernel of the map `L(SL,2)\xrightarrow{Norm}K(SK,2)`
        - ``kernel`` : the kernel of the map as a free module
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: SK = sum([K.primes_above(p) for p in [2,3]],[])
        sage: L.<b> = K.extension(x^2-5)
        sage: SL = sum([L.primes_above(p) for p in SK],[])
        sage: base_norm_condition(K,L,SK,SL)
            ([-1, -1/2*b + 3/2], Free module of degree 4 and rank 2 over Integer Ring
             Echelon basis matrix:
             [1 0 0 0]
             [0 2 0 0])
        
        sage: K.<a> = NumberField(x^2-6)
        sage: SK = sum([K.primes_above(p) for p in [2,3]],[])
        sage: L.<b> = K.extension(x^2-5)
        sage: SL = sum([L.primes_above(p) for p in SK],[])
        sage: base_norm_condition(K,L,SK,SL)
            ([-1, 1/2*b + 3/2, b - a], Free module of degree 6 and rank 3 over Integer Ring
             Echelon basis matrix:
             [1 0 0 0 0 0]
             [0 2 0 0 0 0]
             [0 0 1 0 0 0])
    """

    SunitK = K.S_unit_group(S=SK)
    SunitL = L.S_unit_group(S=SL)
    n = len(SunitL.gens())

    M = copy(zero_matrix(ZZ,len(SunitL.gens()),len(SunitK.gens())))
    g0K = SunitK.torsion_generator().value()
    g0L = SunitL.torsion_generator().value()

    for i,g in enumerate(SunitL.gens_values()):
        M[i] = SunitK(g.norm(K)).list()
    N = copy(zero_matrix(ZZ,1,len(SunitK.gens())))
    if L.relative_degree() == 2:
        N[0,0] = g0K.multiplicative_order()
    else:
        N[0,0] = g0K.multiplicative_order()/2

    A = block_matrix([[M],[N]])
    kernel = A.left_kernel()

    v = copy(zero_matrix(ZZ,1,n))
    v[0,0] = 1
    module = block_matrix([[kernel.matrix()[:,:n]],[v]]).row_module()
    gens = [SunitL.exp(g) for g in module.matrix()]

    return gens,module


def extend_basis_over_ZZ(T):
    r"""

    INPUT:
        - ``T`` : a matrix with integer coefficients such that the rows are less than the columns

    OUTPUT:
        A square matrix whose first columns is the matrix ``T`` and it is invertible if it is able to be done.

    EXAMPLE::

        sage:
    """
    D, U, V = T.smith_form()
    m,n = D.dimensions()
    if prod(D.diagonal()) == 1:
        Dprime = block_matrix([[zero_matrix(ZZ,n-m,m),identity_matrix(ZZ,n-m)]])
        Tprime, Uprime, Vprime = Dprime.smith_form()
        if Uprime.is_one():
            Tprime = Dprime*V.inverse()
            return block_matrix([[T],[Tprime]])
        else:
            T
    else:
        return T


def Norm_subgroup_division_field(SK,SL):
    r"""
    
    INPUT:
        - ``SK`` : a list of prime ideals of a number field `K`
        - ``SL`` : a list of all prime ideals of a number field `L` such that `Ga\ell(L/K)` is isomorphic to a subgroup of `S_3`
    
    OUTPUT:
        - ``lambda_subgroup`` : a list of generators of the subroup of `S_L`-unit group where `\lambda` lies
        - ``mu_subgroup`` : a list of generators of the subroup of `S_L`-unit group where `\mu` lies
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: SK = sum([K.primes_above(p) for p in [2,5,7]],[])
        sage: L.<a> = NumberField(x^6 + 84*x^4 + 994*x^3 + 21609*x^2 + 2058*x + 266854)
        sage: SL = sum([L.primes_above(p) for p in [2,5,7]],[])
        sage: Norm_subgroup_division_field(SK,SL)
            ([29/1190700*a^5 - 7/24300*a^4 + 323/170100*a^3 + 541/170100*a^2 + 242/1215*a - 69973/12150,
            4/297675*a^5 + 1/17010*a^4 + 47/85050*a^3 + 659/42525*a^2 + 1862/6075*a + 2057/6075,
            -11/2381400*a^5 - 1/68040*a^4 - 89/340200*a^3 + 629/340200*a^2 - 821/6075*a - 10739/24300,
            -263/1488375*a^5 + 43/30375*a^4 - 493/42525*a^3 - 15751/212625*a^2 - 66976/30375*a + 990833/30375],
            [-1/198450*a^5 + 1/5670*a^4 - 79/28350*a^3 + 859/28350*a^2 - 154/2025*a + 536/2025,
            19/850500*a^5 - 17/850500*a^4 - 11/121500*a^3 + 6647/121500*a^2 - 1783/30375*a + 8867/12150,
            -59/496125*a^5 + 1/23625*a^4 + 11/2835*a^3 - 23323/70875*a^2 + 268/1125*a - 41561/10125,
            -1/79380*a^5 - 1/18900*a^4 - 61/56700*a^3 - 661/56700*a^2 - 389/1350*a - 4633/4050])
    """
    K = SK[0].ring()
    L = SL[0].ring()
    relative_degree = L.absolute_degree()/K.absolute_degree()

    if relative_degree == 2:

        lambda_group = base_norm_condition(K,L,SK,SL)[0]
        SunitL = L.S_unit_group(S = SL)
        number_of_units_gens = len([1 for g in SunitL.gens_values() if g.is_integral() and g.absolute_norm().abs() == 1])

        #We want to make a basis that contains unit generators
        Gens = matrix(ZZ,[SunitL(g).list() for g in lambda_group])
        T = Gens[:,number_of_units_gens:].left_kernel().matrix()
        Tprime = extend_basis_over_ZZ(T)
        if Tprime != T:
            Gens = Tprime * Gens
        # print 'Gens-2',Gens

        lambda_group = [SunitL.exp(v) for v in Gens.rows()]

        mu_group = SunitL.gens_values()
        
        return lambda_group,mu_group
    elif relative_degree == 3:
        lambda_group = base_norm_condition(K,L,SK,SL)[0]
        sigma = find_sigma(L)

        mu_group = [sigma(g**(-1)) for g in lambda_group]
        
        return lambda_group,mu_group
    elif relative_degree == 6:
        SunitL = L.S_unit_group(S = SL)
        number_of_units_gens = len([1 for g in SunitL.gens_values() if g.is_integral() and g.absolute_norm().abs() == 1])
        sigma = find_sigma(L)
        K_abs_degree = K.absolute_degree()
        
        #M is the unique quadratic extension of K which is a subfield of L
        M = L.base_field()#[T[0] for T in L.subfields(2*K_abs_degree) if len(K.embeddings(T[0])) > 0][0]

        #we find 2 out of the 3 subfield of L with index 2 which contain K
        index_2_subfields = L.subfields(3*K_abs_degree)

        find = False
        i = 0
        while not find:
            if len(K.embeddings(index_2_subfields[i][0])) != 0:
                L1 = index_2_subfields[i][0]
                find = True
            i += 1

        #we find all the primes above SK in L1, L2 and M
        SM = sum([M.primes_above(p) for p in SK],[]) 
        SL1 = sum([L1.primes_above(p) for p in SK],[])
        # SL2 = sum([L2.primes_above(p) for p in SK],[])

        #the subgroups where lambda and mu lie with respect to L1, L2 and M
        GM = base_norm_condition(M,L,SM,SL)
        GL1 = base_norm_condition(L1,L,SL1,SL)

        # print 'GM',GM
        # print 'GL1',GL1
        A = block_matrix(ZZ,[[GM[1].matrix()],[-GL1[1].matrix()]])#,[matrix(v)]])
        B = A.left_kernel().matrix()
        gens = [r[:GM[1].rank()] * GM[1].matrix() for r in B.rows()[:B.dimensions()[0]]]
        Gens = matrix(ZZ,gens)

        #I want to see if I can find a basis that has gennerators which lie in the unit group
        # print 'Gens',Gens
        T = Gens[:,number_of_units_gens:].left_kernel().matrix()
        Tprime = extend_basis_over_ZZ(T)
        if Tprime != T:
            Gens = Tprime * Gens
        # print 'Gens-2',Gens

        lambda_group = [SunitL.exp(v) for v in Gens.rows()]
        return lambda_group, [sigma(g**(-1)) for g in lambda_group]