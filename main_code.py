##### Code over QQ #####

def initial_bound(S):
    r"""
    
    INPUT:
        - ``S`` : a finite set of prime numbers
    
    OUTPUT:
        A big upper bound for the absolute value of the exponents of the solutions of the `S`-unit equation `x \pm y=1`. It is based on the theorem 6.1 of the reference.
        
    REFERENCE:
        B.M.M.De Weger. Algorithms For Diophantine Equations. PhD thesis, University of Leiden, 1988.
        
    EXAMPLE::
        
        sage: S = [2,7,11]
        sage: initial_bound(S).n(21)
            4.09901e19
    """
    
    C1t = [768523,476217,373024,318871,284931,261379,2770008]
    s = len(S)
    t1 = (2 * s)/3
    t = QQ(t1).floor()
    P = prod(S)
    Q = []
    for q in S:
        m = q * (q-1)
        find = False
        qi = Integer(3)
        while not find:
            if qi.divides(m):
                qi = Primes().next(qi)
            else:
                find = True
        Q.append(qi)
    q = max(Q)
    if t < 8:
        a1 = (56 * e)/15
    else:
        a1 = (8 * e)/3
    if t >= 8:
        c = C1t[6]
    else:
        c = C1t[t-2]
        
    m = max([((q-1) * (2+1/(q-1))**t)/((log(q))**(t+2)) for q in S])
    U = c*(a1**t)*(t**((t+5)/2))*(q**(2*t))*(q-1)*((log(t*q))**2)*m*(log(S[s-1])**t)*(log(4*log(S[s-1]))+log(S[s-1])/(8*t))
    C1 = U/(6 * t)
    C2 = U * log(4)
    Omega = 1
    for i in range(s-t,s):
        Vi = 1
        Vs_1 = 1
        Vs = 1
        if Vi < log(S[i]):
            Vi = log(S[i])
        if i == s-2:
            Vs_1 = Vi
        if i == s-1:
            Vs = Vi
        Omega = Omega * Vi
    C3 = 2**(9 * t + 26) * t**(t + 4) * Omega * log(e * Vs_1)
    C4 = 7.4
    a = (C1 * log(P/S[0]) + C3)/log(S[0])
    if a > C4:
        C4 = a
    C5 = (C2 * log(P/S[0])+C3 * log(e * Vs)+0.327)/log(S[0])
    C6 = C5
    a = (C2 * log(P/S[0]) + log(2))/log(S[0])
    if a > C6:
        C6 = a
    C7 = 2 * (C6 + C4 * log(C4))
    C8 = S[s-1]
    if C8 < log(2 * (P/S[0])**S[s-1])/log(S[0]):
        C8 = log(2 * (P/S[0])**S[s-1])/log(S[0])
    if C8 < C2 + C1 * log(C7):
        C8 = C2+C1*log(C7)
    if C8 < C7:
        C8 = C7
    return C8


def primitive_p_1_root_mod_pn(p,n):
    r"""
    
    INPUT:
        - ``p`` : a prime number
        - ``n`` : a natural number
        
    OUTPUT:
        A primitive (p-1)-th root of unity `\mod p^n` if there exists and 1 otherwise.
    
    EXAMPLE::
        
        sage: primitive_p_1_root_mod_pn(5,1)
            2
        sage: primitive_p_1_root_mod_pn(11,3)
            596
    """
    if p == 2 and n > 2:
        return mod(1,p^n)
    ap = mod(primitive_root(p),p**n)
    for i in range(n-1):
        ap = ap**p
    
    return ap
    
    
def change_basis(v):
    r"""
    
    INPUT:
        - ``v`` : a list of integer numbers
        
    OUTPUT:
        If `v=[v_1,...,v_n]`, `gcd(v)=g` and `g=l_1v_1+\cdots +l_nv_n` then the function gives you a matrix in `\mathbb Z` which is invertible and its last row is `[l_1,\cdots,l_n]`
    
    EXAMPLE::
        
        sage: v = [2,11,4]
        sage: change_basis(v)
            [-11   2   0]
            [ 20  -4   1]
            [ -5   1   0]
    """   
    n = len(v)
    v = matrix(v)
    D,U,V = v.smith_form();
    V = V.transpose()
    t = V[0]
    V[0] = V[n-1]
    V[n-1] = t  
    
    return V


def p_adic_approximation_of_a_homogenous_lattice(theta,p,m):
    r"""
    
    INPUT:
        - ``theta`` : a list of `p`-adic numbers as they are defined in section 6.3 page 121 of the reference
        - ``p`` : a prime number
        - ``m`` : the precision of the approximation
    
    OUTPUT:
        - The matrix `B_{\mu}` in the page 68 of the reference
        - A copy of ``theta`` such that the last element has the minimal valuation.
        - the position of the element in ``theta`` that has the minimal valuation and was permuted with the last element of the theta.
    
    REFERENCE:
        B.M.M.De Weger. Algorithms For Diophantine Equations. PhD thesis, University of Leiden, 1988.
        
    EXAMPLE::
        
        sage: R = Qp(5,20,'capped-rel','series')
        sage:theta = [R(-6),R(7),R(14)]
        sage: p_adic_approximation_of_a_homogenous_lattice(theta,5,5)
            [
            [   1    0    0]                                                        

            [   0    1    0]                                                        

            [1044  522 3125], [4 + 2*5 + O(5^20), 2 + 5 + O(5^20), 4 + 3*5 + 4*5^2 +
            4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + 4*5^9 + 4*5^10 + 4*5^11
            + 4*5^12 + 4*5^13 + 4*5^14 + 4*5^15 + 4*5^16 + 4*5^17 + 4*5^18 + 4*5^19
            + O(5^20)],

            0
            ]
    """
    n = len(theta)

    #we are going to find the theta_i with the smallest valuation
    
    ord = min([t.valuation() for t in theta])
    position = [i for i in range(n) if theta[i].valuation() == ord][0]
    
    #we replace theta[n-1] with theta[position] s.t. the theta_i with minimal valuation to be last one
    
    a = theta[position]
    theta[position] = theta[n-1]
    theta[n-1] = a
    
    #Since now that the last element of the theta[] has the minimal valuation we are going to create the matix
    #Bm as it is described to De Weger's thesis page 68
    
    Bm = copy(identity_matrix(n))
    Bm[n-1] = [mod(((-1) * t)/a,p**m) for t in theta]
    Bm[n-1,n-1] = p**m
    
    return Bm,theta,position
    
   
def a_base_for_Gm_star(B,A,p,m,m0):
    r"""
    
    INPUT:
        - ``B`` : the matrix whose columns generate the lattice `\Gamma_{\mu}` as it is defined in page 68 of the reference
        - ``A`` : a list `[a_1,..,a_n]` such that `x=\prod a_i^{x_i}` where `a_i\in Q_p` and `v_p(a_i)=0`
        - ``p`` : a prime number
        - ``m`` : the precision of the lattice
        - ``m0``: the minimal order of `\log_p(a_i)` for `i=1,\cdots , n`
    
    OUTPUT:
        A matrix such that its columns generate the lattice `\Gamma_{\mu}` as in page 72 of the reference when `p>3`
    
    COMMENT:
        It should hold `v_p(\log_p(a_n))` has to be minimal
        
    REFERENCE:
        B.M.M.De Weger. Algorithms For Diophantine Equations. PhD thesis, University of Leiden, 1988.
    """
    
    n = len(A)
    zeta = primitive_p_1_root_mod_pn(p,m+m0)
    xi = [prod([A[j]**B[j,i] for j in range(n)]) for i in range(n)]
    
    #xi has the values of the products Π ai^xi with x=bi
    #kbi has the values of the exponents k(bi)
    #zeta_powers contains the powers of zeta 
    
    zeta_powers=[mod(zeta**i,p**(m+m0)) for i in range(p-1)]
    
    kbi = [min([k for k in range(p-1) if (mod(xi[i],p**(m+m0))-zeta_powers[k]) == 0]) for i in range(n)]

    
    V = change_basis(kbi)    #V is the matrix which change the basis of Gamma from the basis b to the basis b'
    B2 = B * (V.inverse())   #B2 is now the matrix of the Gamma lattice with respect to the basis b'
    kbi = matrix(kbi).transpose()
    kbi = V*kbi              #kbi is containing the exponents of the new basis b'
    B2 = B2.transpose()
    
    
    #we find bi* for i = 1 up to n-1 
    #Bstar is transpose matrix of the matrix that response to a basis for the Gm* sub-lattice of Gm.
     
    Bstar = matrix(ZZ,n)
    for i in range(n-1):
        a = mod(kbi[i][0] / kbi[n-1][0],(p-1)/2)
        gstar = a.centerlift()
        Bstar[i] = B2[i]-gstar * B2[n-1]
    
    
    #we find bn*
    gstar = lcm(kbi[n-1][0],(p-1)/2)/kbi[n-1][0]
    Bstar[n-1] = gstar * B2[n-1]
     
    return Bstar.transpose()


def reducing_the_bound(X0,A,p,m):
    r"""
    
    INPUT:
        - ``X0`` : a big upper bound for the exponents
        - ``A`` : a list `[a_1,..,a_n]` such that `x=\prod a_i^x_i` where `a_i\in Q_p` and `v_p(a_i)=0`
        - ``p`` : a prime number
        - ``m`` : the precision of the lattice
        
    OUTPUT:
        - An new upper bound with respect to the prime ``p``
        - A boolean variable that is True when the condition of lemma 3.14 page 68 of the reference holds
        
    REFERENCE:
        B.M.M.De Weger. Algorithms For Diophantine Equations. PhD thesis, University of Leiden, 1988.    
    """    
    n = len(A)
    A_log = [a.log() for a in A]
    Bm = p_adic_approximation_of_a_homogenous_lattice(A_log,p,m)
    A_log = Bm[1]
 
    pos = Bm[2]
    a = A[pos]
    A[pos] = A[n-1]
    A[n-1] = a
    m0 = A_log[n-1].valuation()
    
    if p > 3:       #if p>3 we find a matrix for Gm* lattice. Otherwise Gm=Gm*
        Bmstar = a_base_for_Gm_star(Bm[0],A,p,m,m0)
    else:
        Bmstar = Bm[0]
    
    Bmstar = Bmstar.transpose()                 #We have to take the transpose of the matrix because of the 
                                                #LLL() function
    C = Bmstar.LLL()                            #assume that the rows of the matrix generate the lattice
    e = copy(zero_vector(ZZ,n))
    e[0] = 1
    v =e * C
    vnorm=v.norm()**2
    if 2**(1-n) * vnorm > n * X0**2:
        increase_m = False
        X0 = (m-1+m0)
    else:
        increase_m = True
        
    
    return [X0,increase_m]


def find_the_new_bound_for_all_primes(X0,A,precision):
    r"""
    
    INPUT:
        - ``X0`` : an upper bound for all the primes
        - ``A`` :a list of primes
        - ``precision`` : the precision we have 
        
    OUTPUT:
        A list with upper bounds for the exponents of each prime in ``A``.
    
    EXAMPLE::
        
        sage: find_the_new_bound_for_all_primes(1000,[2,3,5],100)
            [24, 15, 10]
            
        sage: find_the_new_bound_for_all_primes(10000,[2,3,5,7,11,13],250)
            [85, 53, 37, 29, 24, 22]            
    """
    n = len(A)
    B = [1] * n
    for i in range(n):       #for its prime in A we are going to find a new bound
        p = A[i]
        K = Qp(p, prec = precision, type = 'capped-rel', print_mode = 'series')
        e = [K(a) for a in A if a != p]         #e = a vector with the primes different to p as Qp elements
        m = (2 * log(X0)/log(p)).round()
        newbound = True
        while newbound:
            T = reducing_the_bound(X0,e,p,m)
            newbound = T[1]
            m = m+1
            if m > K.precision_cap():
                # Sieve
                #if m is bigger than the precision we have, we have to increase it an evaluate all the p-adic numbers 
                
                K = Qp(p, prec = 2 * K.precision_cap(), type = 'capped-rel', print_mode = 'series')
                e = [K(A[j]) for j in range(n) if i != j]
        B[i] = T[0]
        
    return B
    
    
def applying_De_Weger_method(A,precision):
    r"""
    
    INPUT:
        - ``A`` : a list of prime numbers
        - ``precision`` : a precision for the `p`-adic numbers
        
    OUTPUT:
        An upper bound of the exponents of the primes in ``A``.
    
    EXAMPLE::
        
        sage: 
    """    
    X0 = initial_bound(A)
    Xnew = max(find_the_new_bound_for_all_primes(X0,A,precision))
    while Xnew < X0:
        X0 = Xnew
        M = find_the_new_bound_for_all_primes(Xnew,A,precision);
        Xnew = max(M)    
    return Xnew   


def simple_loop(S,B):
    r"""
    
    INPUT:
        - ``S`` : a list of primes
        - ``B`` : a natural number
        
    OUTPUT:
        All the `x` of the pairs of the solutions of the `S`-unit equation `x+y=1` such that the absolute values of the exponents of `x,y` are smaller than ``B``
    
    COMMENT:
        Here we use the fact that it holds either `v_p(x)=v_p(y)<0` or `v_p(x)>0,v_p(y)=0` or `v_p(x)=0,v_p(y)>0` for all `p\in S`.
               
    EXAMPLE::
        
        sage: simple_loop([2,3,5],12)
            [1/16, 15/16, -15, 16, 1/4, 3/4, -3, 4, 1/6, 5/6, -5, 6, 1/10, 9/10, -9,
            10, 1/2, 1/2, -1, 2, 1/81, 80/81, -80, 81, 1/9, 8/9, -8, 9, 1/3, 2/3,
            -2, 3, 1/25, 24/25, -24, 25, 1/5, 4/5, -4, 5]
    """  
    solutions = []     
    for v in cartesian_product_iterator([xrange(-B,B+1)] * len(S)):
        #for each candidate x we store the potential y in T
        T = [1]
        x = 1
        for pr,exp in zip(S,v):
            x = x * pr**exp
            temp = []
            for y in T:
                if exp < 0:
                    y = y * pr**exp
                    temp = temp + [y]
                elif exp == 0:
                    for j in range(B+1):
                        temp = temp + [y * pr**j]
            T = temp
        for y in T:
            if x + y == 1:
                solutions.extend([x,y,-y/x,1/x])
    return solutions


def solve_S_unit_equation_over_Q(S):
    r"""
    
    INPUT:
        - ``S`` : a list of primes
    
    OUTPUT:
        All the `x` of the pairs of the solutions of the `S`-unit equation `x+y=1`
        
    COMMENT:
        ``S`` should have at least two elements
        
    EXAMPLE::
        
        sage: solve_S_unit_equation_over_Q([2,3])
            [1/4, 3/4, -3, 4, 1/2, 1/2, -1, 2, 1/9, 8/9, -8, 9, 1/3, 2/3, -2, 3]
            
        sage: solve_S_unit_equation_over_Q([2,3,5])
            [1/16, 15/16, -15, 16, 1/4, 3/4, -3, 4, 1/6, 5/6, -5, 6, 1/10, 9/10, -9,
            10, 1/2, 1/2, -1, 2, 1/81, 80/81, -80, 81, 1/9, 8/9, -8, 9, 1/3, 2/3,
            -2, 3, 1/25, 24/25, -24, 25, 1/5, 4/5, -4, 5]
            
        sage: solve_S_unit_equation_over_Q([3,5])
            []
            
        sage: solve_S_unit_equation_over_Q([2,3,7])
            [1/64, 63/64, -63, 64, 1/8, 7/8, -7, 8, 1/28, 27/28, -27, 28, 1/4, 3/4,
            -3, 4, 1/2, 1/2, -1, 2, 1/9, 8/9, -8, 9, 1/3, 2/3, -2, 3, 1/49, 48/49,
            -48, 49, 1/7, 6/7, -6, 7]
            
    """
    if len(S) < 2:
        raise ValueError('S should have at least two primes')
    S.sort()
    if len([p for p in S if p not in Primes()]) > 0:
        raise ValueError('S contains a composite number')
    
    #we find an upper bound
    B = applying_De_Weger_method(S,150)
       
    return simple_loop(S,B)
    

def tame_hilbert_symbol_over_QQ(a,b,p,n):
    r"""
    
    INPUT:
        - ``a`` : an integer
        - ``b`` : an integer
        - ``p`` : a prime ideal
        - ``n`` : a natural number
        
    OUTPUT:
        The exponent of the general Hilbert symbol `\left(\frac{,}{p}\right):\mathbb Q_p/\mathbb Q_p^{*n}\times\mathbb Q_p/\mathbb Q_p^{*n}\rightarrow\mu_n` when `n\mid p-1` or `n=2` for `p=2`.
    
    EXAMPLE::
        
        sage: tame_hilbert_symbol_over_QQ(3,7,7,6)
            5
        
        sage: tame_hilbert_symbol_over_QQ(3,7,5,2)
            0
    """
    if a == 0 or b == 0:
        raise ValueError('Either a or b is equal to 0')
    if p == 2 and n != 2:
        raise ValueError('p=2 but n is different from 2')
    if p == 2 and n == 2:
        if hilbert_symbol(a,b,p) == -1:
            return 1
        else:
            return 0
    if (p-1) % n !=0 :
        raise ValueError('n does not divide p-1')
        
    l = a.valuation(p)
    m = b.valuation(p)
    t = (p-1)/n
    w = (-1)**(l*m) * b**l/a**m
    GF = FiniteField(p)
    
    return (GF(w)**t).log()


def tame_hilbert_symbol(a,b,prime,n):
    r"""
    
    INPUT:
        - ``a`` : a nonzero element of number field `K`
        - ``b`` : a nonzero element of number field `K`
        - ``prime`` : a prime ideal
        - ``n`` : a natural number
        
    OUTPUT:
        The exponent of the general Hilbert symbol `\left(\frac{,}{p}\right):K_{\mathcal p}/K_{\mathcal p}^{*n}\times K_{\mathcal p}/K_{\mathcal p}^{*n}\rightarrow\mu_n` when `n\mid q-1` or `n=2` for `p=2`, where `q` is the order of the residue field of `\mathcal p`.
    
    EXAMPLE::
        
        sage: K.<i> = QuadraticField(-1)
        sage: p1 = K.prime_above(3)
        sage: tame_hilbert_symbol(3,3,p1,8)
            4
            
        sage: tame_hilbert_symbol(3,7,7,6)
            5
    """
    if prime in QQ:
        return tame_hilbert_symbol_over_QQ(a,b,prime,n)
    K = prime.number_field()
    p = prime.absolute_norm().factor()[0][0]
    GF = prime.residue_field()
    q = GF.cardinality()
    if a.is_zero() or b.is_zero():
        raise ValueError('Either a or b is equal to 0')
    if n == 2:
        if pari(K).nfhilbert(a, b, prime.pari_prime()) == -1:
            return 1
        else:
            return 0
    if (q-1) % n != 0:
        raise ValueError('n does not divide p-1')
        
    l = K(a).valuation(prime)
    m = K(b).valuation(prime)
    t = (q-1)/n
    w = (-1)**(l*m) * b**l/a**m

    return (GF(w)**t).log(GF.primitive_element())
    

def LegendreEllipticCurve(l):
    r"""
    
    INPUT:
        - ``l`` : an element of a ring
        
    OUTPUT:
        The associate to ``l`` elliptic curve in the Legendre form
    
    """
    if l ==0 or l == 1:
        raise ValueError('l is equal to 1 or 0')
    
    return EllipticCurve([0,-l-1,0,l,0])

    
def sieve_with_hilbert_symbol_over_QQ(S,B):
    r"""
    
    INPUT:
        - ``S`` : a finite set of primes
        - ``B`` : a natural number
        
    OUTPUT:
        All the `x` of the pairs of the solutions of the `S`-unit equation `x+y=1` such that the absolute values of the exponents of `x,y` are smaller than ``B``. We use general Hilbert symbol for the sieve.
    
    EXAMPLE::
        
        sage: 
    """
    A = copy(zero_matrix(ZZ,len(S),2 * len(S)))
    for k,p in enumerate(S):
        v = copy(A[k])
        for i,p1 in enumerate(S):
            for j,p2 in enumerate(S):
                if p == 2:
                    if general_hilbert_symbol(p1,p2,p,2) == -1:
                        v[i] += 1
                        v[len(S) + j] += 1
                else:
                    v[i] += general_hilbert_symbol(p1,p2,p,p-1).log()
                    v[len(S)+j] += general_hilbert_symbol(p1,p2,p,p-1).log()
                A[k] = v
      
    #N = [0] * len(S)
    #for i,p in enumerate(S):
    #    if p == 2:
    #        N[i] = 2
    #    else:
    #        N[i] = p-1
    #print N
    #g = lcm([p-1 for p in S if p != 2])
   # 
    #T = []
    #for v in cartesian_product_iterator([xrange(g)] * 2 * len(S)):
    #    v = vector(v)
    #    t = A * v
    #    #print 'v,t,[]',v,t,[1 for s,n in zip(t,N) if t%n != 0]
    #    if not (len([1 for s,n in zip(t,N) if t%n != 0]) > 0):
    #        T.append(v)
    #print 'len(T)',len(T)
    return 1



###### Norm condition step ######

def brace_map(a,S,p):
    r"""
    
    INPUT:
        - ``a`` : an element of the `K(S,p)` Selmer group of a number field `K`
        - ``S`` : a set of prime ideals of `K`
        - ``p`` : a natural prime number
    
    OUTPUT:
        - ``b`` : a vector that represents [a] in S - Class group of `K`
        - ``J`` : the fractioal ideal that represents [a] in S - Class group of `K`
    
    COMMENT:
        
        It is the image of the surjective map on the short exact sequence 
        
        `1\longrightarrow\mathcal O^*_{K,S}/\mathcal O^{*p}_{K,S}\xrightarrow{i} K(S,p)\xrightarrow{[a]}\mathcal C_{K,S}[p]\longrightarrow 1`
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-41)
        sage: S = K.primes_above(41)
        sage: Cls = K.S_class_group(S)
        sage: Cls
            S-class group of order 8 with structure C8 of Number Field in a with defining polynomial x^2 + 41
        sage: K.ideal(2).factor()
            (Fractional ideal (2, a + 1))^2
        sage: brace_map(K(2),S,2)
            ([4], Fractional ideal (2, a + 1))
        sage: K.ideal(3).factor()
            (Fractional ideal (3, a + 1)) * (Fractional ideal (3, a + 2))
        sage: brace_map(K(3),S,2)
            ValueError: The element a does not lie in K(S,p)     
    """
    
    if p not in Primes():
        raise ValueError('p is not a prime')
    
    K = a.parent()
    Cls = K.S_class_group(S)
    fac = K.ideal(a).factor()
    J = K.ideal(1)
    for prime in fac:
        if prime[0] not in S:
            m = prime[1]/p
            if m not in ZZ:
                raise ValueError('The element a does not lie in K(S,p)')
            J = J*(prime[0])**m
    
    
    b = Cls(J).list()
    
    return b,J


def generator_S_principle_ideal(J,S):
    r"""
    
    INPUT:
        - ``J`` : a fractional ideal which is a principal S - ideal
        - ``S`` : a list of prime ideals of a number field `K`
    
    OUTPUT:
        A generator for the principal S - ideal J
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-41)
        sage: S = K.primes_above(2)
        sage: I = S[0]
        sage: Cls = K.S_class_group(S)
        sage: Cl = K.class_group()
        sage: Cl(I).order()
            2
        sage: generator_S_principle_ideal(I,S)
            1
        sage: J = K.class_group().gen().ideal()
        sage: Cl(J).order()
            8
        sage: generator_S_principle_ideal(J,S)
            ValueError: J is not a principal S - ideal
    """
    K = J.number_field()
    Cl = K.class_group()
    Cls = K.S_class_group(S)
    
    #We find a product I of ideals of S such that J*I is principal 
    
    gens_ord = Cl.gens_orders()
    card_S = len(S)
    card_gens_ord = len(gens_ord)
    M = matrix(ZZ,card_S+card_gens_ord,card_gens_ord)
    D = diagonal_matrix(ZZ,card_gens_ord,vector(gens_ord));
    for i,I in enumerate(S):
        M[i] = vector(Cl(I).list())
    for i,d in enumerate(D):
        M[i+card_S] = d
           
    A = -vector(Cl(J).list())
    X = M.solve_left(A)
    I = K.ideal(1)
    for i,N in enumerate(S):
        if X[i] not in ZZ:
            raise ValueError('J is not a principal S - ideal')
        I = I*N**(X[i])
    
    J = I*J
    return J.gens_reduced()[0]


def reorder(A,n):
    r"""
    
    INPUT:
        - ``A`` : a list
        - ``n`` : a natural positive number
        
    OUTPUT:
        A list with the same length ``m`` as ``A`` and its first ``n``-th elements are the last ``n``-th elements of ``A`` and its last ``(m-n)``-th elements are the first ``(m-n)`` elements of ``A``.
        
    EXAMPLE::
        
        sage: A = [1,2,3,4,5]
        sage: reorder(A,3)
            [3, 4, 5, 1, 2]
        
        sage: B = [5,6,6,7,9]
        sage: reorder(B,5)
            [5, 6, 6, 7, 9]
        
        sage: C = [5,10,6,7]
        sage: reorder(C,5)
            ValueError: n is bigger than the length of A
        
    """
    m = len(A)
    if n>m:
        raise ValueError('n is bigger than the length of A')
    S = [a for a in A[0:m-n]]
    T = [a for a in A[m-n:m]]
    
    return T+S


def list_selmer_group(a,S,p):
    r"""
    
    INPUT:
        - ``a`` : an element in the Selmer group `K(S,p)` of a number field `K`
        - ``S`` : a list of prime ideals of K
        - ``p`` : a natural prime number
    
    OUTPUT:
        Return a copy of the exponent vector with respect of the generators that K.selmer_group(S,p) function gives
    
    COMMENT:
        The algorithm is based on the short exact sequence
        
        `1\longrightarrow\mathcal O^*_{K,S}/\mathcal O^{*p}_{K,S}\xrightarrow{i} K(S,p)\xrightarrow{[a]}\mathcal C_{K,S}[p]\longrightarrow 1`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+3)
        sage: S = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: Sel = K.selmer_group(S,3)
        sage: w = Sel[0]^2*Sel[2]*Sel[1]^5
        sage: list_selmer_group(w,S,3)
            (2, 2, 1, 0)
            
        sage: K.<a> = NumberField(x^2-6)
        sage: S = sum([K.primes_above(p) for p in []],[])
        sage: Sel = K.selmer_group(S,2)
        sage: w = Sel[0]
        sage: list_selmer_group(w,S,2)
            (1, 0)       
    """
    if p not in Primes():
        raise ValueError('p is not a prime')
    
    K = a.parent()
    Cls = K.S_class_group(S)
    Sunit = K.S_unit_group(S=S)
    Sel = K.selmer_group(S,p)   
    
    M = matrix(ZZ,len(Sel),len(Cls.gens()))
    j = 0
    for u in Sel:
        r = vector(brace_map(u,S,p)[0])
        M.set_row(j,r)
        j += 1
       
    b = vector(brace_map(K(a),S,p)[0])
    A = M.solve_left(b)   
    
    y = 1
    for s,t in zip(Sel,A):
         y=y*s**t
         
    u = a/y
    v = brace_map(u,S,p)[1]
    gen = generator_S_principle_ideal(v,S)
    t = u*gen**(-p)
    
    Sunit_part = vector(ZZ,len(Sel))
    t_list = Sunit(t).list()
    j = 0
    for i,gen in enumerate(Sunit.gens()):
        if gen.order() == Infinity or gen.order().gcd(p) != 1:
            Sunit_part[j] = t_list[i]
            j += 1
            
    n = len([g for g in Sel if g.absolute_norm() == 1 or g.absolute_norm() == -1])
    Sunit_part = vector(reorder(list(Sunit_part),len(Sel)-n))
    v = Sunit_part + A
    v = v.change_ring(Integers(p))
    
    return v
    
    
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


#####  S3 extensions over K unramified outside S ######

def suitable_element_of_Kz(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field with `\zeta_3\not\in K`
        - ``S`` : a list of prime ideals of ``K``
        
    OUTPUT:
        A list of all 2-tuples `[b,Tr_{Kz/K}(a)]` we need, in order to determine a defining polynomial of a suitable cubic extension of ``K``. 
        
    REFERENCE:
        - Henri Cohen. Advanced Topics in Computational Number Theory. Number 193 in Graduate Texts in Mathematics. Springer-Verlag, New York, 1999. It is a special case of the theorem 5.3.5.
        - Angelos Koutsianas Thesis, 
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: suitable_element_of_Kz(K,S)
            [[1,1]]
            
        sage: K.<a> = NumberField(x^2+1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: suitable_element_of_Kz(K,S)
            [[-1, a], [-a, a - 1], [a, -2*a + 1], [-a, 2*a + 1]]
            
        sage: K.<a> = NumberField(x^2+3)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: suitable_element_of_Kz(K,S)
            ValueError: K contains the 3rd root of unit
    """    
    
    RK = PolynomialRing(K,'y')
    y = RK.gen()
    if not (y**2+3).is_irreducible():
        raise ValueError('K contains the 3rd root of unity')
    
    Kz = K.extension(x**2+3,'b')
    K_selmer_basis = K.selmer_group(S,3)
    Sz = sum([Kz.primes_above(p) for p in S],[])
    Kz_selmer_basis = Kz.selmer_group(Sz,3)
    M = matrix(Integers(3),len(Kz_selmer_basis),len(K_selmer_basis))
    for i,c in enumerate(Kz_selmer_basis):
        M[i] = list_selmer_group(K(c.relative_norm()),S,3)
    ker = M.kernel()
    T = []
    S = []
    for v in ker:
        if v != 0 and v not in S:
            S.append(2*v)
            a = 1
            for s,t in zip(Kz_selmer_basis,v):
                a *= s**t
            fac = (y**3 - a.relative_norm()).factor()
            if fac[0][1] == 1:
                b = -fac[0][0](0)
            else:
                b = -fac[1][0](0)
            T.append([b,a.trace(a.parent().base_field())])
    
    return T


def full_selmer_group(K,S,n):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of K
        - ``n`` : a natural number
        
    OUTPUT:
        A list of representatives of the Selmer group `K(S,n)`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: [a.factor() for a in full_selmer_group(K,S,2)]
            [1, -1, 3, (-1) * 3, 2, (-1) * 2, 2 * 3, (-1) * 2 * 3]
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: [a.factor() for a in full_selmer_group(K,S,3)]
            [1, 5, 5^2, 2, 2 * 5, 2 * 5^2, 2^2, 2^2 * 5, 2^2 * 5^2]
            
        sage: K.<a> = NumberField(x^2-6)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: full_selmer_group(K,S,2)
            [1, 2*a - 5, -1, -2*a + 5, a + 3, a - 3, -a - 3, -a + 3, a - 2, -9*a + 22, -a + 2, 9*a - 22, a, -5*a + 12, -a, 5*a - 12]
    """
                  
    Sel = K.selmer_group(S,n)
    list = [prod([s**t for t,s in zip(v,Sel)]) for v in cartesian_product_iterator([xrange(n)]*len(Sel))]
    
    #We want each element to appear only once
    
    sel = []
    for a in list:
        if a not in sel:
            sel.append(a)
    return sel


def modified_selmer_group_c3(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field such that `\zeta_3\in K`
        - ``S`` : a list of prime ideals of `K`
    
    OUTPUT:
        A list of elements in `K` such that for two elements `a,b` of the list it holds `K(\sqrt[3]{a})\neq K(\sqrt[3]{b})` 
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+3)
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: modified_selmer_group_c3(K,S)
            [-1/2*a + 1/2, 5, -5/2*a + 5/2, -5/2*a - 5/2, 2, -a + 1, -a - 1, 10, -5*a + 5, -5*a - 5, 50, -25*a + 25, -25*a - 25]
            
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: modified_selmer_group_c3(K,S)
            ValueError: The 3-rd root of unity does not lie in K
    """
    y = PolynomialRing(K,'y').gen()
    if (y**2+3).is_irreducible():
        raise ValueError('The 3-rd root of unity does not lie in K')
    
    Sel = K.selmer_group(S,3)
    elements = []
    temp = []
    for v in cartesian_product_iterator([Integers(3)]*len(Sel)):
        v = vector(v)
        if v not in temp and 2 * v not in temp:
            elements.append(prod([b**e for b,e in zip(Sel,v)]))
            temp.append(v)
            temp.append(2*v)
    
    return [b for b in elements if b != 1]
       
    
def quadratic_extensions(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        A list of all quadratic extensions of `K` unramified outside `S`
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2]],[])
        sage: quadratic_extensions(K,S)
            [Number Field in c2 with defining polynomial x^2 + 1 over its base field, 
            Number Field in c2 with defining polynomial x^2 - 2 over its base field, 
            Number Field in c2 with defining polynomial x^2 + 2 over its base field]    
        sage: S = sum([K.primes_above(p) for p in [3,5]],[])
        sage: quadratic_extensions(K,S)
            [Number Field in c2 with defining polynomial x^2 - 5 over its base field, 
            Number Field in c2 with defining polynomial x^2 + 3 over its base field, 
            Number Field in c2 with defining polynomial x^2 + 15 over its base field]
            
        sage: K.<a> = QuadraticField(-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: S
            [Fractional ideal (a + 1), Fractional ideal (3)]
        sage: for L in quadratic_extensions(K,S):
        sage:     L.relative_discriminant().factor()
            (Fractional ideal (a + 1))^4
            Fractional ideal (3)
            (Fractional ideal (a + 1))^4 * (Fractional ideal (3))
            (Fractional ideal (a + 1))^5
            (Fractional ideal (a + 1))^5
            (Fractional ideal (a + 1))^5 * (Fractional ideal (3))
            (Fractional ideal (a + 1))^5 * (Fractional ideal (3))
    """
    
    #We enumerate the 2-Selmer group of K for the set of primes S
                          
    Sel = full_selmer_group(K,S,2)
    
    #we create all possible C2 extensions
    
    candidates = []
    t = PolynomialRing(K,'t').gen()
    for s in Sel:
        if s != 1:
            L = K.extension(t**2 - s,'c2')
            candidates.append(L)          
    
    #We check which fields in 'candidates' have discriminant that is divisible by primes not in 'S'.
                                  
    quadratic_extensions = []
    for L in candidates:       
        if len([I[0] for I in L.relative_discriminant().factor() if I[0] not in S]) == 0:
            quadratic_extensions.append(L)
            
    return quadratic_extensions


def c3_z3_in(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field such that `\zeta_3\in K`
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        A list with all cubic extensions of `K` unramified outside of `S`.
        
    COMMENT:
        `K` should contain `\zeta_3`.
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-3)
        sage: S = sum([K.primes_above(p) for p in [3]],[])
        sage: S
            [Fractional ideal (-a)]
        sage: for L in c3_z3_in(K,S):
        sage:     L.relative_discriminant().factor()
            (Fractional ideal (-a))^6
            (Fractional ideal (-a))^8
            (Fractional ideal (-a))^8
            (Fractional ideal (-a))^8
            
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: c3_z3_in(K,S)
            ValueError: K does not contain the 3-rd root of unity
    """
    
    t = PolynomialRing(K,'t').gen()
    if (t**2+3).is_irreducible():
        raise ValueError('K does not contain the 3-rd root of unity')
    
    #we enumerate all elements of the 3-Selmer group of K which give different cubic extensions
                          
    Sel = modified_selmer_group_c3(K,S)
    
    #we create all possible cubic extensions
    
    candidates = []
    for s in Sel:
        if s != 1:
            L = K.extension(t**3 - s,'c3')
            candidates.append(L)          
    
    #We check which fields in 'candidates' have discriminant that is divisible by primes not in 'S'.
                                  
    cubic_extensions = []
    for L in candidates:       
        if len([I[0] for I in L.relative_discriminant().factor() if I[0] not in S]) == 0:
            cubic_extensions.append(L)
            
    return cubic_extensions


def c3_z3_not(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field such that `\zeta_3\not\in K`
        - ``S`` : a list of prime ideals of `K`
       
    OUTPUT:
        A list with all cubic extensions of `K` unramified outside `S`
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: c3_z3_not(K,S)
            [Number Field in c3 with defining polynomial x^3 - 3*x - 1 over its base field]
            
        sage: K.<a> = QuadraticField(-2)
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: S
            [Fractional ideal (a), Fractional ideal (5)]
        sage: for L in c3_z3_not(K,S):
        sage:    L.relative_discriminant().factor(),L.is_galois_relative()
            (Fractional ideal (5))^2 True
    """
    t = PolynomialRing(K,'t').gen()
    T = suitable_element_of_Kz(K,S)
    SQ = []
    for prime in S:
        p = prime.absolute_norm().factor()[0][0]
        if p not in SQ:
            SQ.append(p)
    cubic_extensions = []
    for beta,trace in T:
        #we evaluate a 3 degree polynomial 'g'
              
        g = t**3 - 3*beta*t - trace
        gdisc = g.discriminant()

        #if 'g' is irreducible and its relative discriminant is a S unit then it is a defining polynomial for a possible extension

        if g.is_irreducible():
            L = K.extension(g,'c3')

            if K.ideal(gdisc).is_S_unit(S = S):
                cubic_extensions.append(L)
            elif gdisc.absolute_norm().prime_to_S_part(S = SQ).is_square():

                #we check if the discriminant of L is unramified outside S

                if K.ideal(L.relative_discriminant()).is_S_unit(S = S):
                # if len([I[0] for I in L.relative_discriminant().factor() if I[0] not in S]) == 0:
                    cubic_extensions.append(L)

    return cubic_extensions


def cubic_extensions(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        A list with all cubic extensions of `K` unramified outside `S`
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-2)
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: S
            [Fractional ideal (a), Fractional ideal (5)]
        sage: for L in cubic_extensions(K,S):
        sage:    L.relative_discriminant().factor(),L.is_galois_relative()
            (Fractional ideal (5))^2 True
            
        sage:K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3,5,7]],[])
        sage: for L in cubic_extensions(K,S):
        sage:     L.is_galois_absolute(),L.absolute_discriminant().factor()
            True 7^2
            True 3^4
            True 3^4 * 7^2
            True 3^4 * 7^2
    
        sage: K.<a> = QuadraticField(-3)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: S
            [Fractional ideal (2), Fractional ideal (-a)]
        sage: for L in cubic_extensions(K,S):
        sage:     L.is_galois_relative(),L.relative_discriminant().factor()
            True (Fractional ideal (-a))^6
            True (Fractional ideal (-a))^8
            True (Fractional ideal (-a))^8
            True (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^4
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^6
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^6
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
    """
    t = PolynomialRing(K,'t').gen()
    if (t**2+3).is_irreducible():
        return c3_z3_not(K,S)
    else:
        return c3_z3_in(K,S)


def s3_extensions(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field `K`
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        - A list of cubic polynomial with coefficients in `K` which have as a splitting field a `S_3` Galois extension of `K` unramified outside `S`.
        - The splitting fields of the polynomials
        - All the qudratic extensions of `K` unramified outside `S`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [3]],[])
        sage: s3_extensions(K,S)
            [[x^3 + 9], [Number Field in c3 with defining polynomial x^3 + c2 over
            its base field], [Number Field in c2 with defining polynomial x^2 + 3
            over its base field]]
            
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2]],[])
        sage: s3_extensions(K,S) 
            [[], [], [Number Field in c2 with defining polynomial x^2 + 1 over its
            base field, Number Field in c2 with defining polynomial x^2 - 2 over its
            base field, Number Field in c2 with defining polynomial x^2 + 2 over its
            base field]]
            
        sage: K.<a> = NumberField(x^2-2)
        sage: S = sum([K.primes_above(p) for p in [3]],[])
        sage: s3_extensions(K,S)  
            [[x^3 - a - 1, x^3 + 18*a + 27, x^3 + 9, x^3 - 9*a - 9], [Number Field
            in c3 with defining polynomial x^3 - a - 1 over its base field, Number
            Field in c3 with defining polynomial x^3 + (2*a + 3)*c2 over its base
            field, Number Field in c3 with defining polynomial x^3 - c2 over its
            base field, Number Field in c3 with defining polynomial x^3 + (-a -
            1)*c2 over its base field], [Number Field in c2 with defining polynomial
            x^2 + 3 over its base field]]
    """
    t = PolynomialRing(K,'t').gen()
    
    #we evaluate all quadratic extensions of K unramified outside S

    quadratic = quadratic_extensions(K,S)
    polynomials = []
    fields = []

    for M in quadratic:
        g = [e for e in M.automorphisms() if e(M.gen()) != M.gen()][0]  #the generator of Gal(M/K)
        SM = sum([M.primes_above(p) for p in S],[])                   


        cubics = cubic_extensions(M,SM) #all the cubic extensions of M unramified outside SM

        eKM = [e for e in K.embeddings(M) if e.preimage(M(K.gen())) == K.gen()][0] #the compatible embbeding of K in M

        #we check when L is an S3 extension and we give a 3-degree polynomial over K such that its splitting is L. By 
        
        for L in cubics:
            
            f = L.defining_polynomial()
            
            #by construction the quadratic coefficient of f is 0. The coefficients of 'f' and 'f_bar'
            
            f0 = f[0]                        
            f1 = f[1]
            f0bar = g(f0)
            f1bar = g(f1)
            
            #the case when f has coefficients in K
            
            if f0bar == f0 and f1bar == f1:
                f0 = eKM.preimage(f0)
                f1 = eKM.preimage(f1)
                f = t**3 + f1*t + f0
                if K.absolute_degree() == 1: #it can not evaluate f.discriminant() if K has absolute degree 1
                    f = f.change_ring(QQ)
                
                if not f.discriminant().is_square(): #if the discriminant of f is not a square we have a S3 extension
                    polynomials.append(f)
                    fields.append(L)
            else:              

                #f doesn't have coefficients in K
                
                p = PolynomialRing(L,'p').gen()
                fbar = p**3 + f1bar*p + f0bar #the conjugate of f
                
                #if fbar is not irreducible in L[x] then the extension is Galois

                if not fbar.is_irreducible():
                    
                    #we evaluate the sum of a root of f and a root of fbar such that the sum is not 0
                    
                    rf = f.change_ring(L).roots()
                    rfbar = fbar.roots()
                    #print f,fbar.change_ring(L).roots(),fbar
                    r = rf[0][0]+rfbar[0][0]
                    if r.is_zero():
                        #we take an other root of rfbar for which we have proved that r!=0
                        r = rf[0][0]+rfbar[1][0]
                        
                    #h is a 3-degree polynomial and should have coefficients in K
                                  
                    h = r.minpoly()
                    if g(h[2]) == h[2] and g(h[1]) == h[1] and g(h[0]) == h[0]:
                        
                        h0 = eKM.preimage(h[0])
                        h1 = eKM.preimage(h[1])
                        h2 = eKM.preimage(h[2])
                        h = t**3 + h2*t**2 + h1*t + h0
                        
                        if K.absolute_degree() == 1: #it can not evaluate f.discriminant() if K has absolute degree 1
                            h = h.change_ring(QQ)
                        
                        #we check if the discriminant of 'h' is not a square
                        
                        if not h.discriminant().is_square():
                           polynomials.append(h)
                           fields.append(L)                       
             
    return polynomials, fields, quadratic


def two_division_fields(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        - ``c2`` : a list of quadratic extensions of `K` unramified outside `S`
        - ``c3`` : a list of cubic extensions of `K` unramified outside `S`
        - ``s3_polynomials`` : a list of cubic polynomials with coefficients in `K` which have splitting field an `S_3` extension of `K` unramified outside `S`
        - ``s3`` : a list of `S_3` extensions of `K` unramified outside `S`
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2]],[])
        sage: two_division_fields(K,S)
            ([Number Field in c2 with defining polynomial x^2 + 1 over its base
            field, Number Field in c2 with defining polynomial x^2 - 2 over its base
            field, Number Field in c2 with defining polynomial x^2 + 2 over its base
            field], [], [], [])
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: two_division_fields(K,S)
            ([Number Field in c2 with defining polynomial x^2 + 1 over its base
            field, Number Field in c2 with defining polynomial x^2 - 5 over its base
            field, Number Field in c2 with defining polynomial x^2 + 5 over its base
            field, Number Field in c2 with defining polynomial x^2 - 2 over its base
            field, Number Field in c2 with defining polynomial x^2 + 2 over its base
            field, Number Field in c2 with defining polynomial x^2 - 10 over its
            base field, Number Field in c2 with defining polynomial x^2 + 10 over
            its base field], [], [x^3 + 45*x + 270], [Number Field in c3 with
            defining polynomial x^3 + 15*x - 40*c2 over its base field])
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: two_division_fields(K,S)
            ([Number Field in c2 with defining polynomial x^2 + 1 over its base
            field, Number Field in c2 with defining polynomial x^2 - 3 over its base
            field, Number Field in c2 with defining polynomial x^2 + 3 over its base
            field, Number Field in c2 with defining polynomial x^2 - 2 over its base
            field, Number Field in c2 with defining polynomial x^2 + 2 over its base
            field, Number Field in c2 with defining polynomial x^2 - 6 over its base
            field, Number Field in c2 with defining polynomial x^2 + 6 over its base
            field], [Number Field in c3 with defining polynomial x^3 - 3*x - 1 over
            its base field], [x^3 - 3*x - 14, x^3 - 2, x^3 + 9, x^3 + 18, x^3 + 36,
            x^3 - 9*x + 18, x^3 - 18*x + 24, x^3 + 3*x + 2], [Number Field in c3
            with defining polynomial x^3 + 3*c2*x + c2 - 1 over its base field,
            Number Field in c3 with defining polynomial x^3 - 2 over its base field,
            Number Field in c3 with defining polynomial x^3 + c2 over its base
            field, Number Field in c3 with defining polynomial x^3 + 2*c2 over its
            base field, Number Field in c3 with defining polynomial x^3 + 4*c2 over
            its base field, Number Field in c3 with defining polynomial x^3 - 3*x -
            2*c2 over its base field, Number Field in c3 with defining polynomial
            x^3 + (-3*c2 - 9)*x + 5*c2 + 12 over its base field, Number Field in c3
            with defining polynomial x^3 + 3*x + 2 over its base field])
    """
    c3 = cubic_extensions(K,S)
    s3_polynomials,s3,c2 = s3_extensions(K,S)
    
    return c2,c3,s3_polynomials,s3


#### About elliptic curves

def eroots(E):
    r'''
    
    INPUT:
        
    - ``E`` : an elliptic curve
    
    OUTPUT:
        
     The three roots of the 2 - division polynomial of ``E``
     
    EXAMPLES::
        
      sage : E = EllipticCurve([0,0,0,-1,0])
      sage : eroots(E)
        (1, 0, -1)  
    '''      
   
    f = E.division_polynomial(2)
    L = f.splitting_field('a')
    e1, e2, e3 = f.roots(L)
    
    return e1[0], e2[0], e3[0]


def lambda_invariants(E):
    r'''
    
    INPUT:
        
    - ``E`` : an elliptic curve
    
    OUTPUT:
    
     A list with all lambda invariants of E.
    
    EXAMPLES::
        
      sage : E = EllipticCurve([0,0,0,-1,0])
      sage : lambda_invariants(E)
          [1/2, 2, 1/2, -1, 2, -1]
    '''
    
    e1, e2, e3 = eroots(E) 
    l = (e1 - e2) / (e1 - e3)
    
    return [l,1/l,1-l,1-1/l,1/(1-l),l/(l-1)]


def j_invariant(l):
    r"""
    
    INPUT:
        - ``l`` : the lambda invariant of an elliptic curve `E`
        
    OUTPUT:
         The associate to ``l`` `j`-invariant of `E`
    """
    
    return (2**8 *(l**2 - l + 1)**3)/(l**2 * (1-l)**2)


########## S-unit reduction step with different groups  for the equation x+y = 1 ##########

def round(a):
    r"""
    
    INPUT:
        - ``a`` : a real number
       
    OUTPUT:
        The closest integer to ``a``
    """
    if a in ZZ:
        return a
    else:
        return a.round()


def modified_height_infinite_case(a,place):
    r"""
    
    INPUT:
        - ``a`` : an element of the number field `K`
        - ``place`` (ring morphism): an infinite place of `K`
    
    OUTPUT:
        The modified absolute height for `a` as it is defined in the reference
        
    REFERENCE:
        A. Baker and G. Wustholz. Logarithmic forms and group varieties. J. Reine Angew. Math., 442:19-62, 1993.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2-2)
        sage: place = K.places()[0]
        sage: modified_height_infinite_case(a,place)
            1.580325730234823217013360503412    
        sage: modified_height_infinite_case(0,place)
            ValueError: a has not to be 0 or 1
            
        sage: K.<a> = NumberField(x-1)
        sage: place = K.places()[0]
        sage: modified_height_infinite_case(5,place)
            1.609437912434100374600759333226
    """
    
    if a == 0 or a == 1:
        raise ValueError('a has not to be 0 or 1')
    # print 'a=%s'%(a)
    K = place.domain()
    a = K(a)
    # print 'place',place.domain(),K
    d = K.absolute_degree()
    return max([d*(a.global_height(place.codomain().precision())),log(place(a)).abs(),1])/d
    

def e_s_real(a,place):
    r"""
    
    INPUT: 
        - ``a`` : an element of a number field `K`
        - ``place`` (ring morphism): an real place of `K`
        
    OUTPUT:
        Reurn `a` if `place(a)>=0`, otherwise `-a`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^4-7)
        sage: place = K.places()[0]
        sage: e_s_real(a,place)
            -a
        sage: e_s_real(-a,place)
            -a
        sage: place(a)
            1.626576561697785743211232345494
    """
    
    if place(a) < 0:
        return (-1)*a
    else:
        return a
 
    
def Baker_Wustholz_low_lattice_bound(A,place):
    r"""
    
    INPUT:
        - ``A`` : a list of elements of a number field `K`
        - ``place`` (ring morphism): an infinite place of `K`
    
    OUTPUT:
        The constant of the low bound of the main theorem(page 20) of the reference
        
    REFERENCE:
        A. Baker and G. Wustholz. Logarithmic forms and group varieties. J. Reine Angew. Math., 442:19-62, 1993.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2-7)
        sage: place = K.places()[0]
        sage: Baker_Wustholz_low_lattice_bound([a,a^2+1],place)
            4.956654367093510940632396859094e10*log(8)
    """
    
    if len(A) == 0:
        raise ValueError('The list A is empty')
    
    d = A[0].parent().absolute_degree()
    n = len(A)
    c = 18*(factorial(n+1))*n**(n+1)*(32*d)**(n+2)*log(2*n*d)

    return c*prod([modified_height_infinite_case(a,place) for a in A])
    

def a_basis_with_0_order_at_p(prime,G):
    r"""
    
    INPUT:
        - ``prime`` : a prime ideal of a number field `K`
        - ``G`` : a list of generators of a subgroup of `K^*`
        
    OUTPUT:
        - ``M0`` : a list of elements in `K^*` which contains all `\mu_0` that can appear to lemma IX.3 page 139 of the reference
        - ``M`` : a list of elements in `K^*` which contains all `\mu_i` for `i>0` that appear to lemma IX.3 page 139 of the reference
        -  the index of the generator in ``G`` which has the property as it is defined in lemma IX.3 page 139 of the reference
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+5)
        sage: SK = K.primes_above(30)
        sage: prime = K.prime_above(7)
        sage: SuK = K.S_unit_group(S = SK)
        sage: G = SuK.gens_values()
        sage: M0, M ,k= a_basis_with_0_order_at_p(prime,G)
        sage: G
            [-1, 2, a + 1, a - 1, -a]
        sage: M0,M,k
            ([-1, 1], [2, a + 1, a - 1, -a])
        sage: prime = K.prime_above(5)
        sage: a_basis_with_0_order_at_p(prime,G)
            ([-1, 1], [2, a + 1, a - 1])
    """ 
    K = prime.ring() 
    g0 = [g for g in G if g.multiplicative_order() != Infinity]
    Gfree = [g for g in G if g.multiplicative_order() == Infinity]
    if len(g0) ==1:
        g0 = g0[0]
    else:
        g0 = K(1)
    
    if len(Gfree) == 0:
        raise ValueError('The group does not have free part')
    if g0 == 0 or len([g for g in Gfree if g == 0]) != 0:
        raise ValueError('Either g0 = 0 or there is a zero element in G')
           
    e = prime.absolute_ramification_index()
    f = prime.residue_class_degree()
    ordprime = lambda x: x.valuation(prime)
    
    
    N = [ordprime(K(g)) for g in Gfree]        #N has the valuations of G
    n_k = min(N)

    #we check if our initial basis satisfies the condition ord(g0)=0 and ord(g)=0 for eacj g in Gfree
    
    if len([a for a in N if a != 0]) == 0:
        return [-g0**i for i in range(g0.multiplicative_order())],Gfree,0
    
    #In the following lines we evaluate sigma,n_k and the other parameters that appear in Lemma IX.3 of reference
        
    N_abs = [a.abs() for a in N]
    n_k_abs = min([a for a in N_abs if a > 0])
    k = N_abs.index(n_k_abs)
    n_k = N[k]
    N2 = [N[i] for i in range(len(N)) if i != k]   #N2 has all n_i except for that one with minimal absolute value.
    G2 = [Gfree[i] for i in range(len(Gfree)) if i != k]   #G2 has all the generator excepr for that one associate to n_k
    
    M0 = []
    for vec in cartesian_product_iterator([xrange(n_k_abs)]*len(N2)):
        sigma = -(vector(vec)*vector(N2))
        if sigma % n_k == 0:
            for g in [g0**i for i in range(g0.multiplicative_order())]:
                m0 = -g * prod([a**b for a,b in zip(G2,vec)]) * Gfree[k]**(sigma/n_k)
                if m0 not in M0:
                    M0.append(m0)
    return M0,[(g**n_k)*(Gfree[k]**(-n)) for g,n in zip (G2,N2)],k+1


def upper_bound_modified_height_finite_case(a,embeddings,prime):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``embeddings`` : a list of all embeddings of `K` to `\mathbb C`
        - ``prime`` : a prime ideal of `K`
        
    OUTPUT:
        An upper bound for the modified height with respect to `prime`. See the appendix of the reference
    
    REFERENCE:
        N. Tzanakis and B. M. M. De Weger. Solving a specific Thue-Mahler equation. Mathematics of Computation, 57(196):799-815, 1991.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+5)
        sage: prime = K.prime_above(2)
        sage: em = K.embeddings(ComplexField(100))
        sage: upper_bound_modified_height_finite_case(a^4,em,prime)
            3.2188758248682007492015186665
    """
        
    K = prime.ring()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()
    d = K.absolute_degree()
    prec = embeddings[0].codomain().precision()
    
    t = polygen(K)
    if ( p > 2 and not (t**2+1).is_irreducible() ) or ( p == 2 and  not (t**2+3).is_irreducible() ):
        D = d
    else:
        D = 2*d
        
    return max([a.global_height(prec),max([log(em(a)).abs() for em in embeddings])/(2*pi*D),(f*log(p))/d])


def Yu_theorem(A,prime,embeddings):
    r"""
    
    INPUT:
        - ``A`` : a list of elements of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``embeddings`` : a list of all embeddings of `K` to `\mathbb C`
        
    OUTPUT:
        `(C_1C_2C_3 , C_1C_2C_3C_4)`, where `C_1, C_2, C_3` and `C_4` are defined in the theorem of the appendix of the reference
        
    REFERENCE:
         N. Tzanakis and B. M. M. De Weger. Solving a specific Thue-Mahler equation. Mathematics of Computation, 57(196):799-815, 1991.
         
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3 - 3*x - 1)
        sage: em = K.embeddings(ComplexField(50))
        sage: Yu_theorem(K.S_unit_group(S=K.primes_above(6)).gens_values(),em,K.prime_above(7))
            (1063465350238590566400000000000*log(2654208*log(7))/log(7),
            2126930700477181132800000000000*log(6)*log(2654208*log(7))/log(7))
    """    
    if len(A) == 0:
        raise ValueError('The list A is empty')
    
    if len([a for a in A if a.valuation(prime) != 0]) != 0:
        raise ValueError('There is an element in A which does not have 0 valuation')
    
    K = prime.ring()
    d = K.absolute_degree()
    t = polygen(K)
    p = prime.absolute_norm().factor()[0][0]   #p is the prime integer below 'prime'
    n = len(A)
    f = prime.residue_class_degree()
    
    D = 2*d
    if ( p > 2 and not (t**2+1).is_irreducible() ) or ( p == 2 and  not (t**2+3).is_irreducible() ):
        D = d
    
    #we evaluate the constants C1, C2, C3, C4 that appear on the theorem we mentioned 
    
    if p % 4 == 1:
        c1 = 35009 * (45/2)**n;
    elif p % 4 == 3:
        c1 = 30760 * 25**n;
    else:
        c1 = 197142 * 36**n;
    
    c4 = 2 * log(D)
    v = [upper_bound_modified_height_finite_case(a,embeddings,prime) for a in A]
    V = max(v)
    
    if p != 2:
        c3 = log( 2**11 * (n+1)**2 * D**2 * V )
    else:
        c3 = log( 3 * 2**10 * (n+1)**2 * D**2 * V )
    c2 = (n+1)**(2*n+4) * p**((D*f)/d) * (f*log(p))**(-n-1) * D**(n+2) * prod(v)

    return c1*c2*c3,c1*c2*c3*c4


def minimal_vector(A,y):
    r"""
    
    INPUT:
        - ``A`` : an square non-singular integer matrix whose rows generate a lattice `\mathcal L`
        - ``y`` : a row vector with integer coordinates
        
    OUTPUT:
        A low bound for the square of `\ell (\mathcal L,\vec y) =\begin{cases}\displaystyle\min_{\vec x\in\mathcal L}\Vert\vec x-\vec y\Vert &, \vec y\not\in\mathcal L. \\ \displaystyle\min_{0\neq\vec x\in\mathcal L}\Vert\vec x\Vert&,\vec y\in\mathcal L.\end{cases}`
    
    COMMENT:
        The algorithm is based on V.9 and V.10 of the reference
        
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
    
    EXAMPLE::
        
        sage: B = matrix(ZZ,2,[1,1,1,0])
        sage: y = vector(ZZ,[2,1])
        sage: minimal_vector(B,y)
            1/2
            
        sage: B = random_matrix(ZZ,3)
        sage: B
            [-2 -1 -1]
            [ 1  1 -2]
            [ 6  1 -1]
        sage: y = vector([1,2,100])
        sage: minimal_vector(B,y)
            15/28
    """
    if A.is_singular():
        raise ValueError('The matrix A is singular')
      
    n = len(y)
    c1 = 2**(n-1)
    ALLL = A.LLL()
    ALLLinv = ALLL.inverse()
    ybrace = [(a-round(a)).abs() for a in y * ALLLinv if (a-round(a)) != 0]
    
    if len(ybrace) == 0:
        return (ALLL.rows()[0].norm())**2 / c1
    else:
        sigma = ybrace[len(ybrace)-1]
        return ((ALLL.rows()[0].norm())**2 * sigma) / c1


def higher_precision(place,new_prec):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        - ``new_prec`` : the new precision
        
    OUTPUT:
        The ``place`` but with precision equal with ``new_prec``
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2-2)
        sage: place = K.places()[0]
        sage: place
            Ring morphism:
              From: Number Field in a with defining polynomial x^2 - 2
              To:   Real Field with 106 bits of precision
              Defn: a |--> -1.414213562373095048801688724210
        sage: higher_precision(place,50)
            Ring morphism:
              From: Number Field in a with defining polynomial x^2 - 2
              To:   Real Field with 50 bits of precision
              Defn: a |--> -1.4142135623731
              
        sage: K.<a> = NumberField(x^4-2)
        sage: place = K.places()[0]
        sage: place
            Ring morphism:
              From: Number Field in a with defining polynomial x^4 - 2
              To:   Real Field with 106 bits of precision
              Defn: a |--> -1.189207115002721066717492233629
        sage: higher_precision(place,150)
            Ring morphism:
              From: Number Field in a with defining polynomial x^4 - 2
              To:   Real Field with 150 bits of precision
              Defn: a |--> -1.1892071150027210667174999705604759152929721
    """
    K = place.domain()
    old_prec = place.codomain().precision()
    Kplaces = K.places(prec = new_prec)
    gens = K.gens()
    
    #Below we check which of the candidates in Kplaces has values quite close to the initial place.
    
    i = 1
    while i <= old_prec:
        Q = [q for q in Kplaces if len([0 for a in gens if (q(a)-place(a)).abs() <= 2**(-i)]) == len(gens)]
        if len(Q) == 1:
            return Q[0]
        else:
            i += 1
    if i > old_prec:
        raise ValueError('I cannot find the place')
    

def is_real_place(place):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        
    OUTPUT:
        `True` if it a real place, otherwise `False`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^4-2)
        sage: place = K.places()[0]
        sage: place
            Ring morphism:
              From: Number Field in a with defining polynomial x^4 - 2
              To:   Real Field with 106 bits of precision
              Defn: a |--> -1.189207115002721066717492233629
        sage: is_real_place(place)
            True
    """
    prec = place.codomain().precision()
    if place.codomain() == RealField(prec):
        return True
    else:
        return False
    

def reduction_step_real_case(place,B0,G,c7):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        - ``B0`` : the initial bound
        - ``G`` : a set of generators of the free part of the group
        - ``c7`` : a positive real number
        
    OUTPUT:
        - a new upper bound 
        - ``True`` if we have to increse precision, otherwise ``False``
        
    COMMENT:
        The constant ``c7`` in the reference page 137
        
    REFERENCE:
         Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
         
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: G = [g for g in K.S_unit_group(S = SK).gens_values() if g.multiplicative_order() == Infinity]
        sage: p1 = K.real_places(prec = 200)[0]
        sage: reduction_step_real_case(p1,10**10,G,2)
            (54,False)
    """   
    n = len(G)     
    Glog = [log(place(e_s_real(g,place))) for g in G]
    #We choose the initial value of C such that the vector v not to have 0 everywhere
    C = round(max([1/l.abs() for l in Glog if l != 0])+1)
    
    #if the precision we have is not high enough we have to increase it and evaluate c7 again
    if place.codomain().precision() < log(C)/log(2):
        return 0,True

    S = (n-1) * (B0)**2
    T = (1 + n * B0)/2
    finish = False
    while  not finish:
        A = copy(identity_matrix(ZZ,n));
        v = vector([round(g*C) for g in Glog])
        
        if v[n-1] == 0: #we replace the last element of v with an other non zero
            k = [i for i,a in enumerate(v) if not a.is_zero()][0]
            v[n-1] = v[k]
            v[k] = 0
        A[n-1] = v
        
        #We have to work with rows because of the .LLL() function
        
        A = A.transpose()
        y = copy(zero_vector(ZZ,n))
        l = minimal_vector(A,y)
             
        #On the following lines I apply Lemma VI.1 from Smart's book page 83
        
        if l < T**2 + S:
            C = 2 * C
            #Again if our precision is not high enough
            if place.codomain().precision() < log(C)/log(2):
                return 0,True 
        else:
            if sqrt(l-S) - T > 0:
                return round((log(C * 2)-log(sqrt(l-S) - T))/c7),False
            else:
                return B0,False   
    

def reduction_step_complex_case(place,B0,G,g0,c7):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        - ``B0`` : the initial bound
        - ``G`` : a set of generators of the free part of the group
        - ``g0`` : an element of the torsion part of the group
        - ``c7`` : a positive real number
        
    OUTPUT:
        - a new upper bound 
        - ``True`` if we have to increse precision, otherwise ``False``
        
    COMMENT:
        The constant ``c7`` in the reference page 138
        
    REFERENCE:
         Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
         
    EXAMPLE::
        
        sage: K.<a> = NumberField([x^3-2])
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: G = [g for g in K.S_unit_group(S = SK).gens_values() if g.multiplicative_order() == Infinity]
        sage: p1 = K.places(prec = 100)[1]
        sage: reduction_step_complex_case(p1,10^5,G,-1,2)
            (18,False)
    """
    #print [place(g) for g in G]
    #if len([g for g in G if place(g).abs() != 1]) == 0:
    #    raise ValueError('The place is not in the support of G')
    
    precision = place.codomain().precision()
    n = len(G)
    Glog_imag = [(log(place(g))).imag_part() for g in G]
    Glog_real = [(log(place(g))).real_part() for g in G]
    Glog_imag = Glog_imag + [2 * pi]
    Glog_real = Glog_real + [0]
    a0log_imag = (log(place(-g0))).imag_part()
    a0log_real = (log(place(-g0))).real_part()
    
    #the 2nd term comes from the fact we don't want later the vector v to have 0 everywhere
    C = max((B0**n/100),max([1/l for l in Glog_imag if l != 0]+[0])+1,max([1/l for l in Glog_real if l != 0]+[0])+1)
    
    #the case when the real part is 0 for all log(a_i)
    
    pl = higher_precision(place,2 * place.codomain().precision())
    if len([g for g in G if (pl(g).abs()-1).abs() > 2**(-place.codomain().precision())]) == 0:
        
        #we have only imaginary numbers and we are in case 2 as Smart's book says on page 84

        C = round(min((B0**n/100),max([1/l.abs() for l in Glog_imag if l != 0]+[0])))+1
        S = n * B0**2
        #if the precision we have is not high enough we have to increase it and evaluate c7 again
        if precision < log(C)/log(2):
            return 0,True
        
        T = ((n+1) * B0 + 1)/2
        finish = False
        while not finish:
            A = copy(identity_matrix(ZZ,n+1))
            v = vector([round(g * C) for g in Glog_imag])
            
            if v[n] == 0: #we replace the last element of v with an other non zero
                k = [i for i,a in enumerate(v) if not a.is_zero()][0]
                v[n] = v[k]
                v[k] = 0
            A[n] = v
            
            #We have to work with rows because of the .LLL() function
    
            A = A.transpose()                   
            y = copy(zero_vector(ZZ,n+1))
            y[n] = (-1) * round(a0log_imag * C)
            l = minimal_vector(A,y)

            #On the following lines I apply Lemma VI.1 of the reference page 83
            
            if l < T**2 + S:
                #print 'l-complex',round(l),round(T**2 + S)
                #if round(l) == 0:
                #    print 'Glog_imag,Glog_real',A.LLL()[0].norm()
                C = 2 * C
                #The same as above if for the new C the precision is low
                if precision < log(C)/log(2):
                   return 0,True 
            else:
                Bnew = round((log(C * 2)-log(sqrt(l-S)-T))/c7)
                finish = True
                if mod(y[n],A[n,n]) == 0:
                    return max(Bnew,(y[n]/A[n,n]).abs()),False
                else:
                    return Bnew,False
        
    else:
        
        #the case when the real part is not 0 for all log(a_i)

        C = max((B0**n/100),max([1/l.abs() for l in Glog_imag if l != 0]+[0])+1,max([1/l.abs() for l in Glog_real if l != 0]+[0])+1)#B0**((n+1)/2)
        if precision < log(C)/log(2):
            return 0, True
        S = (n-1) * B0 ** 2
        T = ((n+1)*B0+1)/sqrt(2)
        finish = False
        
        #we are relabeling the Glog_real and Glog_imag s.t. the condition Real(a_n)*Im(a_(n-1))-Real(a_(n-1))*Im(a_n)!=0 to be satisfied. See page 84 of the reference.
                
        k = [i for i in range(len(Glog_real)) if Glog_real[i] != 0][0]
        a = Glog_real[k]
        Glog_real[k] = Glog_real[n-1]
        Glog_real[n-1] = a
        
        a = Glog_imag[k]
        Glog_imag[k] = Glog_imag[n-1]
        Glog_imag[n-1] = a
        
        while not finish:

            A = copy(identity_matrix(ZZ,n+1))
            A[n-1] = vector([round(g * C) for g in Glog_real])
            A[n] = vector([round(g * C) for g in Glog_imag])
            #print 'A',[t for t in Glog_real if t != 0],round(C)
            #On the following lines I apply Lemma VI.2 of the reference page 85
            
            A = A.transpose()
            y = copy(zero_vector(ZZ,n+1))
            y[n] = (-1) * round(a0log_imag * C)
            y[n-1] = (-1) * round(a0log_real*C)
            l = minimal_vector(A,y)
             
            if l < T**2 + S:
                #print 'l-both',round(l)
                C = 2 * C
                #The same as above if for the new C the precision is low
                if precision < log(C)/log(2):
                    return 0,True 
            else:
                Bnew = round((log(C * 2)-log(sqrt(l-S)-T))/c7)
                
                #we take into account the second case of the theorem VI.2 of the reference page 85
                
                M = matrix(ZZ,2,[A[n-1,n-1],A[n-1,n],A[n,n-1],A[n,n]])
                b = vector(ZZ,2,[-y[n-1],-y[n]])
                if M.determinant() == 1 or M.determinant() == -1:
                    x = M.inverse() * b
                    return max(Bnew,x[0].abs(),x[1].abs()),False
                else:
                    return Bnew,False


def exp_p(a,prime,M):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``M`` : A positive integer
    
    OUTPUT:
        The `\mathfrak p-adic` exponential of ``a`` with respect to ``prime`` with accuary `p^M`, where `p` is the rational prime below ``prime``
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^4-2)
        sage: prime = K.ideal(a^3+1)
        sage: exp_p(a^3+1,prime,40)
            18258004137372707959101180869188831621509143332534131847/629590636134106\
            2871682271657666195529704407040000000000*a^3 +
            611037342146131657112686716139399492861248185433069281/21989378835566212\
            2356549929219959035044823040000000000*a^2 +
            2486870195746358623396592994809122223940417047969210857/1359343418925911\
            301840490471541564943913451520000000000*a +
            43407236459390842010586204501508547322377865800075980307/119622220865480\
            19456196316149565771506438373376000000000   
    """
    if M < 0:
        raise ValueError('M is negative')
    
    e = prime.absolute_ramification_index()
    p = prime.absolute_norm().factor()[0][0]
    if a.valuation(prime) <= e/(p-1):
        raise ValueError('The element a does not have the right valuation at prime')
    
    N = 1
    while N < e*(N.factorial().valuation(p)+M)/a.valuation(prime):
        N += 1
        
    factorial = 1
    exp_p = 1
    z = a
    for i in range(2,N+1):
        exp_p += z/factorial
        factorial *= i
        z *= a
        
    return exp_p


def log_p(a,prime,M): #This one to work with
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of the number field `K`
        - ``M`` : a positive integer
    
    OUPUT:
        The `\mathfrak p-adic` logarithm of a with respect to ``prime`` and accuracy `p^M`, where `p` is the rational prime below ``prime``
        
    COMMENT:
        Here we take into account the other primes in `K` above `p` in order to take coefficients with small values
        
    Example::
        
        sage: K.<a> = NumberField(x^2+14)
        sage: p1 = K.primes_above(3)[0]
        sage: p1
            Fractional ideal (3, a + 1)
        sage: log_p(a+2,p1,20)
            1068278195*a + 734401439
            
        sage: K.<a> = NumberField(x^4+14)
        sage: p1 = K.primes_above(5)[0]
        sage: p1
            Fractional ideal (5, a + 1)
        sage: log_p(1/(a^2-4),p1,30)
            -6082090776100252917421/5*a^3 - 5206581049546514677341/5*a^2 -
            12020643872593790461691/25*a - 17711088212203601903706/25
        
            
    """
    if a == 0:
        raise ValueError('a is the zero element')
    
    if a.valuation(prime) != 0:
        raise ValueError('The valuation of a with respect to prime is not zero')
    
    K = prime.ring()
    p = prime.absolute_norm().factor()[0][0]
    
    #In order to get an approximation with small coefficients we have to take into account the other primes above p with negative valuation
    
    primes = [(-(a.valuation(pr)),pr) for pr in K.primes_above(p) if a.valuation(pr) < 0]
    list = []
    for (val,pr) in primes: 
        #for its pair in primes we find an element in K such that it is divisible only by pr and not by any other ideal above p. Then we take this element in the correct exponent
        
        if pr.is_principal():
            list.append(pr.gens_reduced()[0]**val)
        else:
            list.append(pr.gens()[1]**val)

    return log_p_series_part(a * prod(list),prime,M) - sum([log_p_series_part(b,prime,M) for b in list])


def log_p_series_part(a,prime,M):
    r"""

    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of the number field `K`
        - ``M`` : a positive integer

    OUPUT:
        The `\mathfrak p-adic` logarithm of a with respect to ``prime`` and accuracy `p^M`, where `p` is the rational prime below ``prime``

    COMMENT:
        The algorithm is based on the algorithm page 30 of the reference

    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.

    EXAMPLE::

        sage: K.<a> = NumberField(x^2-5)
        sage: p1 = K.primes_above(3)[0]
        sage: p1
            Fractional ideal (3)
        sage: log_p_series_part(a^2-a+1,p1,30)
            120042736778562*a + 57497887435443

        sage: K.<a> = NumberField(x^4+14)
        sage: p1 = K.primes_above(5)[0]
        sage: p1
            Fractional ideal (5, a + 1)
        sage: log_p_series_part(1/(a^2-4),p1,30)
            143842771317132543834315137804216958834805571417161458644303555788803708\
            397256757062310978903907667409633861253921/18367099231598242312011508394\
            0975887159166493245638675235742454106002696789801120758056640625*a^2 +
            980470833745295017108554730448537715484438011434976509072834104950631953\
            52344619740974087640280522130685500861874/183670992315982423120115083940\
            975887159166493245638675235742454106002696789801120758056640625
    """
    # print 'a = %s\n'%(a)
    # print 'prime = %s, M = %s\n'%(prime,M)
    if a.valuation(prime) != 0:
        raise ValueError('The valuation of a with respect to prime is not zero')

    K = prime.ring()
    g = K.gen()
    n = K.absolute_degree()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()
    e = prime.absolute_ramification_index()
    s = p**f - 1
    divisor = s.divisors()
    order = min([d for d in divisor if (a**d - 1).valuation(prime) > 0])

    gamma= a**order
    t = 0
    while (gamma-1).valuation(prime) < e:
        t += 1
        gamma = gamma**p
    m = (gamma - 1).valuation(prime)/e

    n = 1
    while n < (log(n)/log(p) + M)/m:
        n += 1

    w = RR((log(n)/log(p))).floor()
    gamma = sum([ZZ(gi%(p**(M+w)))* g**i if gi.valuation(p) >= 0 else ZZ((gi * p**(-gi.valuation(p)))%(p**(M+w-gi.valuation(p)))) * p**(gi.valuation(p)) * g**i for i,gi in enumerate(gamma) if gi != 0],0)

    # import time
    # start = time.time()

    beta = 0
    delta = 1-gamma
    for i in range(1,n+1):
        beta -= delta/i
        delta *= (1-gamma)
        delta = sum([ZZ(di%(p**(M+w)))* g**e if di.valuation(p) >= 0 else ZZ((di * p**(-di.valuation(p)))%(p**(M+w-di.valuation(p)))) * p**(di.valuation(p)) * g**e for e,di in enumerate(delta) if di != 0],0)
    beta = beta/(order*p**t)

    # end = time.time()
    # print 'time for loop with beta',end-start

    #we try to make the coefficients small

    logp = 0
    for i,b in enumerate(beta.list()):
        val = b.valuation(p)
        if val < 0:
            t = b * p**(-val)
            t = ZZ(mod(t,p**(M-val)))
            t = t * p**val
        else:
            t = ZZ(mod(b,p**M))
        logp = logp + t * g**i

    return logp
    
    
def defining_polynomial_for_Kp(prime,M):
    r"""
    
    INPUT:
        - ``prime`` : a prime ideal of a number field `K`
        - ``M`` : a positive natural number
        
    OUTPUT:
        A polynomial with integer coefficients that is equivelant `\mod p^M` to the defining polynomial of the completion of `K` associate to the definig polynomial of `K`
    
    COMMENT:
        `K` has to be an absolute extension
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(2)
        sage: p2 = K.prime_above(7); p2
            Fractional ideal (-2*a + 1)
        sage: defining_polynomial_for_Kp(p2,10)
            x + 266983762
        
        sage: K.<a> = QuadraticField(-6)
        sage: p2 = K.prime_above(2); p2
        sage: defining_polynomial_for_Kp(p2,100)
            x^2 + 6
        sage: p5 = K.prime_above(5); p5
            Fractional ideal (5, a + 2)
        sage: defining_polynomial_for_Kp(p5,100)
            x + 3408332191958133385114942613351834100964285496304040728906961917542037
    """     
    K = prime.ring()
    if not K.is_absolute():
        raise ValueError('The number field is not an absolute extension')
    
    theta = K.gen()
    f = K.defining_polynomial()
    p = prime.absolute_norm().factor()[0][0]
    e = prime.absolute_ramification_index()
    
    find = False
    N = M
    while find == False:
        RQp = Qp(p,prec = N,type = 'capped-rel', print_mode = 'series')
        
        #We factorize f in Integers(p**M) using the factorization in Qp
                
        g = f.change_ring(RQp)
        factors = g.factor();
        
        #We are going to find which component of f is related to the prime ideal 'prime'
        
        L = [factors[i][0].change_ring(ZZ) for i in range(len(factors))]
        A = [g for g in L if (g(theta)).valuation(prime) >= e*N/2];
        
        if len(A) == 1:
            return A[0].change_ring(Integers(p**M)).change_ring(ZZ)
        else:
            N += 1  


def embedding_to_Kp(a,prime,M):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``M`` : a positive natural number
        
    OUTPUT:
        An element of K that is equivelant to ``a`` `\mod p^M` and the generator of `K` appears with exponent less than `e\cdot f`, where `p` is the rational prime below ``prime`` and `e,f` are the ramification index and residue degree, respectively.
    
    COMMENT:
        `K` has to be an absolute extension
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(17)
        sage: p = K.prime_above(13); p
            Fractional ideal (a - 2)
        sage: embedding_to_Kp(a-3,p,15)
            -34280483416323924357152170488129450629016974897358099396
                    
        sage: K.<a> = NumberField(x^4-2)
        sage: p = K.prime_above(7); p
            Fractional ideal (-a^2 + a - 1)
        sage: embedding_to_Kp(a^3-3,p,15)
            -1261985118949117459462968282807202378
    """
    K = prime.ring()    
    if not K.is_absolute():
        raise ValueError('K has to be an absolute extension')
    
    g = defining_polynomial_for_Kp(prime,M)
    p = prime.absolute_norm().factor()[0][0]
    gen = K.gen()
    n = g.degree()
    g = g.change_ring(QQ)
    f = K(a).lift()
    
    return K(sum([b*gen**j for j,b in enumerate(f.mod(g))]))


def log_p_of_a_list(L,prime,M):
    r"""
    
    INPUT:
        - ``L`` : a list of elements of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``M`` : a positive natural number
        
    OUTPUT:
        A list with the `\mathfrak p-adic` logarithms of ``L``    
        
    COMMENT:
        `K` has to be an absolute extension
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(17)
        sage: p = K.prime_above(13); p
            Fractional ideal (a - 2)
        sage: log_p_of_a_list([3*a^3+1,2*a^2+a+7],p,20)
            [228743122076416000464228/13*a + 31623834113854898674930/13,
            182612486178943231909010/13*a + 188811596701233257654644/13]
    """
    K = prime.ring()
    if not K.is_absolute():
        raise ValueError('K has to be an absolute extension')

    return [log_p(a,prime,M) for a in L]


def reduction_step_finite_case(prime,B0,M,M_logp,m0,c3,precision):
    r"""
    
    INPUT:
        - ``prime`` : a prime ideal of a number field `K`
        - ``B0`` : the initial bound
        - ``M`` : a list of elements of `K`
        - ``M_logp`` : the p-adic logarithm of elements in `K`
        - ``m0`` : an element of `K`
        - ``c3`` : a positive real constant
        - ``precision`` : the precision of the calculations
        
    OUTPUT:
        - a new upper bound 
        - ``True`` if we have to increse precision, otherwise ``False``
    
    COMMENT:
        The constant `c_5` is the constant `c_5` at the page 89 of the reference which is equal to the constant `c_{10}` at the page 139 of the reference.
        
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
    """
    if len([g for g in M+[m0] if g.valuation(prime) != 0]) > 0:
        raise ValueError('There is an element with non zero valuation at prime')
    
    K = prime.ring()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()
    e = prime.absolute_ramification_index()
    c5 = c3/(f * e * log(p))
    theta = K.gen()
    
    #if M is empty then it is easy to give an upper bound
    if len(M) == 0:
        if m0 != 1:
            return round(max(log(p) * f * (m0-1).valuation(prime)/c3,0)),False
        else:
            return 0,False
    #we evaluate the p-adic logarithms of m0 and we embedd it in the completion of K with respect to prime

    m0_logp = log_p(m0,prime,precision)
    m0_logp = embedding_to_Kp(m0_logp,prime,precision)
    n = len(M_logp)
    #Below we implement paragraph VI.4.2 of the reference, pages 89-93
    
    #we evaluate the order of discriminant of theta
    
    Theta = [theta**i for i in range(K.absolute_degree())]
    ordp_Disc = (K.disc(Theta)).valuation(p)
    
    #We evaluate lambda
    
    c8 = min([min([a.valuation(p) for a in g]) for g in M_logp])
    l = p**c8
    
    #we apply lemma VI.5 of Smart's book page 90
    
    low_bound = round(1/c5)
    for a in m0_logp:
        if a != 0:
            if c8 > a.valuation(p):
                B1 = (c8 + ordp_Disc/2)/c5
                if B1 > low_bound:
                    return round(B1),False
                else:
                    return low_bound,False
    
    c8 = min([a.valuation(p) for a in m0_logp]+[c8])
    B = [g/l for g in M_logp]
    b0 = m0_logp/l
    c9 = c8 + ordp_Disc/2

    #We evaluate 'u' and we construct the matrix A
    
    m = e * f
    u = round(((1 + n/m) * log(B0))/log(p))
    if u > (precision * log(2))/log(p):
        # print 'increase precision'
        return 0,True

    # print 'n * B0**2',n * B0**2
    finish = False
    while not finish:
        if u > (precision * log(2))/log(p):
            # print 'increase precision'
            return 0,True
           
        #We construct the matrix A as a block matrix
        
        A11 = copy(identity_matrix(ZZ,n))
        A12 = copy(zero_matrix(ZZ,n,m))
        A21 = copy(zero_matrix(ZZ,n,m))
        A22 = p**u * copy(identity_matrix(ZZ,m))
        for i,b in enumerate(B):
            A21[i] = vector([mod(b[j],p**u) for j in range(m)])
        A = block_matrix([[A11,A12],[A21.transpose(),A22]])

        y = copy(zero_vector(ZZ,n+m))
        for i in range(m):
            y[i+n] = -mod(b0[i],p**u)
            
        l = minimal_vector(A.transpose(),y)
        # print 'l > n * B0**2',l,n * B0**2
        if l > n * B0**2:
            B2 = (u + c9)/c5
            if B2 > low_bound:
                return round(B2),False
            else:
                return low_bound,False
        else:
            u += 1


def c_constants(G,precision):
    r"""
    
    INPUT:
        - ``G`` : a list with the generators of the free part of a subgroup of `K^*`
        - ``precision`` : the precision
    
    OUTPUT:
        The constants `c_1,c_2,c_3` that appear on the page 136 of the reference
        
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
    
    COMMENT:
        `K` has to be an absolute number field
            
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: c_constants(G,50)
            (1.6094379124341, 0.6213349,3455961, 0.20504052840467)
            
        sage: K.<a> = NumberField(x^8 + 1)
        sage: g = K.gen()
        sage: G = [g^6+g^4+g^2,-(g^4+g^3+g^2),1+g^3-g^5,1-g]
        sage: c_constants(G,80)
            (1.4497321111770749035704, 0.68978261038039241636303, 0.170721196069147)
    """
    if len(G) == 0:
        raise ValueError('G is empty')
    if len([g for g in G if g.multiplicative_order() != Infinity]) > 0:
        raise ValueError('G has an element with finite myltiplicative order')

    finiteSup,realSup,complexSup = support_of_G(G,precision)

    if len([s for s in realSup if not is_real_place(s)]) > 0:
        raise ValueError('realSup has a complex place')
    if len([s for s in complexSup if is_real_place(s)]) > 0:
        raise ValueError('complexSup has a real place')
    
    if len(realSup) > 0:
        K = realSup[0].domain()
        #infinite_prec = realSup[0].codomain().precision()
    elif len(complexSup) > 0:
        K = complexSup[0].domain()
        #infinite_prec = complexSup[0].codomain().precision()
    else:
        K = finiteSup[0].ring()
    # if not K.is_absolute():
    #     raise ValueError('K has to be an absolute extension')

    #R = RealField(prec)
    A = copy(zero_matrix(RealField(precision),len(finiteSup)+len(complexSup)+len(realSup),len(G)))

    #we create the matrix which has as rows the logarithms of the absolute value with respect a place for the lements in G
    
    #finite places
    
    for i,p in enumerate(finiteSup):
        #we have to be careful with the logarithm of 1 because sometimes does not give 0
        
        v = [0] * len(G)
        for j,g in enumerate(G):
            if (K(g)).abs_non_arch(p,prec = precision) != 1:
                v[j] = log((K(g)).abs_non_arch(p,prec = precision))
        A[i] = vector(v)
    
    #real infinite places     
        
    for i,s in enumerate(realSup):
        v = [0] * len(G)
        for j,g in enumerate(G):
            if abs(s(g)) != 1:
                v[j] = log(abs(s(g)))
        A[i + len(finiteSup)] = vector(v)
    
    #complex infinite places    
    
    for i,s in enumerate(complexSup):
        v = [0] * len(G)
        for j,g in enumerate(G):
            if abs(s(g)) != 1:
                v[j] = log(abs(s(g)))
        A[i + len(finiteSup) + len(realSup)] = vector(v)

    #We find the minimum infinite norm of all the invertible submatrices of A 

    n = len(finiteSup) + len(complexSup) + len(realSup)
    # print 'len(finiteSup), len(complexSup), len(realSup)',len(finiteSup), len(complexSup) , len(realSup)
    s = Set(range(n))
    X = s.subsets(len(G)).list()
    c1 = -Infinity
    for g in X: 
        M = A[g.list(),:] #the submatrix associate to g
        d = M.determinant()

        #if the precision is high enough the determinant of M can not be 'quite small'
        
        if d > 2**(-round(precision/2)):
            B = M.inverse()
            a = max([sum([b.abs() for b in row]) for row in M.inverse().rows()])
            if a > c1:
                c1 = a
    c2 = 1/c1
    c3 = c2/len(G)
    c3 = (99 * c3)/100
    
    return c1,c2,c3


def initial_bound_real_case(G2free,place,c3):
    r"""
    
    INPUT:
        - ``G2free`` : the generator of the free part of a finitely generated subgroup of `K^*`, where `K` is a number field
        - ``place`` (ring morhpism) : an infinite real place of `K`
        - ``c3`` : is defined in the page 136 of the reference
        
    OUTPUT:
        An upper bound associate to ``place`` according to IX.1.1 of the reference page 137
    
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: p1,p2 = K.places(prec = 50)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: c3 = 99*c1_constant(G,S,[p1],[p2])/(100*len(G))
        sage: initial_bound_real_case(G,p1,c3)
            2.7776062935760e14*log(18)*log(1.3888031467880e14*log(18)) +
            3.7656662700583*log(2)
    """
    if not is_real_place(place):
        raise ValueError('place is not real')

    c5 = log(2)/c3
    c7 = c3 
    c8 = Baker_Wustholz_low_lattice_bound([e_s_real(g,place) for g in G2free],place)
    
    return max([c5,(2 * (log(2) + c8 * log(c8/c7) ) )/c7,0])
    
    
def initial_bound_complex_case(G2free,place,g0,c3):
    r"""
    
    INPUT:
        - ``G2free`` : the generator of the free part of a finitely generated subgroup of `K^*`, where `K` is a number field
        - ``place`` (ring morhpism) : an infinite real place of `K`
        - ``g0`` : the generator of the torsion part of the group `G_2`
        - ``c3`` : is defined in the page 136 of the reference
    
    OUTPUT:
        An upper bound associate to ``place`` according to IX.1.2 of the reference page 138
    
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: p1,p2 = K.places(prec = 50)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: g0 = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() != Infinity][0]
        sage: c3 = 99*c1_constant(G,S,[p1],[p2])/(100*len(G))
        sage: initial_bound_complex_case(G,p2,g0,c3)
            2.0771265747068e23*log(30)*log(4) +
            2.0771265747068e23*log(30)*log(1.0385632873534e23*log(30)) +
            7.5313325401165*log(2)
    """
    if is_real_place(place):
        raise ValueError('place is not real')
    if g0.multiplicative_order() == Infinity:
        raise ValueError('g0 does not have finite multiplicative order')
    
    c5 = (2 * log(2))/c3
    c7 = c3/2
        
    #we find a bound for its element of the torsion part and we get the maximum among them
    
    Gtorsion = [g0**i for i in range(g0.multiplicative_order())]
    B = 0
    n = len(G2free)
    for ad in Gtorsion:
        if ad != -1:
            c8 = Baker_Wustholz_low_lattice_bound(G2free + [(-1) * ad,-1],place)
            B = max([c5,(2 * (log(2) + c8 * log(c8/c7) + c8 * log(n+1)) )/c7,B])
        else:
            c8 = Baker_Wustholz_low_lattice_bound(G2free + [-1],place)
            B = max([c5,(2 * (log(2) + c8 * log(c8/c7) + c8 * log(n+1)) )/c7,B])
        
    return B
    

def initial_bound_finite_case(G2free,prime,g0,c3,embeddings):
    r"""
    
    INPUT:
       - ``G2free`` : the generator of the free part of a finitely generated subgroup of `K^*`, where `K` is a number field
       - ``prime`` : a prime ideal of K`
       - ``g0`` : the generator of the torsion part of the group `G_2`
       - ``c3`` : is defined in the page 136 of the reference
       - ``embeddings`` : a list of all embendings of `K` to `\mathbb C`
    
    OUTPUT:
        - an upper bound associate to ``prime`` according to IX.1.3 of the reference page 139
        - a list of elements in `K^*` which contains all `\mu_0` that can appear to lemma IX.3 page 139 of the reference
        - a list of elements in `K^*` which contains all `\mu_i` for `i>0` that appear to lemma IX.3 page 139 of the reference
        - the constant `c_9` that appears to IX.1.3 of the reference page 139
    
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: p1,p2 = K.places(prec = 50)
        sage: S = K.primes_above(5)
        sage: prime = S[0]; prime
            Fractional ideal (-a^2 - 1)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: g0 = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() != Infinity][0]
        sage: c3 = 99*c1_constant(G,S,[p1],[p2])/(100*len(G))
        sage: initial_bound_finite_case(G,prime,g0,c3,[p1,p2])
            (-5.1276394965735e20*(-2.0000000000000*log(6)/log(5)^2 -
            log(2.5638197482868e20/log(5))/log(5)^2)*log(5), [-1, 1], [a - 1, a^2 -
            2*a - 1], 0.53111451110325/log(5))    
    """
             
    p = (prime.norm()).factor()[0][0]
    f = prime.residue_class_degree()
    e = prime.absolute_ramification_index()
    c9 = c3/(e * f * log(p))

    M0,M,k = a_basis_with_0_order_at_p(prime,[g0]+G2free)
    B = 0
    for m0 in M0:
        c11 , c12 = Yu_theorem([m0]+M,prime,embeddings)
        B = max([B,(2 * (c12 + c11 * log(c11/(e * c9))) )/(e * c9)])
    
    return B,M0,M
    

def is_in_G(x,G):
    r"""
    
    INPUT:
        - ``x`` : a non zero element of a number field
        - ``G`` : a list of generators of a finitely generated multiplicative subgroup of `K^*`
        
    OUTPUT:
        ``True`` if x lies in G, otherwise ``False``
    
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(15)
        sage: G = [a+1,a+2]
        sage: is_in_G((a+1)^5*(a+2),G)
            True
        sage: is_in_G(a+3,G)
            False
    """ 
    if x == 0:
        raise ValueError('x is the zero element')
    if len(G) == 0:
        raise ValueError('G is empty')
    
    K = G[0].parent()
    supp = support_of_G(G,30)[0]
    # for g in G:
    #     supp.extend([p for p in g.support() if p not in supp])
    
    SunitK = K.S_unit_group(S = supp) #G is a subgroup of SunitK
    m0 = min([g.multiplicative_order() for g in SunitK.gens()])
    m = len(SunitK.group_generators())
    k = len(G)

    #A has as rows the list of its generator of G as element of SunitK taking into account the generator
    # if the torsion part
    A = copy(zero_matrix(ZZ,k+1,m))
    
    for i,g in enumerate(G):
        A[i] = SunitK(g).list()
    A[k] = zero_vector(ZZ,m)
    A[k,0] = m0
    
    #x is in G if is in SunitK and lies in the row space of A
    
    if K.ideal(x).is_S_unit(S = supp):
        y = vector(SunitK(x).list())
        M = A.row_space()
        if y in M:
            return True
        else:
            return False
    else: 
        return False


def list_in_G(x,G):
    r"""

    INPUT:
        ``x`` : an element of a number field `K`
        ``G`` : a list of generators of a multiplicative subgroup of `K^*`

    OUTPUT:
         A vector with the exponents of ``x`` with respect to ``G``

    EXAMPLE::

        sage:
    """

    if x == 0:
        raise ValueError('x is the zero element')
    if len(G) == 0:
        raise ValueError('G is empty')

    K = G[0].parent()
    x = K(x)
    supp = support_of_G(G,30)[0]

    SunitK = K.S_unit_group(S = supp) #G is a subgroup of SunitK
    m0 = min([g.multiplicative_order() for g in SunitK.gens()])
    m = SunitK.rank()+1#len(SunitK.group_generators())
    k = len(G)

    #A has as rows the list of its generator of G as element of SunitK taking into account the generator
    # if the torsion part
    A = copy(zero_matrix(ZZ,k+1,m))
    for i,g in enumerate(G):
        A[i] = SunitK(g).list()
    A[k] = zero_vector(ZZ,m)
    A[k,0] = m0

    #x is in G if is in SunitK and lies in the row space of A

    if K.ideal(x).is_S_unit(S = supp):
        y = vector(SunitK(x).list())
        M = A.row_space()
        if y in M:
            D,U,V = A.smith_form()
            ybar = y * V
            xbar = ybar[:k] * D[:k,:k].inverse()
            return (vector(list(xbar)+[0]) * U)[:k]
        else:
            raise ValueError('x is not in G')
    else:
        raise ValueError('x is not in G')


def solutions_when_no_free_part(g0,G2):
    r"""
    
    INPUT:
        - ``g0`` : the generator of the torsion part of the group `G_1` where `x` lies
        - ``G2`` : the generators of the groups `G_2` where `y` lies
    
    OUTPUT:
        All `x` which are solutions of the S-unit equation `x+y=1`
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(2)
        sage: SK = sum([K.primes_above(p) for p in [2,3]],[])
        sage: g0 = K.unit_group().torsion_generator().value()
        sage: solutions_when_no_free_part(g0,K.S_unit_group(S = SK).gens_values())
            [-1]
            
        sage: K.<a> = CyclotomicField(19)
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: g0 = K.unit_group().torsion_generator().value()
        sage: solutions_when_no_free_part(a,K.S_unit_group(S = SK).gens_values())
            [-a^8, -a^5, -a^2, a^17 + a^16 + a^15 + a^14 + a^13 + a^12 + a^11 + a^10
            + a^9 + a^8 + a^7 + a^6 + a^5 + a^4 + a^3 + a^2 + a + 1, -a^15, -a^12,
            -a^9, -a^6, -a^3, -1, -a^16, -a^13, -a^10, -a^7, -a^4, -a, -a^17, -a^14,
            -a^11]
    """
    if g0.multiplicative_order() == Infinity:
        raise ValueError('g0 has infinity multiplicative order')
    if len(G2) == 0:
        raise ValueError('G2 is empty')
    
    solutions = []
    for x in [g0**i for i in range(g0.multiplicative_order())]:
        if x != 1:
            if is_in_G(1-x,G2):
                if x not in solutions:
                    solutions.append(x)
    return solutions


def support_of_G(G,infinite_prec):
    r"""
    
    INPUT:
        - ``G`` : a list of generators of a multiplicative subgroup of a number field `K^*`
        - ``infinite_prec`` : the preicision of the infinite places
        
    OUTPUT:
        The finite,the real infinite and complex infinite part of the support of ``G`` respectively
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[]); 
        sage: support_of_G(K.S_unit_group(S = SK).gens_values(),100)
            ([Fractional ideal (a), Fractional ideal (a + 1), Fractional ideal (-a^2
            - 1), Fractional ideal (a^2 - 2*a - 1)], 
            [Ring morphism:
              From: Number Field in a with defining polynomial x^3 - 2
              To:   Real Field with 100 bits of precision
              Defn: a |--> 1.2599210498948731647672106073], 
            [Ring morphism:
              From: Number Field in a with defining polynomial x^3 - 2
              To:   Complex Field with 100 bits of precision
              Defn: a |--> -0.62996052494743658238360530364 + 1.0911236359717214035600726142*I])
    """
    if len(G) == 0:
        raise ValueError('G is empty')
    
    K = G[0].parent()
    Krealplaces = K.real_embeddings(prec = infinite_prec)
    Kcomplexplaces = [s for s in K.places(prec = infinite_prec) if not is_real_place(s)]

    #We find the infinite_primes
    complexsup = [c for c in Kcomplexplaces if len([a for a in G if (c(a).abs()-1).abs() >= 2**(-infinite_prec/2)])>0]
    realsup = [c for c in Krealplaces if len([a for a in G if (c(a).abs()-1).abs() >= 2**(-infinite_prec/2)])>0]

    #we find the finite primes
    finitesup = []
    for g in G:
        for p in g.support():
            if p not in finitesup:
                finitesup.append(p)

    #we reorder the finite primes such that the primes which lie above the smallest rational primes are first

    rational_primes_below = [p.absolute_norm().factor()[0][0] for p in finitesup]
    for i in range(len(finitesup)):
        for j in range(i,len(finitesup)):
            if rational_primes_below[j-1] > rational_primes_below[j]:
                temp = rational_primes_below[j-1]
                rational_primes_below[j-1] = rational_primes_below[j]
                rational_primes_below[j] = temp
                # print rational_primes_below
                temp = finitesup[j-1]
                finitesup[j-1] = finitesup[j]
                finitesup[j] = temp
    return finitesup,realsup,complexsup


def reduce_the_bound_absolute_field(K,G1,G2,precision):
    r"""
    
    INPUT:
       - ``K`` : a number field
       - ``G1`` : a list of generators of a multiplicative subgroup of `K^*` where `x` lies
       - ``G2`` : a list of generators of a multiplicative subgroup of `K^*` where `y` lies
       - ``precision`` : the precision for the calculations
       
    OUTPUT:
        All the solutions `x` of the `S-unit` equation `x+y=1` when `x\in G_1` and `y\in G_2`
        
    COMMENT:
        K has to be a absolute field

    EXAMPLE::
        
        sage: 
    
    """
    if len(G1) == 0:
        raise ValueError('G1 is the empty list')
    if len(G2) == 0:   
         raise ValueError('G2 is empty list')
    
    Kplaces = K.places(prec = precision)
    Krealplaces = K.real_embeddings(prec = precision)
    Kcomplexplaces = [s for s in Kplaces if not is_real_place(s)]
    Kembeddings = Krealplaces + Kcomplexplaces

    finiteSup1, realSup1, complexSup1 = support_of_G(G1,precision)
    finiteSup2, realSup2, complexSup2 = support_of_G(G2,precision)
         
    #the generators for the free part of each G1 and G2
           
    G1free = [g for g in G1 if g.multiplicative_order() == Infinity]
    G2free = [g for g in G2 if g.multiplicative_order() == Infinity]
    
    lenG1free = len(G1free)
    lenG2free = len(G2free)
    
    #the generator of the torsion part of G1 and G2
    
    if len([g for g in G1 if g.multiplicative_order() != Infinity]) > 0:
        g01 = [g for g in G1 if g.multiplicative_order() != Infinity][0]
    else:
        g01 = K(1)
        
    if len([g for g in G2 if g.multiplicative_order() != Infinity]) > 0:
        g02 = [g for g in G2 if g.multiplicative_order() != Infinity][0]
    else:
        g02 = K(1)
        
    #Since both groups have the same torsion part we define a global torsion

    if lenG1free == 0:
        return 0#,solutions_when_no_free_part(g01,G2)
    elif lenG2free == 0:
        return 0#,solutions_when_no_free_part(g02,G1)

    G1c1 ,G1c2, G1c3= c_constants(G1free,precision)
    G2c1,G2c2, G2c3 = c_constants(G2free,precision)
    c1 = max([G1c1,G2c1])

    S1 = finiteSup1+complexSup1+realSup1
    S2 = finiteSup2+complexSup2+realSup2
    
    ##  STEP 1 - Initial bound  ##
    
    #Calculating initial bound for the real case
    
    G1B1real = max([initial_bound_real_case(G2free,prime,G1c3) for prime in realSup1] + [0])
    G2B1real = max([initial_bound_real_case(G1free,prime,G2c3) for prime in realSup2] + [0])
    B1real = max(G1B1real,G2B1real)
    # print('B1real',B1real)
    
    #Calculating initial bound for the complex case
    
    G1B1complex = max([initial_bound_complex_case(G2free,prime,g02,G1c3) for prime in complexSup1] + [0])
    G2B1complex = max([initial_bound_complex_case(G1free,prime,g01,G2c3) for prime in complexSup2] + [0])
    B1complex = max(G1B1complex,G2B1complex)
    # print('B1complex',B1complex.n(21))
    
    #Calculating initial bound for the finite case and objects we need for the reduction step
    
    G1B1finite = 0
    G1finite_initialization = []
    for prime in finiteSup1:
        B1, M0, M= initial_bound_finite_case(G2free,prime,g02,G1c3,Kembeddings)
        G1finite_initialization.append([prime, M0, M])
        G1B1finite = max(G1B1finite,B1)
        
    G2B1finite = 0 
    G2finite_initialization = []
    for prime in finiteSup2:
        B1, M0, M = initial_bound_finite_case(G1free,prime,g01,G2c3,Kembeddings)
        G2finite_initialization.append([prime, M0, M])
        G2B1finite = max(G2B1finite,B1)
    B1finite = max(G1B1finite,G2B1finite)
    B1 = RR(max(B1real,B1complex,B1finite)).floor()
    # print 'B1',RR(B1).floor()
    
    # print 'step 1'
    ##  STEP 2 - Reduction step  ##
    
    # Real case
    # print 'real'

    # print 'G1'
    #G1
    G1B2real = 0
    for place in realSup1:
        Bold = B1
        finish = False
        while not finish:
            Bnew , increase_precision = reduction_step_real_case(place,Bold,G2free,G1c3)
            
            #if we have to increase the precision we evaluate c1,c2,c3 constants again

            if not increase_precision:
                if Bnew < Bold:
                    Bold = Bnew
                else:
                    finish = True
            else:
                #we evaluate with higher precision G1c1 , G1c2 and G1c3

                temp_finiteSup1, temp_realSup1, temp_complexSup1 = support_of_G(G1,2*place.codomain().precision())
                G1c1 ,G1c2, G1c3 = c_constants(G1free,2*place.codomain().precision())
                place = higher_precision(place,2*place.codomain().precision())
                      
        G1B2real = max(G1B2real,Bold)

    #print 'G2'
    #G2
    G2B2real = 0
    for place in realSup2:
        Bold = B1
        finish = False
        while not finish:
            Bnew , increase_precision = reduction_step_real_case(place,Bold,G1free,G2c3)
            
            #if we have to increase the precision we evaluate c1,c2,c3 constants again

            if not increase_precision:
                if Bnew < Bold:
                    Bold = Bnew
                else:
                    finish = True
            else:
                #we evaluate with higher precision G2c1 , G2c2 and G2c3
                
                temp_finiteSup2, temp_realSup2, temp_complexSup2 = support_of_G(G2,2*place.codomain().precision())
                G2c1 ,G2c2, G2c3 = c_constants(G2free,2*place.codomain().precision())
                place = higher_precision(place,2*place.codomain().precision())
                      
        G2B2real = max(G2B2real,Bold)
    B2real = max(G1B2real,G2B2real)
    
    #  Complex case
    # print 'complex'

    #print 'G1'
    #G1
    G1B2complex = 0
    for place in complexSup1:
        B_place = 0
        for g0 in [g02**i for i in range(g02.multiplicative_order())]:
            Bold_g0 = B1
            finish = False
            while not finish:
                Bnew_g0 ,increase_precision = reduction_step_complex_case(place,Bold_g0,G2free,g0,G1c3/2)
                #print 'Bnew,Bold',round(Bnew_g0),round(Bold_g0),increase_precision
                #if we have to increase the precision we evaluate c1,c2,c3 constants again
                if not increase_precision:
                    if Bnew_g0 < Bold_g0:
                        Bold_g0 = Bnew_g0
                    else:
                        finish = True
                else:
                    #we evaluate with higher precision G1c1 , G1c2 and G1c3
                
                    temp_finiteSup1, temp_realSup1, temp_complexSup1 = support_of_G(G1,2*place.codomain().precision())
                    G1c1 ,G1c2, G1c3 = c_constants(G1free,2*place.codomain().precision())
                    place = higher_precision(place,2*place.codomain().precision())
            B_place = max(B_place,Bold_g0)
        G1B2complex = max(G1B2complex,B_place)

    #print 'G2'
    #G2
    G2B2complex = 0
    for place in complexSup2:
        B_place = 0
        for g0 in [g01**i for i in range(g01.multiplicative_order())]:
            Bold_g0 = B1
            finish = False
            while not finish:
                Bnew_g0 ,increase_precision = reduction_step_complex_case(place,Bold_g0,G1free,g0,G2c3/2)
                #print 'Bnew,Bold',round(Bnew_g0),round(Bold_g0),increase_precision
                #if we have to increase the precision we evaluate c1,c2,c3 constants again
                if not increase_precision:
                    if Bnew_g0 < Bold_g0:
                        Bold_g0 = Bnew_g0
                    else:
                        finish = True
                else:
                    #we evaluate with higher precision G2c1 , G2c2 and G2c3
                
                    temp_finiteSup2, temp_realSup2, temp_complexSup2 = support_of_G(G2,2*place.codomain().precision())
                    G2c1 ,G2c2, G2c3 = c_constants(G2free,2*place.codomain().precision())
                    place = higher_precision(place,2*place.codomain().precision())
            B_place = max(B_place,Bold_g0)
        G2B2complex = max(G2B2complex,B_place)
    B2complex = max(G1B2complex,G2B2complex)

    #  Finite case
    # print 'finite'
    # print 'G1'
    # import time
    #G1
    G1B2finite = 0
    # return G1finite_initialization
    # print 'len(G1finite_initialization)',len(G1finite_initialization)
    for P in G1finite_initialization:
        # print 'len(P[1])',len(P[1])
        # print 'B1',B1
        SunitK = K.S_unit_group(S = support_of_G(P[2],10)[0])
        B_place = 0
        prec = precision
        # start = time.time()
        M_logp = [sum([c * log_p(g,P[0],prec) for c,g in zip(SunitK(m).list(),SunitK.gens_values()) if c != 0]) for m in P[2]]
        M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
        # end = time.time()
        # print 'time for initial logp',end-start
        for m0 in P[1]:
            # print 'm0'
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
                    # print 'increase precision'
                    prec *= 2
                    G1c1 ,G1c2, G1c3 = c_constants(G1free,prec)
                    # start = time.time()
                    M_logp = [sum([c * log_p(g,P[0],prec) for c,g in zip(SunitK(m).list(),SunitK.gens_values()) if c != 0]) for m in P[2]]
                    M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
                    # end = time.time()
                    # print 'time for increase logp',end-start
            B_place = max(B_place,Bold_m0)
        G1B2finite = max(G1B2finite,B_place)

    # print 'G2'
    #G2
    G2B2finite = 0
    for P in G2finite_initialization:
        B_place = 0
        prec = precision
        M_logp = [log_p(m,P[0],prec) for m in P[2]]
        M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
        for m0 in P[1]:
            Bold_m0 = B1
            finish = False
            while not finish:
                
                Bnew_m0,increase_precision = reduction_step_finite_case(P[0],Bold_m0,P[2],M_logp,m0,G2c3,prec)

                #if we have to increase the precision we evaluate c1,c2,c3 constants again
                if not increase_precision:
                    if Bnew_m0 < Bold_m0:
                        Bold_m0 = Bnew_m0
                    else:
                        finish = True
                else:
                    #we evaluate with higher precision G2c1 , G2c2 and G2c3
                    prec *= 2
                    G2c1 ,G2c2, G2c3 = c_constants(G2free,prec)
                    M_logp = [log_p(m,P[0],prec) for m in P[2]]
                    M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
            B_place = max(B_place,Bold_m0)
        G2B2finite = max(G2B2finite,B_place)
    B2finite = max(G1B2finite,G2B2finite)

    return RR(max(B2real,B2complex,B2finite)).floor()


def reduce_the_bound(K,G1,G2,precision):
    r"""

    INPUT:
       - ``K`` : a number field
       - ``G1`` : a list of generators of a multiplicative subgroup of `K^*` where `x` lies
       - ``G2`` : a list of generators of a multiplicative subgroup of `K^*` where `y` lies
       - ``precision`` : the precision for the calculations

    OUTPUT:
        An upper bound for the exponents of the solutions `x,y` of the `S-unit` equation `x+y=1` when `x\in G_1` and `y\in G_2`

    EXAMPLE::

        sage:

    """
    if len(G1) == 0:
        raise ValueError('G1 is the empty list')
    if len(G2) == 0:
         raise ValueError('G2 is empty list')

    if K.is_absolute():
        return reduce_the_bound_absolute_field(K,G1,G2,precision)
    else:
        Kabs = K.absolute_field('b')
        KembKabs = K.embeddings(Kabs)[0]
        G1abs = [KembKabs(g) for g in G1]
        G2abs = [KembKabs(g) for g in G2]
        return reduce_the_bound_absolute_field(Kabs,G1abs,G2abs,precision)

#### Norm subgroups for all 2-division fields####

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
  
###### Sieve step ######
      
def congruence_mod_p(G,prime,n,B):
    r"""
    
    INPUT:
        - ``G`` : a list `[g_0,g_1,\cdots,g_k]` of generators of a subgroup of `K^*` for a number field `K`
        - ``prime`` : a prime ideal `\mathfrak p` of `K`
        - ``n`` : a natural number
        - ``B`` : a natural number
    
    COMMENT:
        The `g_i` have to be coprime to the ideal `\mathfrak p`. The bound for the exponent of `g_0` is 1.
        
    OUTPUT:
        A list of all elements `g` of `G` such that `g\equiv 1\mod \mathfrak p^n` and `\displaystyle\max_{i=0,\cdots, k}\lbrace\mid a_i\mid\rbrace\leq B` if `g=\displaystyle\prod_{i=0}^{k}g_i^{a_i}`
    
    EXAMPLE::
        
        sage: con
    """
    import time
    
    if len([g for g in G if g.valuation(prime) != 0]) > 0:
        raise ValueError('Not all elements of G are coprime to prime')
    
    K = prime.ring()
    Tbounds = [Infinity] * len(G)
    h0 = min([g.multiplicative_order() for g in G])
    for i in range(1,n):
        I = prime**i
        Ostar = I.idealstar()
        if Ostar.order() > 1:
            M = matrix(ZZ,len(G),sum([I.ideallog(g) for g in G],[]))
            N = diagonal_matrix(Ostar.gens_orders())
            A = block_matrix([[M],[N]])
            C = A.kernel().matrix()[:len(G),:len(G)]
            A = C.inverse()
            for j,col in enumerate(A.columns()):
                Tbounds[j] = min(round(vector(col[1:len(col)]).norm(1) * B+col[0].abs()*h0),B,Tbounds[j])
    
    #print 'Tbounds',Tbounds
    #for v in cartesian_product_iterator([xrange(-b,b+1) for b in Tbounds[1:len(Tbounds)]]):
    #    lam = G[0] * prod([g**e for g,e in zip(G[1:len(G)],v)])
    #    if lam !=0 and lam !=1:
            #start = time.time()
    #        print j_invariant(lam) == j_invariant(1-lam)
            #end = time.time()
            #print end - start
    #        if j_invariant(lam) == j_invariant(1-lam):
    #            if j_invariant(lam) in QQ:
    #                print 'j_invariant(lam)',j_invariant(lam)
            #end = time.time()
            #print end - start
    return Tbounds


###### Pacetti's method ######

def bounds_for_discriminant_over_QQ_single_field(K,B,Gl,Gm,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``B`` : an upper bound for the exponents of ``Gl`` and ``Gm``
        - ``Gl`` : a list of generators of the subgroup of `K^*` where `\lambda` lies
        - ``Gl`` : a list of generators of the subgroup of `K^*` where `\mu` lies
        - ``S`` : the finite list of rational prime
        
    OUTPUT:
        A list with upper bounds for each prime in ``S``
        
    EXAMPLE::
        
        sage: K.<a>
    """    
    if len(S) == 0 or len(Gl) == 0 or len(Gm) == 0:
        raise ValueError('Gl,Gm or S is empty')
    
    Bounds = []
    for p in S:
        P = K.primes_above(p)
        bound = Infinity
        for pr in P:
            e = pr.absolute_ramification_index()
            if len([g for g in Gl if g.valuation(pr) != 0]) == 0 and len([g for g in Gm if g.valuation(pr) != 0]) == 0:
                if p != 2 and p != 3:
                    u = 6
                elif p == 3:
                    u = 12
                else:
                    u = 10
            else:
                um = vector([g.valuation(pr) for g in Gm]).norm(1) * B
                ul = vector([g.valuation(pr) for g in Gl]).norm(1) * B
                u = max(um,ul)
                if p != 2 and p != 3:
                    u = 2 * (u/e + 3)
                elif p == 3:
                    u = 2 * (u/e + 3/2)
                else:
                    u = max(11,2 * (u/e + 6))
            bound = min(bound,u)
        Bounds.append(bound)
    
    return Bounds
    
    
def bounds_for_discriminant_over_QQ(S):
    r"""
    
    INPUT:
        - ``S`` : a finite list of primes
        
    OUTPUT:
        For each potential 2-division field a list of bounds for the exponents of the primes in `S`, together with field and the bound for the exponents of the associate `\lambda` and `\mu`.
        
    """
    import time 
    K = NumberField(x-1,'a')
    SK = sum([K.primes_above(pr) for pr in S],[])
    fields = two_division_fields(K,SK)
    print 'S=%s'%(S)
    
    # C2 case
    print 'C2 case'
    
    for M in fields[0]:
        SM = sum([M.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SM)
        M2 = M.absolute_field('m2')
        emb = M.embeddings(M2)[0]
        start = time.time()
        B = reduce_the_bound(M2,[emb(g) for g in Gl],[emb(g) for g in Gm],200)
        end = time.time()
        print 'f=%s, bounds=%s, B=%s, rank=%s and time=%s'%(M.defining_polynomial(),bounds_for_discriminant_over_QQ_single_field(M,B,Gl,Gm,S),B,min(len(Gl)-1,len(Gm)-1),end-start)
        
    # C3 case
    print 'C3 case'
    
    for M in fields[1]:
        SM = sum([M.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SM)
        M2 = M.absolute_field('m2')
        emb = M.embeddings(M2)[0]
        start = time.time()
        B = reduce_the_bound(M2,[emb(g) for g in Gl],[emb(g) for g in Gm],200)
        end = time.time()
        print 'f=%s, bounds=%s, B=%s, rank=%s and time=%s'%(M.defining_polynomial(),bounds_for_discriminant_over_QQ_single_field(M,B,Gl,Gm,S),B,min(len(Gl)-1,len(Gm)-1),end-start)
        
    
    # S3 case
    print 'S3 case'
    
    for i,M in enumerate(fields[3]):
        SM = sum([M.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SM)
        M2 = M.absolute_field('m2')
        emb = M.embeddings(M2)[0]
        #return M2,emb,Gl,Gm
        start = time.time()
        B = reduce_the_bound(M2,[emb(g) for g in Gl],[emb(g) for g in Gm],200)
        end = time.time()
        print 'f=%s, bounds=%s, B=%s, rank=%s and time=%s'%(fields[2][i],bounds_for_discriminant_over_QQ_single_field(M,B,Gl,Gm,S),B,min(len(Gl)-1,len(Gm)-1),end-start)
    
    
#### S-unit, determine small solutions ####

##### REFERENCES #####
      
#[3] N.P.SMART, Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999


def evaluate_R0(B,G,S1,precision):
    r"""
    
    INPUT:
        - ``B`` : a bound for the exponents
        - ``G`` : a list of generators of a subgroup of `K^*`
        - ``S1`` : the support of G
        - ``precision`` : the precision 
        
    OUTPUT:
        A parameter `R_0` which is mentioned in lemma 1 of the reference
        
    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999
    
    EXAMPLE::
        
        sage: L.<a> = NumberField(x^6 + 84*x^4 + 994*x^3 + 21609*x^2 + 2058*x + 266854)
        sage: G = [-1/73500*a^5-1/283500*a^4-7/8100*a^3-1313/94500*a^2-1886/10125*a+5311/20250,-1/396900*a^5-
            1/18900*a^4-19/11340*a^3-737/56700*a^2-2/225*a+13/4050,-4/297675*a^5-1/17010*a^4-47/85050*a^3-
            659/42525*a^2-1862/6075*a-2057/6075]
        sage: prec = 80
        sage: finite,real,complex = support_of_G(G,prec)
        sage: evaluate_R0(353,G,finite+real+complex,prec)
            1.4750496337890720688172e658
    """   
    from sage.rings.number_field.number_field_ideal import NumberFieldFractionalIdeal    
    
    if is_NumberFieldFractionalIdeal(S1[0]):
        K = S1[0].ring()
    else:
        K = S1[0].domain()
    
    e = 0
    for p in S1:
        if is_NumberFieldFractionalIdeal(p):
            e_new = sum([(log(K(a).abs_non_arch(p,prec = precision))).abs() for a in G])
        elif is_real_place(p):
            e_new = sum([(log(p(a).abs())).abs() for a in G])
        else:
            e_new = sum([2 * (log(p(a).abs())).abs() for a in G])
        e = max(e,e_new)   
    return exp(B * e)


def mix_basis(G1,G2):
    r"""
    
    INPUT:
        - ``G1`` : a list of generators of a subgroup of `K^*` for a number field `K`
        - ``G2`` : a list of generators of a subgroup of `K^*` for a number field `K`
        
    OUTPUT:
        A list of generators for the group `G_1\times G_2`.
        
    EXAMPLE::
        
       sage:  
    """
    from sage.rings.number_field.number_field_ideal import NumberFieldFractionalIdeal
    K = G1[0].parent()
    S1 = sum([L.primes_above(g) for g in G1],[])
    S2 = sum([L.primes_above(g) for g in G2],[])
     
    S12 = []
    for p in S1+S2:
        if p not in S12:
            S12.append(p)
    
    SunitK = K.S_unit_group(S = S12)
    A = copy(zero_matrix(ZZ,len(G1+G2),SunitK.rank()+1))

    for i,g in enumerate(G1+G2):
        A[i] = vector(SunitK(g).list())
    
    U,S,T = A.smith_form()
    M = U * T.inverse()
    G12 = []
    for m in M.rows():
        g = SunitK.exp(m)
        if g != 1:
            G12.append(g)
    
    #t = max([sum([a.abs() for a in s]) for s in S.inverse().columns()])      
        
    return G12#,t


def trivial_Tp_infinite_place(bounds,place,G,delta):
    r"""
    
    INPUT:
        - ``bounds`` : a list of upper bounds for the exponents of the generators
        - ``place`` (ring morphism): an infinite place `\mathfrak p` of a number field `K`
        - ``G`` : a list `[g_1,g_2,\cdots,g_n]` of elements of `K^*` which are linear independent
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
    # print 'trivial Tp infinite'
    K = place.domain()
    precision = place.codomain().precision()
    real_place = is_real_place(place)

    if real_place:
        delta_prime = -log(1-delta)
    else:
        delta_prime = -log(1-sqrt(delta))/2
        
    #we choose C such that none of the elements of the lowest row of the matrix A we define later to be 0
    if real_place:
        C = max([round(1/log(place(g).abs()))+1 for g in G]+[2])
    else:
        C = max([round(1/log(place(g).abs()**2))+1 for g in G]+[2])
    t = len(G)
    C_upper = C**10000 # arbitrary choice
    A = copy(identity_matrix(ZZ,t))
    
    if precision < log(C)/log(2):
        place = higher_precision(place,2 * precision)
    
    y = zero_vector(ZZ,t)
    finish = False
    while not finish:
        if real_place:
            A[t-1] = vector([round(log(place(g).abs())*C) for g in G])
            if A[t-1,t-1].is_zero():
                i,x = [[i,a] for i,a in enumerate(A[t-1]) if not a.is_zero()][0]
                A[t-1,t-1] = x
                A[t-1,i] = 0
                temp = bounds[i]
                bounds[i] = bounds[t-1]
                bounds[t-1] = temp
        else:
            A[t-1] = vector([(log(place(g).abs()**2) * C).round() for g in G])
            if A[t-1,t-1].is_zero():
                i,x = [[i,a] for i,a in enumerate(A[t-1]) if not a.is_zero()][0]
                A[t-1,t-1] = x
                A[t-1,i] = 0
                temp = bounds[i]
                bounds[i] = bounds[t-1]
                bounds[t-1] = temp

        l = minimal_vector(A.transpose(),y)
        if l <= sum([b**2 for b in bounds[:t-1]]) + (sum([b for b in bounds]) + C * delta_prime)**2:
            C = 10 * C
            if C <= C_upper:
                if precision < log(C)/log(2):
                    place = higher_precision(place,2 * precision)
            else:
                finish = True
        else:
            return True    
    
    return False


def trivial_Tp_finite_place(B,prime,M0,M,M0_logp,M_logp,delta,precision):
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
    # print 'new trivial Tp finite'
    if len([m for m in M+M0 if m.valuation(prime) != 0]) > 0:
        raise ValueError('There is an element without non zero valuation at prime') 
    K = prime.ring()
    theta = K.gen()
    e = prime.absolute_ramification_index() 
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()
    
    delta_prime = -log(delta)/(e*f*log(p))
    if delta_prime < 1:
        return False, M0_logp,M_logp,precision
    M_logp_emb = [embedding_to_Kp(m,prime,precision) for m in M_logp]
    M0_logp_emb = [embedding_to_Kp(m0_logp,prime,precision) for m0_logp in M0_logp]
    n = e * f
    s = len(M)
    u = round((1 + s/n) * log(B)/log(p))

    #nothing changes if we take the valuation of the global field instead of its completion
    ordp_Disc = (K.disc([theta**i for i in range(K.degree())])).valuation(p)

    c5 = delta_prime-ordp_Disc/2

    for k in range(len(M0_logp_emb)):
        m0_logp_emb = M0_logp_emb[k]
        c6 = min([min([a.valuation(p) for a in v]) for v in M_logp_emb+[m0_logp_emb]])
        c7 = c5-c6
        lam = p**c6
        T = [[v[i]/lam for i in range(n)] for v in M_logp_emb]
        T0 = [m0_logp_emb[i]/lam for i in range(n)]

        finish = False
        while not finish:
            if u <= precision:
                if u > c7:
                    return False, M0_logp,M_logp,precision
                A11 = copy(identity_matrix(ZZ,s))
                A12 = copy(zero_matrix(ZZ,s,n))
                A21 = copy(zero_matrix(s,n))
                A22 = p**u *copy(identity_matrix(ZZ,n))
                y = vector(ZZ,n+s)
                for i in range(s):
                    A21[i] = vector([mod(a,p**u) for a in T[i]])
                for i in range(n):
                    y[s+i] = -mod(T0[i],p**u)
                A = block_matrix([[A11,A12],[A21.transpose(),A22]])
                l = minimal_vector(A.transpose(),y)
                if l > s * B**2:
                    finish = True
                else:
                    u += 1
            else:
                precision *= 2
                M_logp = [log_p(m,prime,precision) for m in M]
                M_logp_emb = [embedding_to_Kp(m,prime,precision) for m in M_logp]
                M0_logp = [log_p(m0,prime,precision) for m0 in M0]
                M0_logp_emb = [embedding_to_Kp(m0_logp,prime,precision) for m0_logp in M0_logp]
                m0_logp_emb = M0_logp_emb[k]
                c5 = delta_prime-ordp_Disc/2
                c6 = min([min([a.valuation(p) for a in v]) for v in M_logp_emb+[m0_logp_emb]])
                c7 = c5-c6
                lam = p**c6
                T = [[v[i]/lam for i in range(n)] for v in M_logp_emb]
                T0 = [m0_logp_emb[i]/lam for i in range(n)]

    return True,M0_logp,M_logp,precision


def non_trivial_Tp_infinite_case(K,place,G,S,R,r,delta,prec_finite,prec_infinite):
    
    #  --INPUT--
    #K = a number field
    #place = an infinite place
    #G = a set of elements in K which are multiplicative indepedent 
    #S = the support of G
    #R = a rean number greater than 1
    #r = an element in K*
    #delta = a real number less than 1
    #prec_finite = precision for finite places
    #prec_infinite = precision for infinite places
    
    
    #  --OUTPUT--
    #Sol = a list with some solutions of the S-unit equation
    
    if is_real_place(place):
        print 'place is real'
    else:
        print 'place is complex'
    
    zeta=K.unit_group().torsion_generator()        
    d2=arccos(sqrt(1-delta))
    t=len(G)
    n=len(S)
    
    A=copy(zero_matrix(RealField(prec=prec_infinite),n+1,t+2))
    y=zero_vector(RealField(prec=prec_infinite),t+2)
    for i,p in enumerate(S):
        if is_NumberFieldFractionalIdeal(p):
            e=p.ramification_index()
            A[i]=(e*vector([log(g.abs_non_arch(p,prec_finite)) for g in G]+[0,0]))/log(R)
            y[i]=-e*log(r.abs_non_arch(p,prec_finite))/log(R)
        elif is_real_place(place):
            A[i]=vector([log(place(g).abs()) for g in G]+[0,0])
            y[i]=-log(place(r).abs())
            if p==place:
                d1=log(1/(1-delta))
                A[i]=A[i]/d1
                y[i]=y[i]/d1
            else:
                A[i]=A[i]/log(R)
                y[i]=y[i]/log(R)
        else:
            A[i]=vector([2*log(place(g).abs()) for g in G]+[0,0])
            y[i]=-2*log(place(r).abs())
            if p==place:
                d1=log(1/(1-sqrt(delta)))/2
                A[i]=A[i]/d1
                y[i]=y[i]/d1
            else:
                A[i]=A[i]/log(R)
                y[i]=y[i]/log(R)
    
    complex=ComplexField(prec=prec_infinite)
    real=RealField(prec=prec_infinite)
    A[n]=vector([complex(place(g)).argument() for g in G]+[complex(place(zeta)).argument(),-2*pi])/d2
    y[n]=complex(place(1/r)).argument()/d2
    
    #C is a bound for the square of the norm of A*x
    
    C=(sqrt(n+1)+y.norm())^2
    Cprime=n+1
    print 'C',C
    print 'Cprime',Cprime
    #c4,singular=minimal_vector(A.transpose(),y)
    #print 'c4',c4
    B=2*A.transpose()*A
    
    #print pari(B)
    #print 'B',B
    X=pari(B).qfminim(flag=2).python()
    #v=vector(X[2])
    print 'X',X
    #print (A*X[2]).norm()
                    
    return B        


#I don't use this
def reduce_bound_with_sieve(K,B2,G1,G2,c1,precision):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``B2`` : an upper bound for the exponents
        - ``G1`` : a list of generators of a multiplicative subgroup of `K^*` where `x` lies
        - ``G2`` : a list of generators of a multiplicative subgroup of `K^*` where `y` lies
        - ``c1`` : real positive number as it is mentioned in the Notation paragraph of the reference
        - ``precision`` : the precision for the calculations
    
    OUTPUT:
        All pairs `(x,y)\in G_1\times G_2` such that `x+y=1`
        
    COMMENT:
        This is an implementation of the paper in the reference
        
    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999
    
    EXAMPLE::
        
        sage: K.<a>
    """    
    from sage.rings.number_field.number_field_ideal import is_NumberFieldFractionalIdeal
    
    #finiteSup1,realSup1,complexSup1 = support_of_G(G1,precision)
    #finiteSup2,realSup2,complexSup2 = support_of_G(G2,precision)
    S1 = sum(support_of_G(G1,precision),[])#finiteSup1 + realSup1 + complexSup1
    S2 = sum(support_of_G(G2,precision),[])#finiteSup2 + realSup2 + complexSup2
    g01 = [g for g in G1 if g.multiplicative_order() != Infinity][0]
    g02 = [g for g in G2 if g.multiplicative_order() != Infinity][0]
    G1free = [g for g in G1 if g.multiplicative_order() == Infinity]
    G2free = [g for g in G2 if g.multiplicative_order() == Infinity]
    
    #we evaluate R0
    R0 = evaluate_R0(B2,G1,S1,precision)
    
    #S12 = S1
    #for p in S2:
        #if p not in S12:
            #S12.append(p)
    
    #G12 = mix_basis(G1,G2)
    #G12free = [g for g in G12 if g.multiplicative_order() == Infinity]
    #g012 = [g for g in G12 if g.multiplicative_order() != Infinity][0]
    solutions = []
    end = False
    #print 'len(S12)',len(S12)
    
    while not end:
    
        R1 = R0**(1/4)
        #T1 and T2 sets together 
        
        for place in S2:
            if not is_NumberFieldFractionalIdeal(place):
                finish = False
                while not finish and R1 < R0:
                    if trivial_Tp_infinite_place(B2,place,G1free,1/(1+R1)):
                        finish = True
                    else:
                        R1 = 2 * R1
            else:
                if place in S1:
                    M0, M ,k= a_basis_with_0_order_at_p(place,G1)
                    for m0 in M0:
                        finish = False
                        while not finish and R1 < R0:
                            if trivial_Tp_finite_place(B2,place,m0,M,1/(1+R1),precision):
                                finish = True
                            else:
                                R1 = 2 * R1
                  
                else:
                    finish = False
                    while not finish and R1 < R0:
                        if trivial_Tp_finite_place(B2,place,g01,G1free,1/(1+R1),precision):
                            finish = True
                        else:
                            R1 = 2 * R1
        
        
        for i,place in enumerate(S2):
            print 'R1',R1
            #print 'i place',i,is_NumberFieldFractionalIdeal(place)
            if not is_NumberFieldFractionalIdeal(place):
                finish = False
                while not finish and R1 < R0:
                    if trivial_Tp_infinite_place(B2,place,G1free,1/(1+R1)):
                        finish = True
                    else:
                        R1 = 2 * R1
            else:
                M0, M ,k= a_basis_with_0_order_at_p(place,G1)
                for m0 in M0:
                    finish = False
                    while not finish and R1 < R0:
                        if trivial_Tp_finite_place(B2,place,m0,M,1/(1+R1),precision):
                            finish = True
                        else:
                            R1 = 2 * R1
                
        
        
        return round(c1 * log(R1+1))
        #T3 set
    
        for place in S1:
            if not is_NumberFieldFractionalIdeal(place):
                if trivial_Tp_infinite_place(B2,place,G2,1/R1,precision):
                    ola=1
                    #print 'No solutions for T3-infinite'
                else:
                    #print 'potential solutions T3-infinite'
                    finish=true
            else:
                for tor in G1torsion:
                    M0,M,k=a_basis_with_0_order_at_p(K,place,G2,-tor,e,f)
                    for m0 in M0:
                        if trivial_Tp_finite_place(B2,K,place,M,s1/R1,m0,p,e,f,prec_finite):
                            ola=1
                            #print 'No solutions for T3-finite'
                        else:
                            #print 'potential solutions T3-finite'
                            finish=False#True
                        
                        
        #T4 set
    
        for place in S1:
            if is_NumberFieldFractionalIdeal(place)==False:
                for a in G12torsion:
                    if trivial_Tp_infinite_place(t*B2,K,place,G_mix,s1/R1,-a,prec_infinite):
                        ola=1
                        #print 'No solutions for T4-infinite'
                    else:
                        #print 'potential solutions T4-infinite'
                        finish=true
            else:
                e=place.ramification_index()
                f=place.residue_class_degree()
                p=place.norm().factor()[0][0]
                for a in G12torsion:
                    M0,M,k=choice_a_basis_with_0_order_at_p(K,place,G_mix,-a,e,f)
                    for m0 in M0:
                        if trivial_Tp_finite_place(B2,K,place,M,1/(1+s1*R1),m0,p,e,f,prec_finite):
                            ola=1
                            #print 'No solutions for T4-finite'
                        else:
                            #print 'potential solutions T4-finite'
                            finish=False#True
        
        c2 = max([log(s(R1+1)),log((s1*R1+1)/s3),log(R1)])
        print 'c1,c2-',c1,c2
        B2=min([c1*c2,B2])
        print 'B2',B2           
        R0=R1
    return s1,s2,s3
   

def determine_small_solutions_for_elliptic_curves(K,B2,Gl,Gm,c1,precision):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``B2`` : an upper bound for the exponents
        - ``Gl`` : a list of generators of a multiplicative subgroup of `K^*` where `x` lies
        - ``Gm`` : a list of generators of a multiplicative subgroup of `K^*` where `y` lies
        - ``c1`` : real positive number as it is mentioned in the Notation paragraph of the reference
        - ``precision`` : the precision for the calculations
    
    OUTPUT:
        All pairs `(x,y)\in G_\lambda\times G_\mu` such that `x+y=1`
        
    COMMENT:
        This is an implementation of the paper in the reference
        
    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999
    
    EXAMPLE::
        
        sage: K.<a>
    """    
    from sage.rings.number_field.number_field_ideal import is_NumberFieldFractionalIdeal
    
    finiteSup1,realSup1,complexSup1 = support_of_G(Gl,precision)
    finiteSup2,realSup2,complexSup2 = support_of_G(Gm,precision)
    Sl = finiteSupl + realSupl + complexSupl
    Sm = finiteSupm + realSupm + complexSupm
    gl0 = [g for g in Gl if g.multiplicative_order() != Infinity][0]
    gm0 = [g for g in Gm if g.multiplicative_order() != Infinity][0]
    Glfree = [g for g in Gl if g.multiplicative_order() == Infinity]
    Gmfree = [g for g in Gm if g.multiplicative_order() == Infinity]
    
    #we evaluate R0
    R0 = evaluate_R0(B2,Gl,S1,precision)
    
    Slm = Sl
    for p in Sm:
        if p not in Slm:
            Slm.append(p)
    
    Glm = mix_basis(Gl,Gm)
    Glmfree = [g for g in Glm if g.multiplicative_order() == Infinity]
    glm0 = [g for g in Glm if g.multiplicative_order() != Infinity][0]
    solutions = []
    end = False
    #print 'len(Slm)',len(Slm)
    
    while not end:
            
        R1 = R0**(1/4)
        #T1 and T2 sets together 
        
        for i,place in enumerate(Slm):
            print 'R1',R1
            #print 'i place',i,is_NumberFieldFractionalIdeal(place)
            if not is_NumberFieldFractionalIdeal(place):
                finish = False
                while not finish and R1 < R0:
                    if trivial_Tp_infinite_place(B2,place,Glfree,1/(1+R1)):
                        finish = True
                    else:
                        R1 = 2 * R1
            else:
                M0, M ,k= a_basis_with_0_order_at_p(place,Gl)
                for m0 in M0:
                    finish = False
                    while not finish and R1 < R0:
                        if trivial_Tp_finite_place(B2,place,m0,M,1/(1+R1),precision):
                            finish = True
                        else:
                            R1 = 2 * R1
                
        return round(c1 * log(R1+1))
        
        c2 = max([log(s(R1+1)),log((s1*R1+1)/s3),log(R1)])
        print 'c1,c2-',c1,c2
        B2 = min([c1*c2,B2])
        print 'B2',B2           
        R0=R1
    return s1,s2,s3


def find_j_invariants_over_QQ_C2(S,Gl,Gm,B):
    r"""

    INPUT:
        - ``S``: a list of rational primes
        - ``Gl`` : a list of generators where `\lambda` lies
        - ``Gm`` : a list of generators where `\mu` lies
        - ``B`` : a bound for the exponents

    OUTPUT:
        All the `j`-invariants

    EXAMPLE::

        sage: K.<a> = NumberField(x-1)
        sage: SK = sum([K.primes_above(p) for p in [2,5,7]],[])
        sage: t = polygen(QQ)
        sage: L.<a> = (t^3-45*t+135).splitting_field()
        sage: SL = sum([L.primes_above(p) for p in [2,5,7]],[])
        sage: Gl,Gm = Norm_subgroup_division_field(SK,SL)
        sage: find_j_invariants_over_QQ([2,5,7],Gl,Gm,88)
            [-160000, -262885120/343, 172800/343, -34560/7, -6288640/16807, 1280/7,
            1280, -6400/7, -6400/7, 1280, 1280/7, -6288640/16807, -34560/7,
            172800/343, -262885120/343, -160000]

    """
    J = []
    finiteSup,realSup,complexSup = support_of_G(Gm,20)
    SQ = []
    for p in finiteSup:
        if p.absolute_norm().factor()[0][0] not in SQ:
            SQ.append(p.absolute_norm().factor()[0][0])
    Glfree = [g for g in Gl if g.multiplicative_order() == Infinity]
    g0 = [g for g in Gl if g.multiplicative_order() != Infinity][0]
    Gltorsion = [g0**i for i in range(g0.multiplicative_order())]
    for v in cartesian_product_iterator([xrange(-B,B+1)] * len(Glfree)):
        l = prod([g**k for k,g in zip(v,Glfree)])
        for u in Gltorsion:
            if (1 - u * l).absolute_norm().is_S_unit(SQ):
                j = j_invariant(u*l)
                if j in QQ:
                    j = QQ(j)
                    if j.is_S_integral(S=S):
                        J.append(j)
    return J


def find_j_invariants_over_QQ_C3_S3(S,Gl,Gm,B):
    r"""

    INPUT:
        - ``S``: a finite set of rational prime
        - ``Gl``: a list of generetaors of a subgroup of `K^*` where `\lambda` lies
        - ``Gm``: a list of generetaors of a subgroup of `K^*` where `\mu` lies
        - ``B`` : an upper bound for the exponents of `\lambda` and `\mu`

   OUTPUT:
       All the j-invariants of elliptic curves with no full 2 torsion and good reduction outside ``S``
   """
    from itertools import product

    L = Gl[0].parent()

    SL = sum([L.primes_above(p) for p in S],[])
    SuL = L.S_unit_group(S = SL)
    print 'Gl'
    for g in Gl:
        print SuL(g).list()
    print 'lambda'
    if L.absolute_degree() == 6:
        M,MemL,t= L.subfields(degree = 2)[0]
        Emb = L.embeddings(L)
        for s in Emb:
            if s(MemL(M.gen())) == MemL(M.gen()) and not (s(L.gen()) == L.gen()):
                if len([g for g in Gl if is_in_G(s(g),Gm)]) == len(Gl):
                    sigma = s
    else:
        Emb = L.embeddings(L)
        for s in Emb:
            if len([g for g in Gl if is_in_G(s(g),Gm)]) == len(Gl):
                sigma = s
    J = []
    finiteSup,realSup,complexSup = support_of_G(Gm,20)
    SQ = []
    for p in finiteSup:
        if p.absolute_norm().factor()[0][0] not in SQ:
            SQ.append(p.absolute_norm().factor()[0][0])
    Glfree = [g for g in Gl if g.multiplicative_order() == Infinity]
    g0 = [g for g in Gl if g.multiplicative_order() != Infinity][0]
    Gltorsion = [g0**i for i in range(g0.multiplicative_order())]

    sGlfree = [sigma(g) for g in Gl if g.multiplicative_order() == Infinity]
    sg0 = [sigma(g) for g in Gl if g.multiplicative_order() != Infinity][0]
    sGltorsion = [sg0**i for i in range(g0.multiplicative_order())]

    sgplistp = [[L(1),g,g**-1] for g in sGlfree]
    for _ in range(B-1):
        for sgpl,g in zip(sgplistp,sGlfree):
            sgpl.extend([sgpl[-2] * g,sgpl[-1] * g**-1])

    gplistp = [[L(1),g,g**-1] for g in Glfree]
    for _ in range(B-1):
        for gpl,g in zip(gplistp,Glfree):
            gpl.extend([gpl[-2] * g,gpl[-1] * g**-1])

    for v1,v2 in zip(product(*gplistp),product(*sgplistp)):
        l = prod(v1)
        #print (l^2-l+1).absolute_norm().factor()
        sl = prod(v2)
        for u,su in zip(Gltorsion,sGltorsion):
            lam = u * l
            slam = su * sl
            w = (1-lam) * slam
            if w == 1:
                if (1 - lam).absolute_norm().is_S_unit(SQ):
                    j = j_invariant(lam)
                    if j in QQ:
                        j = QQ(j)
                        if j.is_S_integral(S=S):
                            print SuL(lam).list()
                            J.append(j)
    return J


def elliptic_curves_over_Q_with_good_reduction_outside_S(S=[]):
    r"""

    INPUT:
        - ``S`` : a finite set of rational primes

    OUTPUT:
        A list wiil all elliptic curve over `\mathbb Q` with good reduction outside ``S``

    """
    from sage.schemes.elliptic_curves.ell_egros import egros_from_j

    K = NumberField(x-1,'a')
    SK = sum([K.primes_above(p) for p in S],[])
    fields = two_division_fields(K,SK)

    J = [0,1728]
    #C2 cases
    for N in fields[0]:
        print 'J',J
        L = N.absolute_field('a')
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SL)
        if len(Gl) > 1 and len(Gm) >1:
            B = reduce_the_bound(L,Gl,Gm,400)
        else:
            B = 0
        if len(Gl) <= len(Gm):
            temp = find_j_invariants_over_QQ_C2(S,Gl,Gm,B)
            for j in temp:
                if j not in J:
                    J.append(j)
        else:
            temp = find_j_invariants_over_QQ_C2(S,Gm,Gl,B)
            for j in temp:
                if j not in J:
                    J.append(j)

    #C3 cases
    for N in fields[1]:
        print 'J',J
        L = N.absolute_field('a')
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SL)
        if len(Gl) > 1 and len(Gm) >1:
            B = reduce_the_bound(L,Gl,Gm,400)
        else:
            B = 0
        if len(Gl) <= len(Gm):
            temp = find_j_invariants_over_QQ_C3_S3(S,Gl,Gm,B)
            for j in temp:
                if j not in J:
                    J.append(j)
        else:
            temp = find_j_invariants_over_QQ_C3_S3(S,Gm,Gl,B)
            for j in temp:
                if j not in J:
                    J.append(j)

    #S3 case
    for N in fields[3]:
        print 'J',J
        L = N.absolute_field('a')
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SL)
        if len(Gl) > 1 and len(Gm) >1:
            B = reduce_the_bound(L,Gl,Gm,400)
        else:
            B = 0
        if len(Gl) <= len(Gm):
            temp = find_j_invariants_over_QQ_C3_S3(S,Gl,Gm,B)
            for j in temp:
                if j not in J:
                    J.append(j)
        else:
            temp = find_j_invariants_over_QQ_C3_S3(S,Gm,Gl,B)
            for j in temp:
                if j not in J:
                    J.append(j)

    curves = []
    for j in J:
        curves = curves + egros_from_j(j,S = S)

    return curves
    
    
#### Sieve different from Smart's-using Hilbert symbol ####

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


def relative_residue_class_degree(p):
    r"""

    INPUT:
        - ``p`` : a prime ideal

    OUTPUT:
        The relative class degree of ``p`` over the base field of its ring.

    EXAMPLE:

        sage: K.<a> = QuadraticField(17)
        sage: k3 = K.prime_above(3)
        sage relative_residue_class_degree(k3)
            2
        sage: L.<b> = K.extension(x^2-5)
        sage: l3 = L.prime_above(k3)
        sage: relative_residue_class_degree(l3)
            1
    """
    from sage.rings.number_field.number_field_ideal import is_NumberFieldFractionalIdeal

    if not is_NumberFieldFractionalIdeal(p):
        raise ValueError('p is not a fractional ideal')
    if p.ring().is_absolute():
        return p.residue_class_degree()

    pbelow = p.ideal_below()
    return p.residue_class_degree()/pbelow.residue_class_degree()


def simply_loop_in_C2(Gl,S,B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of `G_\lambda`
        - ``S`` : a finite set of primes
        - ``B`` : a bound of the exponents

    OUTPUT:
        All `\lambda`-invariants of the elliptic curves with `C_2` 2-division field the parent of the elements in Gl

    COMMENT:
        Actually we don't use any kind of sieving here.

    EXAMPLE::

        sage: L.<a> = QuadraticField(-1)
        sage: SL = sum([L.primes_above(p) for p in [2,3]],[])
        sage: sieve_in_C2(L.S_units(S=SL),SL,10)
            [a, -1, -a, 3, -3, 1/3, -1/3, 9, 1/9, a + 1, -a + 1, -1/2*a + 1/2,
            1/2*a + 1/2, -2, 2, 2/3, 1/2, -1/2, 3/2, 4, 4/3, 1/4, 3/4, -8, 8/9,
            -1/8, 9/8]
    """

    if Gl == []:
        raise ValueError('Gl is empty')

    L = Gl[0].parent()
    K = L.base_field()
    if L.relative_degree() != 2:
        raise ValueError('You do not work over a quadratic extension')

    SQ = list(set([p.absolute_norm().factor()[0][0] for p in S]))
    Glfree = [g for g in Gl if g.multiplicative_order() == Infinity]
    g0 = [g for g in Gl if g.multiplicative_order() != Infinity][0]
    Gltorsion = [g0**i for i in range(g0.multiplicative_order())]

    p = ZZ(2)
    while p in SQ:
        p = Primes().next(p)
    Sieve_data = []
    LCM = 1
    while LCM <= max(B/100,1):
        PL = L.primes_above(p)
        for prime in PL:
            if relative_residue_class_degree(prime) == 2:
                q = sqrt(prime.residue_field().order())
                # print 'q-1=%s'%(q-1).factor()
                # t = gcd([prime.ideallog(g)[0] for g in Gl]+[q-1])
                # print [prime.ideallog(g)[0]%(q-1) for g in Gl]+[q-1]
                # print't=%s'%(t)
                Sieve_data.append([vector([prime.ideallog(g)[0]%(q-1) for g in Gl]),q-1])
                LCM = lcm(LCM,q-1)
        p = Primes().next(p)
    print 'Sieve_data',Sieve_data
    print 'LCM=%s and B=%s'%(LCM,B)
    count = 0
    elements = []
    for v in cartesian_product_iterator([xrange(g0.multiplicative_order())]+[xrange(LCM)]*len(Glfree)):
        if len([1 for V in Sieve_data if (V[0]*vector(v)%V[1]).is_zero()]) == len(Sieve_data):
            count += 1
            # print v
            elements.append(prod([g**e for g,e in zip(Gl,v)]))
    print 'count=%s,percentage=%s'%(count,count/(g0.multiplicative_order()*LCM**len(Glfree)))

    from itertools import product
    Glfreetemp = [g**LCM for g in Glfree]
    gplistp = [[L(1),g,g**-1] for g in Glfreetemp]
    for _ in range((B/LCM).floor()-1):
        for gpl,g in zip(gplistp,Glfreetemp):
            gpl.extend([gpl[-2] * g,gpl[-1] * g**-1])

    import time
    Sunits = []
    for v in product(*gplistp):
        start = time.time()
        l = prod(v)
        for g in elements:
            mu = 1-l*g
            if not mu.is_zero():
                t = mu.absolute_norm()
                if t.is_S_unit(SQ):
                    if L.ideal(mu).is_S_unit(S):
                        Sunits.append(1-mu)
        end = time.time()
        # print end-start
    return Sunits


def congruence_relations(G,I):
    r"""
    
    INPUT:
        - ``G`` : a of generators of a subgroup of `K^*` for a number field `K`
        - ``I`` : an ideal of the number field `K`
        
    OUTPUT:
       - A matrix with rows the values of the elements of ``G`` at `(\mathcal O/I)^*`. 
       - A list with the orders of the generators of `(\mathcal O/I)^*`.
        
    EXAMPLE::
        
        sage: F.<a> = QuadraticField(2)
        sage: I = L.prime_above(5)^5
        sage: G = L.unit_group().gens_values()
        sage: congruence_relations(G,I)
            ([50  0]
            [73 11]
            [48  0],[100, 25]
            )
    """
    
    Istar = I.idealstar()
    M = copy(matrix(ZZ,len(G),len(Istar.gens()),sum([I.ideallog(g) for g in G],[])))
    return M,[g.order() for g in Istar.gens()]


def solve_linear_congruence_equation(A,b,m):
    r"""
    
    INPUT:
        - ``A`` : a list of integer numbers
        - ``b`` : an integer number
        - ``m`` : an integer number
    
    OUTPUT:
        - A basis for the solutions `\vec x=(x_1,x_2,\cdots,x_n)\in \mathbb Z^n` of the homogeneous linear congeruence equation `a_1x_1+a_2x_2\cdots+a_nx_n\equiv 0\mod m` with `A=[a_1,a_2,\cdots,a_n]`
        - A single solution for the equation `a_1x_1+a_2x_2\cdots+a_nx_n\equiv b\mod m`
        
    EXAMPLE::
        
        sage: solve_linear_congruence_equation([2,2],2,4)
            ([
             (1, 1),
             (0, 2)
             ], (1, 0))
        
                 
        sage: solve_linear_congruence_equation([5,10],2,25)
            ValueError: The linear congruence equation does not have a solution
    """
    if b % gcd(A+[m]) != 0:
        raise ValueError('The linear congruence equation does not have a solution')
    
    M = matrix(ZZ,A+[-m]).transpose()
    y = M.solve_left(vector([b]))[:len(A)]
    
    return [v[:len(A)] for v in M.kernel().basis()],y


#### Find curves ####

##Quadratic case


def choice_of_delta(place,G,bounds):
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
    return exp(-sum([(log(place(g).abs())).abs() * b for g,b in zip(G,bounds) if g.is_integral() and g.absolute_norm().abs() == 1]))


def reduce_bound_for_unit_generators_C2(Gl,Gm,bound_Gl,bound_Gm,R):
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
    infinite_primes = sum(support_of_G(Gl,200)[1:],[])

    #we find which generators are units
    units_index = [i for i,g in enumerate(Gl) if g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i,g in enumerate(Gl) if i in units_index]
    if Glunit == []:
        return bound_Gl,R
    c1_units = c_constants(Glunit,200)[0]

    # print 'R inside',R
    # R = R**4
    # print 'R',R
    #we are going to reduce the bound for units using Smart's ideas
    Bold = max([b for i,b in enumerate(bound_Gl) if i in units_index])

    #we find logRlprime
    logRlprime = max([sum([b * log(p(g).abs()).abs() for b,g in zip(bound_Gl,Gl) if g not in Glunit]) if is_real_place(p) else sum([2 * b * log(p(g).abs()).abs() for b,g in zip(bound_Gl,Gl) if g not in Glunit])for p in infinite_primes])

    #we make an arbitrary choice of an initial delta
    delta_old = 1/R
    delta_new = sqrt(delta_old)
    #max([choice_of_delta(s,Gl,[Bold/20 if i in units_index else b for i,b in enumerate(bound_Gl)]) for s in infinite_primes])

    #we reduce the bounds for the units
    reduce_bounds = bound_Gl
    while True:
        # print 'delta_old',delta_old
        # print '1',[1 for place in infinite_primes if trivial_Tp_infinite_place(bound_Gm,place,Gm[1:],delta_old)]
        if len([1 for place in infinite_primes if trivial_Tp_infinite_place(bound_Gm,place,Gm[1:],delta_new)]) == len(infinite_primes):
            Bold = min((c1_units * log(delta_new).abs() + c1_units * logRlprime).floor(),Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_old)
            reduce_bounds = [min(b,Bold) if i in units_index else b for i,b in enumerate(bound_Gl)]
            # print 'reduce_bounds',reduce_bounds
        else:
            return reduce_bounds,1/delta_old**2


def is_S_unit_element(self,u):
    r"""

    INPUT:
        - ``self`` : a S-unit group of a number field `K`
        - ``u`` : an element of the number field `K`

    OUTPUT:
        Returns `True` if ``u`` is an S-unit, `False` otherwise.

    EXAMPLE::

        sage: M.<a> = QuadraticField(2)
        sage: SM = M.primes_above(2)
        sage: is_S_unit_element(M.S_unit_group(S=SM),2)
            True
        sage: is_S_unit_element(M.S_unit_group(S=SM),3)
            False
    """
    K = self._UnitGroup__number_field
    pK = self._UnitGroup__pari_number_field
    try:
        u = K(u)
    except TypeError:
        raise ValueError("%s is not an element of %s"%(u,K))
    if self._UnitGroup__S:
        m = pK.bnfissunit(self._UnitGroup__S_unit_data, pari(u)).mattranspose()
        if m.ncols() == 0:
            return False
        else:
            return True
    else:
        if not u.is_integral() or u.norm().abs() != 1:
            return False
        else:
            return True


def sieve_in_C2(Gl,Gm,B):
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
    Sl = support_of_G(Gl,40)[0]
    Sm = support_of_G(Gm,40)[0]
    SmnotSl = [p for p in Sm if p not in Sl]
    infinite_primes = L.places(prec = 200)

    #we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()]+[B]*(len(Gl)-1)
    bound_Gm = [Gm[0].multiplicative_order()]+[B]*(len(Gm)-1)

    print 'bound_Gl-1',bound_Gl
    print 'bound_Gm-1',bound_Gm

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
    print 'bound_Gl-2',bound_Gl
    print 'bound_Gm-2',bound_Gm

    R = max([exp(sum([(log(s(g).abs())).abs() * b if is_real_place(s) else (2*log(s(g).abs())).abs() * b for g,b in zip(Gl,bound_Gl)])) for s in infinite_primes])
    # print 'R',R
    bound_Gl , R = reduce_bound_for_unit_generators_C2(Gl,Gm,bound_Gl,bound_Gm,R)

    print 'bound_Gl-3',bound_Gl
    print 'bound_Gm-3',bound_Gm

    #we use triangle inequality to reduce the bound

    old_bound = copy(bound_Gl)
    # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl,p,bound_Gl,R)
    # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl,p,bound_Gl,R)
        # print '3-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    print 'bound_Gl-4',bound_Gl
    print 'bound_Gm-4',bound_Gm

    Sunits = []

    # #we evaluate lambda in case mu is divisible by a high power(arbitrary choice) of primes in SmnotSl
    # #and we find new bounds for the exponents of Gm for the rest solutions
    #
    # Sunits = []
    # #we make a choice of the exponents of primes in SmnotSl
    # bound_SmnotSl = []
    # for p in SmnotSl:
    #     i = 1
    #     I = p**i
    #     while I.idealstar().order() == 1:
    #         i += 1
    #         I *= p
    #     while I.idealstar().gens_orders()[0] < 2*sqrt(B): #arbitrary choice of bound
    #         i += 1
    #         I *= p
    #     bound_SmnotSl.append(i)
    #
    # for e,p in zip(bound_SmnotSl,SmnotSl):
    #     Sunits += sieve_for_p_not_in_support_of_Gl_C2(p**e,Gl,Sm,bound_Gl)
    #
    # for i,p in enumerate(Sm):
    #     if p in SmnotSl:
    #         bound_Sm[i] = bound_SmnotSl[SmnotSl.index(p)]
    #     elif tau(p) in SmnotSl:
    #         bound_Sm[i] = bound_SmnotSl[SmnotSl.index(tau(p))]
    #
    # bound_Gm = bounds_for_exponents_from_bounds_for_primes(Gm,Sm,bound_Sm,bound_Gm)
    # print 'bound_Gl-5',bound_Gl
    # print 'bound_Gm-5',bound_Gm
    #
    # bound_Gl,R = reduce_bound_for_unit_generators_C2(Gl,Gm,bound_Gl,bound_Gm,R)
    #
    # print 'bound_Gl-5',bound_Gl
    # print 'bound_Gm-5',bound_Gm
    #
    # old_bound = copy(bound_Gl)
    # # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    # for p in infinite_primes:
    #     bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl,p,bound_Gl,R)
    # # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    #
    # while old_bound != bound_Gl:
    #     old_bound = copy(bound_Gl)
    #     for p in infinite_primes:
    #         bound_Gl = reduce_bound_with_simple_inequalities_C3(Gl,p,bound_Gl,R)
    #     # print '3-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)

    #Since we have reduced as much as we can, now we are able to make a simple loop to find the rest of the solutions

    Smunit_group = L.S_unit_group(S=Sm)
    for v in cartesian_product_iterator([xrange(bound_Gl[0]/2+1),xrange(bound_Gl[1]+1)]+[xrange(-b,b+1) for b in bound_Gl[2:]]):
        l = prod([g**e for g,e in zip(Gl,v)])
        if is_S_unit_element(Smunit_group,1-l):
            if l not in Sunits:
                Sunits.append(l)

    return Sunits


def sieve_for_p_not_in_support_of_Gl_C2(p,Gl,SL,bounds):
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

    #we create the congruence relations for the exponents with respect to the ideal p**n
    orders = p.idealstar().gens_orders()
    # print 'orders',orders
    M = matrix(ZZ,len(Gl),len(orders),[p.ideallog(g) for g in Gl])

    #we divide the congruence relations with the gcd of the coefficients
    GCD = [gcd(list(col)+[m]) for col,m in zip(M.columns(),orders)]
    # print 'GCD=',GCD
    C = matrix(ZZ,[col/g for col,g in zip(M.columns(),GCD)]).transpose()
    # print 'C',C
    prime_orders = [c/g for c,g in zip(orders,GCD)]
    maxorder = max(prime_orders)
    # print 'prime_orders',prime_orders

    #we need a bound for the exponents of the solutions mod p**n
    congruence_bounds = [xrange(bounds[0])]+[xrange(maxorder) if 2*b >= maxorder else xrange(-b,b) for b in bounds[1:]]
    Bpr = [0 if 2*b >= maxorder else 1 for b in bounds[1:]]
    # print 'congruence_bounds',congruence_bounds

    #we determine the solutions module p
    count = 0
    elements = []
    for v in cartesian_product_iterator(congruence_bounds):
        v = vector(v)
        if vector([(v*col)%m for m,col in zip(prime_orders,M.columns())]).is_zero():
            elements.append(prod([g**e for g,e in zip(Gl,v)]))
            count += 1
    # print 'count',count
    # print 'percent',(count/prod(congruence_bound)).n(21)

    #we determine the global solutions

    Sunits = []
    B = [QQ(b/len(c)).floor()+1 if len(c) !=0 else 1 for b,c in zip(bounds[1:],congruence_bounds[1:])]
    # print 'B',B
    Gl_exp = [g**len(c) if b == 0 else 1 for g,c,b in zip(Gl[1:],congruence_bounds[1:],Bpr)]
    count = 0
    for v in cartesian_product_iterator([xrange(-b,b) if i == 0 else xrange(1) for b,i in zip(B,Bpr)]):
        # print 'v',v
        l = prod([g**e for g,e in zip(Gl_exp,v)])
        # print 'case',count
        count += 1
        for i,g in enumerate(elements):
            # print 'i',i
            mu = 1-l*g
            if is_S_unit_element(SunitL,mu):
                if (1-mu) not in Sunits:
                    Sunits.append(1-mu)
    # print 'percent',(count/(g0.multiplicative_order()*congruence_bound**len(Glfree))).n(21)
    return Sunits


def reduce_the_bound_for_p_in_support_of_Gl_C2(prime,Gm,B):
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
    Bmid = (QQ((Blow+Bupp)/2)).floor()
    L = prime.ring()
    Labs = L.absolute_field('a')
    eLLabs = L.embeddings(Labs)[0]
    prime_abs = eLLabs(prime)
    Gm_abs = [eLLabs(g) for g in Gm]
    p = prime_abs.absolute_norm().factor()[0][0]
    f = prime_abs.residue_class_degree()
    precision = 200

    #we evaluate the new basis of Gm of elements with zero valuation at prime and their p-adic logarithms
    new_Gm0_abs, new_Gm_abs, k = a_basis_with_0_order_at_p(prime_abs,Gm_abs)
    new_Gm_abs_logp = [log_p(m,prime_abs,precision) for m in new_Gm_abs]
    new_Gm0_abs_logp = [log_p(m0,prime_abs,precision) for m0 in new_Gm0_abs]

    while Bupp-Blow > 1:
        trivial, new_Gm0_abs_logp, new_Gm_abs_logp, precision = trivial_Tp_finite_place(B,prime_abs,new_Gm0_abs,new_Gm_abs,new_Gm0_abs_logp,new_Gm_abs_logp,p**(-Bmid*f),precision)
        if trivial:
            Bupp = Bmid
        else:
            Blow = Bmid
        # print 'Bupp=%s, Blow=%s'%(Bupp,Blow)
        Bmid = (QQ((Blow+Bupp)/2)).floor()
    return Bupp


def bounds_for_exponents_from_bounds_for_primes(G,primes,primes_bounds,exp_bounds):
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
    infinite_primes = sum(support_of_G(G,200)[1:],[])
    #we find for which generators the exponents will change
    GS = [g for g in G if len([1 for p in primes if g.valuation(p) !=0]) > 0]
    # print 'GS',GS
    GSenu = [G.index(g) for g in GS]

    GSenu_bounds = [b for i,b in enumerate(exp_bounds) if G[i] in GS]
    # print 'primes_bounds',primes_bounds
    # print 'GSenu',GSenu
    # print 'GSenu_bounds',GSenu_bounds
    A = matrix(ZZ,len(primes),[[g.valuation(p) for g in GS] for p in primes])
    # B = matrix(RR,len(infinite_primes),[[log(s(g).abs()) if is_real_place(p) else 2*log(s(g).abs()) for g in GS] for p in infinite_primes])
    # AB = block_matrix([[A],[B]])
    # print 'A',A
    #we find the new exponents and return a list with the new exponents

    #if X is empty we use simply inequalities to reduce the bound

    X = Set(range(A.dimensions()[0])).subsets(len(GS)).list()

    if X == []:
        for i,gen in enumerate(GSenu):
            # print 'gen=%s, i=%s'%(gen,i)
            index_bound = exp_bounds[gen]
            # print 'index_bound',index_bound
            for j,v in enumerate(A.rows()):
                # print 'S=%s'%(sum([b*a.abs() for b,a,k in zip(GSenu_bounds,v,range(len(v))) if k != i]))
                S = sum([b*a.abs() for b,a,k in zip(GSenu_bounds,v,range(len(v))) if k != i])
                low_b = ((S+primes_bounds[j])/v[i]).floor()
                # print 'low_b',low_b
                if low_b < exp_bounds[gen]:
                    exp_bounds[gen] = low_b
            # print 'exp_bounds',exp_bounds
        return exp_bounds

    #if X is not empty we use a submatrix of A

    new_exponents = copy(exp_bounds)
    min_exp_bounds = +Infinity
    for g in X:
        M = A[g.list(),:]
        if M.rank() == len(GS):
            # print 'M',M
            Minv_abs = M.inverse().apply_map(abs)
            x = matrix(primes_bounds)[:,g.list()]
            x = x.transpose()
            # print 'x',x
            v = (Minv_abs*x).apply_map(floor)
            # print 'v',v
            for i in range(len(exp_bounds)):
                if i in GSenu:
                    exp_bounds[i] = min(v[GSenu.index(i)][0],exp_bounds[i])
            if sum(exp_bounds) < min_exp_bounds:
                new_exponents = exp_bounds
    return new_exponents


def elliptic_curves_with_good_reduction_with_a_rational_Weierstrass_point(K,S):
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
        K = NumberField(x-1,'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    #we through away the canditate 2-division fields whose relative discrimiant does not have even valuation at
    #the primes above which are not in SK

    start = time.time()
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

    #using Hilbert's symbol we choose with which fields we are going to work with

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
    end = time.time()
    print 'we have %s fields to work with,'%(len(quadratic_fields))
    print 'time for fields = %s'%(end-start)

    J = []
    #The case when they may exist two isogenous curves with the same 2-division field

    for i in range(N):
        if A[i,i] != 0:
            M,Gl,Gm = C2_extensions[i]
            print 'M=%s'%(M)
            start = time.time()
            bound = reduce_the_bound(M,Gl,Gm,200)
            end = time.time()
            print 'bound=%s,time for reduce bound=%s'%(bound,end-start)
            start = time.time()
            for l in sieve_in_C2(Gl,Gm,bound):
                j = j_invariant(l)
                # print 'j',j
                if j in K:
                    if K(j) not in J:
                        J.append(j)
            end = time.time()
            print 'time for sieve=%s'%(end-start)
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
            print 'M=%s'%(M)
            start = time.time()
            bound = reduce_the_bound(M,Gl,Gm,200)
            end = time.time()
            print 'bound=%s, time for reduce bound=%s'%(bound,end-start)
            start = time.time()
            for l in sieve_in_C2(Gl,Gm,bound):
                j = j_invariant(l)
                # print 'j',j
                if j in K:
                    if K(j) not in J:
                        J.append(j)
            end = time.time()
            print 'time for sieve=%s'%(end-start)
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

    from sage.schemes.elliptic_curves.ell_egros import egros_from_j

    curves = []
    J = [QQ(j) for j in J]+[QQ(0),QQ(1728)]
    S = [ZZ(p) for p in S]
    for j in J:
        for E in egros_from_j(j,S):
            if E not in curves:
                curves.append(E)
            for E_isogeny in E.isogenies_prime_degree(2):
                if E_isogeny.codomain() not in curves:
                    curves.append(E_isogeny.codomain())
                if E_isogeny.codomain().j_invariant() not in J:
                    J.append(E_isogeny.codomain().j_invariant())
    for E in curves:
        if E.j_invariant() not in J:
            J.append(E.j_invariant())
    if K.absolute_degree() == 1:
        J = [QQ(j) for j in J]
        final_J = []
        for j in J:
            if len(egros_from_j(j,S)) > 0:
                final_J.append(j)
        return final_J
    return J


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
    S = support_of_G(G,20)[0]
    reduce_S = []
    while S != []:
        p1 = S[0]
        p2 = sigma(p1)
        p3 = sigma(p2)
        sum1, sum2, sum3 = [sum([g.valuation(p) for g in G]) for p in [p1,p2,p3]]
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


def reduce_bound_for_unit_generators_C3(Gl,bounds,R):
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
    infinite_primes = sum(support_of_G(Gl,200)[1:],[])
    # print 'bounds',bounds

    #we find which generators are units
    units_index = [i for i,g in enumerate(Gl) if g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i,g in enumerate(Gl) if i in units_index]
    c1_units = c_constants(Glunit,200)[0]
    # print 'Glunit',Glunit


    #we are going to reduce the bound for units using Smart's ideas
    Bold = max([b for i,b in enumerate(bounds) if i in units_index])

    #we find logRlprime
    logRlprime = max([sum([b * log(p(g).abs()).abs() for b,g in zip(bounds,Gl) if g not in Glunit]) if is_real_place(p) else sum([2 * b * log(p(g).abs()).abs() for b,g in zip(bounds,Gl) if g not in Glunit])for p in infinite_primes])

    #we make an arbitrary choice of an initial delta
    delta_old = 1/R
    delta_new = sqrt(delta_old)

    #we reduce the bounds for the units
    reduce_bounds = bounds
    while True:
        # print 'Bold',Bold
        if len([1 for place in infinite_primes if trivial_Tp_infinite_place(reduce_bounds,place,Gl[1:],delta_new)]) == len(infinite_primes):
            Bold = min((c1_units * log(delta_new).abs() + logRlprime).floor(),Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_new)
            reduce_bounds = [min(b,Bold) if i in units_index else b for i,b in enumerate(bounds)]
            # print 'reduce_bounds',reduce_bounds
        else:
            return reduce_bounds,1/delta_old**2


def reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I,Gl,Gm,bounds):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``bounds`` : a list of upper bounds for each exponent. It is the same for both groups since by construction
        it holds `m_i=\sigma(l_i^{-1})`, where `l_i` and `m_i` are the generators of `Gl` and `Gm` respectively.

    """
    L = Gl[0].parent()
    Sm = support_of_G(Gm,20)[0]
    sigma = find_sigma(L)

    # print 'bounds',bounds

    #the part of the sieve based on Hilbert symbol

    Q = []
    for p in Sm:
        n = p.residue_field().order()
        if n == 2:
            M = matrix(Integers(n),[[tame_hilbert_symbol(gl,gm,p,n) for gm in Gm] for gl in Gl])
        else:
            M = matrix(Integers(n-1),[[tame_hilbert_symbol(gl,gm,p,n-1) for gm in Gm] for gl in Gl])
        Q.append(M)

    lcm_hsymbol = lcm([M.base_ring().order() for M in Q])
    # print 'lcm_hsymbol',lcm_hsymbol

    #the part of the sieve based on unramified prime and Hilbert symbol
    factors = I.factor()
    n = len(factors)
    maxorder = lcm([max((f[0]**f[1]).idealstar().gens_orders()) for f in factors]+[lcm_hsymbol])


    congruence_bounds = [xrange(bounds[0])]+[xrange(maxorder) if 2*b >= maxorder else xrange(-b,b) for b in bounds[1:]]
    Bpr = [0 if 2*b >= maxorder else 1 for b in bounds[1:]]
    # print 'congruence_bound=%s'%(congruence_bounds)
    count = 0
    elements = []
    for v in cartesian_product_iterator(congruence_bounds):
        v = vector(v)
        if len([1 for M in Q if (v*M*v).is_zero()]) == len(Q):
            # print 'v-1',v
            l = prod([g**e for g,e in zip(Gl,v)])
            m = prod([g**e for g,e in zip(Gm,v)])
            if len([1 for f in factors if (l+m-1).valuation(f[0]) >= f[1]]) == n:
                # print 'v-2',v
                count += 1
                elements.append(l)
    # print 'count=%s'%(count)
    # print 'prod',prod([len(c) for c in congruence_bounds])
    # print 'percent=%s'%((QQ(count)/QQ(prod([len(c) for c in congruence_bounds]))).n(21))
    # return 1
    #we find the solutions

    Sunits = []
    SmunitL = L.S_unit_group(S = Sm)
    B = [QQ(b/len(c)).floor()+1 if len(c) !=0 else 1 for b,c in zip(bounds[1:],congruence_bounds[1:])]
    # print 'B',B
    Gl_final = [g**len(c) if b == 0 else 1 for g,c,b in zip(Gl[1:],congruence_bounds[1:],Bpr)]
    for v in cartesian_product_iterator([xrange(-b,b) if i == 0 else xrange(1) for b,i in zip(B,Bpr)]):
        # print 'v',v
        u = prod([g **e for g,e in zip(Gl_final,v)])
        for l in elements:
            if is_S_unit_element(SmunitL,1 - l*u):
                Sunits.append(l*u)

    return Sunits


def sieve_for_p_in_support_of_Gl_C3(prime,Gm,Sl,bounds,bound_prime):
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

    #here we need to make a change of generators such that all the generators have 0 valuation at p
    new_Gm0, new_Gm ,k = a_basis_with_0_order_at_p(prime,Gm)
    # print 'new_Gm0',len(new_Gm0)
    reduce_bounds = [e for i,e in enumerate(bounds) if i != k]
    # print 'new_Gm0',len(new_Gm0)

    exp = 1
    I = prime
    while I.idealstar().order() == 1:
        exp += 1
        I *= prime
    finish = False

    if exp > bound_prime:
        return [] , exp

    while not finish and exp <= bound_prime:
        orders = I.idealstar().gens_orders()
        # print 'orders',orders

        #we create the congruence relations for the exponents with respect to the ideal p**n
        M = matrix(ZZ,len(new_Gm),len(orders),[I.ideallog(g) for g in new_Gm])
        # print 'M',M
        new_Gm0log = matrix(ZZ,[I.ideallog(m0) for m0 in new_Gm0])
        # print 'new_Gm0log',new_Gm0log
        GCD = [gcd(list(col)+[m]+list(m0)) for col,m,m0 in zip(M.columns(),orders,new_Gm0log.columns())]
        # print 'GCD',GCD
        prime_orders = [c/g for c,g in zip(orders,GCD)]
        # print 'prime_orders',prime_orders
        prime_M = matrix(ZZ,[col/g for col,g in zip(M.columns(),GCD)]).transpose()
        # print 'prime_M',prime_M
        prime_Gm0log =matrix(ZZ,[col/g for col,g in zip(new_Gm0log.columns(),GCD)]).transpose()
        # print 'prime_Gm0log',prime_Gm0log
        # print 'max(prime_orders)',max(prime_orders)
        # print 'sqrt(max(bounds))',RR(sqrt(max(bounds)))

        #Check if we have to increase the exponent
        if max(prime_orders) > sqrt(max(bounds)):
            finish = True
        else:
            exp += 1
            I *= prime

    maxorder = max(prime_orders)
    # print 'maxorder',maxorder
    import time
    #Now we find which elements satisfy the congruence relation
    # print 'len(new_Gm0log)',prime_Gm0log.dimensions()[0]
    Sunits = []
    # print 'len(new_Gm0)',len(new_Gm0)
    for new_m0,prime_m0log in zip(new_Gm0,prime_Gm0log):
        start = time.time()
        # print 'new_m0',new_m0
        # print 'mpika'
        if k != 0:
            congruence_bounds = [xrange(maxorder) if 2*b >= maxorder else xrange(-b,b) for b in reduce_bounds[1:]]
            Bprime = [0 if 2*b >= maxorder else 1 for b in reduce_bounds[1:]]
            B = [QQ(b/len(c)).floor()+1 if len(c) !=0 else 1 for b,c in zip(reduce_bounds[1:],congruence_bounds)]
        else:
            congruence_bounds = [xrange(maxorder) if 2*b >= maxorder else xrange(-b,b) for b in reduce_bounds]
            Bprime = [0 if 2*b >= maxorder else 1 for b in reduce_bounds]
            B = [QQ(b/len(c)).floor()+1 if len(c) !=0 else 1 for b,c in zip(reduce_bounds,congruence_bounds)]
        # print 'congruence_bounds',congruence_bounds
        # print 'B',B
        count = 0
        elements = []
        valuations = []
        start_congruence = time.time()
        for v in cartesian_product_iterator(congruence_bounds):
            v = vector(v)
            if vector([((v*col)+m0)%m for m,m0,col in zip(prime_orders,prime_m0log,prime_M.columns())]).is_zero():
                # print 'v',v
                elements.append(new_m0 * prod([g**e for g,e in zip(new_Gm,v)]))
                count += 1
        end_congruence = time.time()
        # print 'time for congruence %s'%(end_congruence - start_congruence)
        # print 'count',count
        # print 'percent=%s'%(RR(QQ(count)/QQ(prod([len(c) for c in congruence_bounds]))))
        # print 'number of case I have to check=%s'%(count*prod([2*b if i == 0 else 1 for b,i in zip(B,Bprime)]))

        #we determine the solutions

        elements_sigma_square = [sigma(sigma(m0)) for m0 in elements]
        if count != 0:
            new_Gm_powers = [g**len(c) if b == 0 else 1 for g,c,b in zip(new_Gm,congruence_bounds,Bprime)]
            new_Gm_powers_sigma_square = [sigma(sigma(g))**len(c) if b == 0 else 1 for g,c,b in zip(new_Gm,congruence_bounds,Bprime)]
            # print 'cartesian_product',[xrange(-b,b) if i == 0 else xrange(1) for b,i in zip(B,Bprime)]
            # count_big = 0
            # count_small = 0
            for v in cartesian_product_iterator([xrange(-b,b) if i == 0 else xrange(1) for b,i in zip(B,Bprime)]):
                # print 'v-2',v
                # count_big += 1
                m1 = prod([g**e for g,e in zip(new_Gm_powers,v)])
                m1_sigma = prod([g**e for g,e in zip(new_Gm_powers_sigma_square,v)])
                for m0,m0_sigma in zip(elements,elements_sigma_square):
                    # l = 1 - m0 * m1
                    # if is_S_unit_element(SunitL,l):
                    # if sigma(l) * (1-l) == 1:
                    if m0_sigma * m1_sigma - m0 * m1 * m0_sigma * m1_sigma == 1:
                        # count_small += 1
                        # print 'percent last loop',QQ(count_small)/QQ(count_big)
                        if is_S_unit_element(SunitL,1 - m0 * m1) or is_S_unit_element(SunitL,1 - 1/(m0 * m1)):
                            if m0 * m1 not in Sunits:
                                Sunits.append(m0 * m1)
        # end = time.time()
        # print 'time for one loop %s'%(end-start)
    return Sunits,exp


def reduce_bound_with_simple_inequalities_C3(Gl,p,bounds,R):
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
    vbar = [c for i,c in enumerate(v) if i != max_index]
    bounds_bar = [b for i,b in enumerate(bounds) if i != max_index]
    # print 'bounds_bar',bounds_bar
    # print 'S',[c*b for c,b in zip(vbar,bounds_bar)]
    S = sum([c*b for c,b in zip(vbar,bounds_bar)])

    # print 'bounds',bounds
    # print 'max_index',max_index
    low_b = QQ(S/v[max_index]).floor()
    # print 'low_b',low_b
    if low_b <= bounds[max_index]:
        for b in range(low_b,bounds[max_index]+1):
            # print 'b',b
            # print 'v[max_index]*b - S',v[max_index]*b - S
            if v[max_index]*b - S > log(R):
                # print 'b',b
                bounds[max_index] = b
                return bounds
        return bounds
    else:
        return bounds


def sieve_in_C3(Gl,Gm,B):
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
    Sm = Sl = S = support_of_G(Gl,30)[0]
    infinite_primes = sum(support_of_G(Gl,200)[1:],[])
    sigma = find_sigma(L)
    Slreduce = find_reduce_S_C3(Gl)
    # print 'Slreduce=%s'%(Slreduce)

    #we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()]+[B]*(len(Gl)-1)
    bound_Gm = [Gm[0].multiplicative_order()]+[B]*(len(Gm)-1)
    print 'bound_Gl-0',bound_Gl

    #for each prime in Slreduce we get a reduced upper bound for the valuation of lambda using Smart's idea

    bound_Slreduce = [0]*len(Slreduce)
    for i,prime in enumerate(Slreduce):
        # if prime in Slreduce:
        bound_Slreduce[i] = bound_Slreduce[Slreduce.index(prime)] = reduce_the_bound_for_p_in_support_of_Gl_C2(prime,Gm,B)
        # else:
        #     bound_Sl[i] = reduce_the_bound_for_p_in_support_of_Gl_C2(prime,Gm,B)

    bound_Sl = [0]*len(Sl)
    for i,p1 in enumerate(Slreduce):
        p2 = sigma(p1)
        p3 = sigma(p2)
        bound_Sl[Sl.index(p1)] = bound_Sl[Sl.index(p2)] = bound_Sl[Sl.index(p3)] = bound_Slreduce[i]
    bound_Gm = bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl,Sl,bound_Sl,bound_Gl)
    print 'bound_Gl-1',bound_Gl

    #we reduce the bound for the unit generators
    R = max([exp(sum([(log(s(g).abs())).abs() * b for g,b in zip(Gl,bound_Gl) if s(g).abs() != 1])) for s in infinite_primes])
    bound_Gl , R = reduce_bound_for_unit_generators_C3(Gl,bound_Gl,R)
    print 'bound_Gl-2',bound_Gl
    # print 'Slreduce',Slreduce


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


    print 'bound_Gl-3',bound_Gl

    Sunits = []

    #we determine the solutions which are divisible by high powers of primes in Slreduce

    for k,p in enumerate(Slreduce):
        # return p,bound_Gl,bound_Slreduce[k]
        solutions, exp1 = sieve_for_p_in_support_of_Gl_C3(p,Gm,Sl,bound_Gl,bound_Slreduce[k])
        Sunits += solutions
        solutions, exp2 = sieve_for_p_in_support_of_Gl_C3(p,[sigma(g) for g in Gm],Sl,bound_Gl,bound_Slreduce[k])
        Sunits += solutions
        bound_Slreduce[k] = max(exp1,exp2)
    for i,p1 in enumerate(Slreduce):
        p2 = sigma(p1)
        p3 = sigma(p2)
        bound_Sl[Sl.index(p1)] = bound_Sl[Sl.index(p2)] = bound_Sl[Sl.index(p3)] = bound_Slreduce[i]
    bound_Gm = bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl,Sl,bound_Sl,bound_Gl)
    print 'bound_Gl-4',bound_Gl


    #we reduce the bound for the unit generators again
    bound_Gl , R = reduce_bound_for_unit_generators_C3(Gl,bound_Gl,R)
    print 'bound_Gl-5',bound_Gl


    old_bound = copy(bound_Gl)
    # print '1-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm,p,bound_Gl,R)
    # print '2-old_bound=%s,bound_Gl=%s'%(old_bound,bound_Gl)
    #
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
            if pL not in Sl and not pL.idealstar().is_trivial():
                pK = pL.ideal_below()
                if pK.residue_class_degree() == pL.residue_class_degree():
                    I = L.ideal(pL.ideal_below())
                    find_prime = True
        p = Primes().next(ZZ(p))

    #we do the final sieve using the unramified and split prime we found above and the Hilbert symbol
    for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I,Gl,Gm,bound_Gl):
        if l not in Sunits:
            Sunits.append(l)

    return Sunits


def elliptic_curves_with_good_reduction_with_cubic_two_division_field(K,S):
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
        K = NumberField(x-1,'a')
        SK = [K.prime_above(p) for p in S]
        # if 2 not in S:
        #     SK.append(K.prime_above(2))
    else:
        SK = S
        # for p in K.primes_above(2):
        #     if p not in SK:
        #         SK.append(p)

    #we through away the canditate two division fields whose relative discrimiant does not have even valuation at
    #the primes above which are not in SK

    start = time.time()
    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        cubic_fields = []
        for L in cubic_extensions(K,SK+primes_above_2_not_in_SK):
            if len([1 for p in primes_above_2_not_in_SK if L.relative_discriminant().valuation(p) % 2 != 0])  == 0:
                cubic_fields.append(L)
    else:
        cubic_fields = cubic_extensions(K,SK)

    #now we have to add the primes above 2 in SK
    for p in K.primes_above(2):
        if p not in SK:
            SK.append(p)

    end = time.time()
    print 'we have %s fields to work with,'%(len(cubic_fields))
    print 'time for fields = %s'%(end-start)

    J = []
    for L in cubic_fields:
        print 'L=%s'%(L)
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SL)
        start = time.time()
        bound = reduce_the_bound(L,Gl,Gm,200)
        end = time.time()
        print 'time for reduce bound=%s'%(end-start)
        print 'bound=%s'%(bound)
        start = time.time()
        for l in sieve_in_C3(Gl,Gm,bound):
            j = j_invariant(l)
            if j in K:
                if j not in J:
                    J.append(j)
        end = time.time()
        print 'time for sieve=%s'%(end-start)

    return [QQ(j) for j in J if len(egros_from_j(QQ(j),S)) > 0]



##S3 case

def reduce_bound_for_unit_generators_S3(Gl,Gm,bounds,R):
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
    infinite_primes_Gl = sum(support_of_G(Gl,200)[1:],[])
    infinite_primes_Gm = sum(support_of_G(Gm,200)[1:],[])
    infinite_primes = [p for p in infinite_primes_Gl if p in infinite_primes_Gm]
    # print 'bounds',bounds
    # print 'infinite_primes',infinite_primes

    #we find which generators are units
    units_index = [i for i,g in enumerate(Gl) if g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    units_index = [i for i in units_index if len([1 for p in infinite_primes if p(Gl[i]).abs() != 1]) > 0]
    # print 'units_index',units_index
    Glunit = [g for i,g in enumerate(Gl) if i in units_index]
    if len(Glunit) == 0:
        return bounds,R
    # print 'Glunit',Glunit
    c1_units = c_constants(Glunit,200)[0]
    # print 'c1_units',c1_units

    #we are going to reduce the bound for units using Smart's ideas
    Bold = max([bounds[b] for b in units_index])
    # print 'Bold',Bold

    #we find logRlprime
    logRlprime = max([sum([b * log(p(g).abs()).abs() for b,g in zip(bounds,Gl) if g not in Glunit]) if is_real_place(p) else sum([2 * b * log(p(g).abs()).abs() for b,g in zip(bounds,Gl) if g not in Glunit])for p in infinite_primes])
    # print 'logRlprime',logRlprime

    #we make an arbitrary choice of an initial delta
    delta_old = 1/R
    # print 'delta_old',delta_old
    delta_new = sqrt(delta_old)
    # print 'delta_new',delta_new

    #we reduce the bounds for the units
    reduce_bounds = bounds
    # print 'reduce_bounds',reduce_bounds
    while True:
        # print 'Bold',Bold
        # print 'delta_new',1/delta_new
        sm = len([1 for place in infinite_primes if trivial_Tp_infinite_place(reduce_bounds,place,Gm[1:],delta_new)])
        sl = len([1 for place in infinite_primes if trivial_Tp_infinite_place(reduce_bounds,place,Gl[1:],delta_new)])
        if sm == len(infinite_primes) and sl == len(infinite_primes):
            # print 'log_delta',-log(delta_new)
            Bold = min((c1_units * (log(delta_new).abs() + logRlprime)).floor(),Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_new)
            reduce_bounds = [min(b,Bold) if i in units_index else b for i,b in enumerate(bounds)]
            # print 'reduce_bounds',reduce_bounds
        else:
            return reduce_bounds,1/delta_old**2


def sieve_in_S3(Gl,Gm,B):
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
    Sl, real_infinite_primes_Sl, complex_infinte_primes_Sl = support_of_G(Gl,200)
    Sm, real_infinite_primes_Sm, complex_infinte_primes_Sm = support_of_G(Gm,200)
    infinite_primes = [p for p in real_infinite_primes_Sl+complex_infinte_primes_Sl if p in real_infinite_primes_Sm+complex_infinte_primes_Sm]
    sigma = find_sigma(L)

    #when we have only one generator of the free part
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

        #we do the final sieve using the unramified and split prime we found above and the Hilbert symbol
        for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I,Gl,Gm,[L.primitive_root_of_unity().multiplicative_order()]+[B]):
            if l not in Sunits:
                Sunits.append(l)

        return Sunits
    #we have gp6 primes
    for p in Sl:
        if len(L.primes_above(p.ideal_below().ideal_below())) == 6:
            raise ValueError('There exists a prime with 6 primes!')


    #gp3 and gp6 mean the primes which have 3 and 6 congugate primes respectively

    SlnotSm_gp3 = []
    for p in Sl:
        p_below = p.ideal_below().ideal_below()
        if len(L.primes_above(p_below)) == 3:
            if p not in Sm:
                SlnotSm_gp3.append(p)


    # print 'Sl',Sl
    # print 'SlnotSm_gp3',SlnotSm_gp3
    # return sigma

    #we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()]+[B]*(len(Gl)-1)
    # bound_Gm = [Gm[0].multiplicative_order()]+[B]*(len(Gm)-1)
    bound_Sl = [0]*len(Sl)
    print 'bound Gl-0',bound_Gl

    #for each prime in SlnotSm_gp3 we get a reduced upper bound for the valuation of lambda using Smart's idea

    for prime in SlnotSm_gp3:
        e = reduce_the_bound_for_p_in_support_of_Gl_C2(prime,Gm,B)
        bound_Sl[Sl.index(prime)] = e
        if sigma(prime) in Sl:
            bound_Sl[Sl.index(sigma(prime))] = e
        else:
            bound_Sl[Sl.index(sigma(sigma(prime)))] = e

    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl,Sl,bound_Sl,bound_Gl)
    print 'bound_Gl-1',bound_Gl

    #we reduce the bound for the unit generators
    R = max([exp(sum([(2*log(s(g).abs())).abs() * b for g,b in zip(Gl,bound_Gl) if s(g).abs() != 1])) for s in infinite_primes])

    bound_Gl, R = reduce_bound_for_unit_generators_S3(Gl,Gm,bound_Gl,R)
    print 'bound_Gl-2',bound_Gl

    #we reduce the bound using simple inequalities

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


    print 'bound_Gl-3',bound_Gl

    Sunits = []

    #we determine the solutions which are divisible by high powers of primes in SlnotSm_gp3
    print 'len(SlnotSm_gp3)',len(SlnotSm_gp3)
    # return SlnotSm_gp3,Sl,bound_Gl,bound_Sl,R,infinite_primes
    for k,p in enumerate(SlnotSm_gp3):
        # return p,Sl,bound_Gl,bound_Sl
        solutions,i = sieve_for_p_in_support_of_Gl_C3(p,Gm,Sl,bound_Gl,bound_Sl[Sl.index(p)])
        # solutions, i = modified_sieve_for_p_in_support_of_Gl_S3(p,Gm,Gl,Sl,bound_Gl,bound_Sl[Sl.index(p)])
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
    # return I,bound_Gl
    for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I,Gl,Gm,bound_Gl):
        if l not in Sunits:
            Sunits.append(l)

    return Sunits


def elliptic_curves_with_good_reduction_with_S3_two_division_field(K,S):
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
        K = NumberField(x-1,'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    #we through away the canditate two division fields whose relative discrimiant does not have even valuation at
    #the primes above which are not in SK

    start = time.time()

    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        S3_fields = []
        quadratic_subfields = []
        cubic_polynomials = []
        T = s3_extensions(K,SK+primes_above_2_not_in_SK)
        for f,L,M in zip(T[0],T[1],T[2]):
            K_abs_degree = K.absolute_degree()
            dM = M.relative_discriminant()
            L1 = K.extension(f,'l1')
            dL1 = L1.relative_discriminant()
            t = dM**3 * dL1**2

            if len([1 for p in primes_above_2_not_in_SK if (t.valuation(p)-3*dM.valuation(p)) % 4 != 0])  == 0:
                S3_fields.append(L)
                quadratic_subfields.append(M)
                cubic_polynomials.append(f)
    else:
        cubic_polynomials, S3_fields, quadratic_subfields = s3_extensions(K,SK)


    #now we have to add the primes above 2 in SK
    for p in primes_above_2_not_in_SK:
        SK = [p]+SK

    end = time.time()
    print 'We have %s fields to work with'%(len(S3_fields))
    print 'time for fields = %s'%(end-start)

    J = []
    for f,L in zip(cubic_polynomials,S3_fields):
        print 'L=%s'%(L)
        print 'M',L.base_field()
        print 'f',f
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK,SL)
        # print 'Gl= %s'%(len(Gl))
        start = time.time()
        bound = reduce_the_bound(L,Gl,Gm,200)
        end = time.time()
        # return bound
        print 'time for reduce bound=%s'%(end-start)
        print 'bound=%s'%(bound)
        start = time.time()
        for l in sieve_in_S3(Gl,Gm,bound):
            j = j_invariant(l)
            if j in K:
                if j not in J:
                    J.append(j)
        end = time.time()
        print 'time for sieve=%s'%(end-start)
    from sage.schemes.elliptic_curves.ell_egros import (egros_from_jlist, egros_from_j, egros_get_j)

    return [QQ(j) for j in J if len(egros_from_j(QQ(j),S))]
