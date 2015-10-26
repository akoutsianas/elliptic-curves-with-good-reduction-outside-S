def discriminant(C):
    r"""

    INPUT:
        - ``C`` : a hyperelliptic curves ``C`` of the form `y^2+Q(x)y=P(x)`.

    OUTPUT:
        The discriminant of ``C``.

    EXAMPLE::

        sage: C = HyperellipticCurve(t^5-1,t^3)
        sage: discriminant(C)

    """

    g = C.genus()
    P, Q = C.hyperelliptic_polynomials()

    return 2**(4*g)*(P+Q**2/4).discriminant()

