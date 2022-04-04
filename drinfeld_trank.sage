import sage.rings
import sage.rings.polynomial.skew_polynomial_element
#from sage.rings.polynomial.skew_polynomial_element import ConstantSkewPolynomialSection
import math

# Field parameters
p = 11
k = 1
q = p^k
m = 5
qq = q**m
d = 2
n = m*d


# Field constructors, should put this in a class to reduce
# hard-coding
F0 = GF(q)

F1 = GF(qq)


A.<t> = F0[]
ip = t^5 - t^2 + 1

FP.<t> = GF(q**m, modulus=ip)

FPX.<s> = PolynomialRing(FP)

#print(FPX.irreducible_element(2))
ipp = s^2 + 7*t^4 + 7*t^3 + 6*t^2 + 8*t + 6
FD = FP.extension(ipp)
#print(FD.size())

#print(n)
sigma = FD.frobenius_endomorphism(1)


K = FD

L = OrePolynomialRing(FD, sigma, 'x')

KR.<w> = K[]

rand_elem = ((8*t^4 + 3*t^3 + 9*t^2 + 8*t + 5)*s + 10*t^4 + 2*t^3 + 2*t^2 + 4*t + 4)*w^2 + ((3*t^4 + t^3 + 8*t^2 + 6*t + 1)*s + 2*t^4 + 10*t^3 + 9*t^2 + 7*t + 5)*w + (t^4 + 5*t^3 + 5*t^2 + 8*t + 1)*s + t^3 + 10*t^2 + 10*t + 6

KE = K.extension(rand_elem)

#rank
r = 3
xx = L.gen()
#print("h3")
drin = [K(0) for i in range(r + 1)]
#print("h2")

#drin[7] = 1
#drin[5] = 1
#drin[4] = t + 2*t^2 - s
drin[3] = 1
drin[2] = t +5*t^5 + s
drin[1] = t^2 + 1 + s + t^3
drin[0] = t



phit = L(0)
for i, coeff in enumerate(drin):
    phit += coeff * (xx)^i



print("parameters")
print("characteristic: " + str(p))
print("F_q: GF(" + str(q) + ")" )
print("A-Characteristic: " + str(ip))
print("d: " + str(d))
print("n: " + str(n))
print("r: " + str(r))
print("phi_t: " + str(phit))


def frob_iter(elem, iters):
    ret = elem
    for i in range(iters):
        ret = (ret)^q
    return ret


def pad(lst, size):
    diff = size - len(lst)
    if diff > 0:
        for i in range(diff):
            lst.append(0)
    return lst

def gen_power_matrix(elem, m):
    M = matrix(K, m, m)
    base = 1
    for i in range(1,m+1):
        base *= elem
        base_coeffs = base.coefficients(sparse = false)
        for j in range(m):
            M[i,j] = base_coeffs[j]
    return M

def is_basis(elem):
    M = gen_power_matrix(elem, m)
    return not M.determinant == 0


# compute a(b)
def fast_comp(a,b):
    n = max(len(a.list()), len(b.list())) - 2
    k = int(math.ceil(sqrt(n + 1)))
    a_coeff = pad(a.list(), n + 1)
    b_coeff = pad(b.list(), n + 1)
    pi = [1,b]
    ti = [1]
    qi = []
    # Step 1
    for i in range(2, k + 1):
        pi.append( (pi[i-1]*b) )
        if (i == k):
            ti.append(pi[k])
    # Step 2
    for i in range(2,k):
        ti.append(ti[i-1]*ti[1] )
    # Step 3
    P = matrix( m , k )
    Q = matrix( k, k )
    for i in range(k):
        for j in range(k):
            Q[i,j] = a_coeff[j*k + i]

    for j in range(k):
        poly = pad( pi[j].list(), m +1)
        for i in range(m):
            P[i,j] = poly[i]
    PQ = P * Q
    for l in range(k):
        temp = 0
        for i in range(m):
            temp += PQ[i,l]*(t^i)
        qi.append(temp)
    # Step 4
    res = qi[0]
    for i in range(1,k):
        res += qi[i] * ti[i]
    return res


def fast_exp(a, e):
    if e == 0:
        return 1
    ex = a
    prod = 1
    while e > 0:
        if e % 2 == 1:
            prod *= ex
        e = e // 2
        ex *= ex
    return prod

def comp(a,m):
    res = t
    for i in range(m):
        res = fast_comp(res,a)
    return res


def comp_b(a, m):
    if m == 0:
        return t
    ex = a
    com = t
    while m > 0:
        if m % 2 == 1:
            com = fast_comp(ex,com)
        m = m // 2
        ex = fast_comp(ex,ex)
    return com

def trace(a):
    res = 0
    cur = a
    for i in range(m):
        res += cur
        cur = cur^q
    return res




def fast_mult(a, b):
    s = max(a.degree(), b.degree())
    sstar = int(math.ceil(sqrt(s + 1)))
    a_coeff = a.coefficients(sparse = false)
    b_coeff = b.coefficients(sparse = false)
    lena = len(a_coeff)
    lenb = len(b_coeff)
    for i in range(sstar^2 - lena):
        a_coeff.append(0)
    for i in range(sstar^2 - lenb):
        b_coeff.append(0)
    A = matrix(K, sstar, sstar)
    B = matrix(K, sstar, sstar + s)
    C = matrix(K, sstar, sstar + s)
    sigmai = [t, t^q]
    poly_inv = comp(t^q, m-1)

    inv_sigmai = [t, comp(poly_inv, sstar)]
    for i in range(2, s + sstar):
        sigmai.append(fast_comp(sigmai[1], sigmai[i-1] ))
    for i in range(sstar):
        if i > 1:
            inv_sigmai.append(fast_comp(inv_sigmai[1], inv_sigmai[i-1] ))
        for j in range(sstar):
            A[i,j] = fast_comp(inv_sigmai[i], (a_coeff[i*sstar +j]) )
        for j in range(sstar + s):
            if (j >= i and j - i <= s):
                B[i,j] = fast_comp(sigmai[i], b_coeff[j- i])
            else:
                B[i,j] = 0
    C = A*B
    res = 0
    for i in range(sstar):
        ci = 0
        for j in range(sstar + s):
            ci += fast_comp(sigmai[i*sstar], C[i, j])*(xx^(i*sstar + j))
        res += ci
    return res


def sigma_n_mod(mod_mat):
    mod_coeff = matrix(K, 3, 1)
    mod_coeff[0,0] = 1
    mod_coeff[1,0] = mod_coeff[2,0] = 0
    for i in range(n-1):
        mod_coeff = mod_mat*mod_coeff
    return mod_coeff

def eval(poly, val):
    coeff = poly.list()
    res = 0
    for i in range(len(coeff)):
        res += coeff[i]*(val^i)
    return res

def phimap(poly):
    coeff = poly.polynomial().list()
    res = 0
    for i in range(len(coeff)):
        res += coeff[i]*phit^i
    return res

# use this for weird cases like ip
def phimap2(poly):
    coeff = poly.list()
    res = 0
    for i in range(len(coeff)):
        res += coeff[i]*phit^i
    return res

def phimap3(poly):
    coeff = poly.list()
    res = 0
    for i in range(len(coeff)):
        res += coeff[i]*phit^i
    return res


# apply the skew polynomial as an operator to val
def oper(skew, val):
    coeff = skew.list()
    ret = 0
    for i in range(len(coeff)):
        ret += coeff[i]*(val^(q^i))
    return ret

# version that works when the frobenius is the identity
def fast_oper(skew, val):
    coeff = skew.list()
    ret = 0
    if skew == 1:
        return val
    for i in range(len(coeff)):
        ret += coeff[i]*val
    return ret


def hankel_sol():

    phip = phimap2(ip^d)
    col_blocks = int(math.floor((n*(r -1))/r)) + 1
    row_blocks = n
    row_block_size = r
    rowdim = row_blocks*row_block_size
    alpha = [KE.random_element() for q in range(row_blocks)]
    col_block_size = [r - 1 - math.floor(u*r/n) for u in range(col_blocks)]
    coldim = 0
    for u in range(col_blocks):
        coldim += col_block_size[u]
    matr = matrix(KE, rowdim, coldim)
    vec = matrix(KE, rowdim, 1)
    basei = 0
    basej = 0
    phit_arr = [1]
    for i in range(col_blocks):
        phit_arr.append(phit_arr[i]*phit)
    for b_i in range(row_blocks):
        basei = row_block_size*b_i
        for b_j in range(col_blocks):
            basej = 0
            for bloc in range(b_j):
                basej += col_block_size[bloc]
            br = col_block_size[b_j]
            for i in range(row_block_size):
                for j in range(1, br + 1):
                    if (i == 0):
                        matr[basei + i, basej + j - 1] = oper(-phit_arr[b_j], frob_iter(alpha[b_i], n*(j)))
                    elif (j < br):
                        matr[basei + i, basej + j - 1] = matr[basei + i - 1, basej + j]
                    else:
                        matr[basei + i, basej + j - 1] = frob_iter(matr[basei + i - 1, basej + j - 1], n)
    for q in range(row_blocks):
        for i in range(row_block_size):
            vec[row_block_size*q + i, 0] = frob_iter(alpha[q], n*(r +i)) - oper(phip, frob_iter(alpha[q], n*(i)))
    return matr.solve_right(vec)




#print(phimap(ip)

# use the algorithm given in garai/papikian to compute the char poly for higher rank
def garai():
    res = matrix(K,r-1,1)
    ret = phimap2(-ip^d)
    for i in range(r-1):
        coeff = ret.list()
        res[i] = -1*coeff[n*(i+1)]
        ret += phimap(res[i][0])*(xx^(n*(i+1) ))
    return res

def schoof():
    points = [ [] for i in range(r - 1) ]
    for i in range(p):
        e = i
        mods = [xx^(n) % (phit - e)]
        modbasis = [(xx^(n) % (phit - e)).list()]
        for i in range(1, r):
            mods.append(mods[0]*mods[i-1] % (phit - e))
            modbasis.append(mods[i].list())
            #modbasis.append((xx^(i*n) % (phit - e)).list())
        # pad coefficient list with 0
        for i in range(r):
            clen = len(modbasis[i])
            if clen < r:
                for j in range(clen, r):
                    modbasis[i].append(0)
        sol_mat = matrix(K, r - 1, r -1)
        ker = vector([-modbasis[r-1][i] for i in range(r - 1, 0, -1) ])
        for i in range(r-1):
            for j in range(r-1):
                sol_mat[j, r - 2 - i] = modbasis[i][r - 1 - j]

        sol = sol_mat.solve_right(ker)

        for i in range(r-1):
            points[i].append((e, sol[i]))

    RR = PolynomialRing(K, 'u')
    mincoeffs = []
    for i in range(r-1):
        mincoeffs.append(RR.lagrange_polynomial(points[i]))
    return mincoeffs

print("testing Schoof-like algorithm")
f = schoof()
print(f)

res = xx^(r*n) - phimap2(ip^d)
for i in range(1, r):
    res += phimap2(f[i-1]) * (xx^((r-i)*n))

print("Verification of schoof-like (this must be 0): " + str(res))


print("garai")

#print(garai())

print("hankel")
print(hankel_sol())

QQ.<u> = A[]
