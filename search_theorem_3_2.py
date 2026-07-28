"""
Reference implementation and complete verification for Theorem 3.2 of
"Two Eternal Survivors of a GCD-Perturbed Fibonacci Recursion,
via a Finite-Candidate Criterion for Unimodular Orbits"

Certifies that the seeds (a,b) = (3893, 2201) and (4361, 2615) of the
recursion

    g(1)=a, g(2)=b, g(n) = g(n-1) + g(n-2) + gcd(g(n-1), g(n-2))

are ETERNAL SURVIVORS: gcd(g(n), g(n-1)) = 1 for every n >= 1.

Method (Theorem 3.1 of the paper). Write h1=a+1, h2=b+1. If a prime q
ever "captures" the sequence (forces the gcd above 1), then q must
divide N(h1,h2)^2 - 1, where N(x,y) = x^2+xy-y^2 is the norm form of
Z[phi]. This is a FIXED, FINITE integer computable directly from the
seed. We factor it completely and test EVERY resulting candidate prime
by an exact discrete-log computation in Z[phi]/(q). If none captures,
Theorem 3.1 guarantees NO prime ever can: the seed survives forever,
with mathematical certainty, not merely "up to the primes we checked".

Dependencies: sympy (factorint, isprime, primerange).
Runtime: a few seconds.
"""

import math
from sympy import factorint, isprime, primerange

# ============================================================================
# Part 0 — Arithmetic in Z[phi], where phi^2 = phi + 1.
# Elements are represented as pairs (x, y) meaning x + y*phi.
# ============================================================================


def ring_mul(u, v, p):
    """(x1+y1*phi)*(x2+y2*phi) mod p, using phi^2 = phi+1."""
    x1, y1 = u
    x2, y2 = v
    return ((x1 * x2 + y1 * y2) % p,
             (x1 * y2 + x2 * y1 + y1 * y2) % p)


def ring_pow(base, e, p):
    """base^e mod p in the ring, by fast exponentiation. e >= 0."""
    result = (1, 0)  # multiplicative identity
    b = base
    while e > 0:
        if e & 1:
            result = ring_mul(result, b, p)
        b = ring_mul(b, b, p)
        e >>= 1
    return result


def N(x, y):
    """Field norm N(x + y*phi) = x^2 + xy - y^2. Multiplicative: N(ab)=N(a)N(b)."""
    return x * x + x * y - y * y


def legendre(a, p):
    """Legendre symbol (a/p) for odd prime p."""
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


# ============================================================================
# Part 1 — exact multiplicative order of phi mod q
# ============================================================================

def true_order(base, M, p):
    """
    Exact order of `base` in (Z[phi]/p)^*, given a known multiple M of
    that order (M = p-1 if p splits, M = 2(p+1) if p is inert). Standard
    algorithm: for each prime factor of M, remove as much of it as
    possible while the reduced power still equals the identity.
    """
    L = M
    for ell in factorint(M):
        while L % ell == 0 and ring_pow(base, L // ell, p) == (1, 0):
            L //= ell
    return L


# ============================================================================
# Part 2 — baby-step giant-step membership test
# ============================================================================

def bsgs_member(beta, base, L, p):
    """
    Decide whether beta lies in the cyclic group <base> (of exact order
    L) inside (Z[phi]/p)^*, via baby-step giant-step. O(sqrt(L)) ring
    operations -- feasible even when L is many millions.
    """
    m = math.isqrt(L) + 1
    baby = {}
    cur = (1, 0)
    for i in range(m):
        if cur not in baby:
            baby[cur] = i
        cur = ring_mul(cur, base, p)
    base_inv = ring_pow(base, L - 1, p)      # base^(-1), since base^L = 1
    gamma = ring_pow(base_inv, m, p)          # base^(-m)
    cur = beta
    for j in range(m):
        if cur in baby:
            return True
        cur = ring_mul(cur, gamma, p)
    return False


# ============================================================================
# Part 3 — independent correctness validation of Parts 1-2
# (exactly the checks described in the proof of Theorem 3.2)
# ============================================================================

def validate_algorithm(verbose=True):
    """
    (a) For every split prime q < 2000, compare true_order() against
        direct enumeration of the cyclic orbit of phi.
    (b) For the degenerate structural case L = q-1 (which occurs for
        two of the three decisive primes below, and in which every
        element trivially satisfies x^(q-1)=1 by Fermat), exhaustively
        test bsgs_member() against EVERY nonzero point of (Z/qZ)^2,
        for several small primes sharing this configuration.
    Raises AssertionError on any discrepancy.
    """
    if verbose:
        print("Validation (a): true_order() vs. direct enumeration (split q < 2000)")
    checked = 0
    for q in primerange(3, 2000):
        if legendre(5, q) != 1:
            continue
        L = true_order((0, 1), q - 1, q)
        x, y, L_direct = 0, 1, 1
        while (x, y) != (1, 0):
            x, y = ring_mul((x, y), (0, 1), q)
            L_direct += 1
        assert L == L_direct, f"order mismatch at q={q}: {L} vs {L_direct}"
        checked += 1
    if verbose:
        print(f"  {checked} split primes checked, 0 discrepancies.")

    if verbose:
        print("Validation (b): bsgs_member() vs. exhaustive search, degenerate case L=q-1")
    tested = 0
    for q in primerange(11, 400):
        if legendre(5, q) != 1:
            continue
        if true_order((0, 1), q - 1, q) != q - 1:
            continue
        L = q - 1
        for a in range(q):
            for b in range(q):
                if (a, b) == (0, 0):
                    continue
                predicted = bsgs_member((a, b), (0, 1), L, q)
                x, y, found = 0, 1, False
                for _ in range(L):
                    if (x, y) == (a, b):
                        found = True
                        break
                    x, y = ring_mul((x, y), (0, 1), q)
                assert predicted == found, f"BSGS mismatch at q={q}, point=({a},{b})"
        tested += 1
        if tested >= 3:
            break
    if verbose:
        print(f"  {tested} primes with L=q-1, EVERY nonzero point checked, 0 discrepancies.\n")


# ============================================================================
# Part 4 — certification of a single seed
# ============================================================================

def certify_survivor(name, a, b):
    """
    Certify that seed (a,b) is an eternal survivor of the recursion,
    following exactly the algorithm specified in the proof of
    Theorem 3.2.
    """
    h1, h2 = a + 1, b + 1
    assert math.gcd(a, b) == 1, "seed must be coprime"
    assert h1 % 6 == 0 and h2 % 6 == 0, "fails the necessary mod-6 condition (Section 2.1)"

    Nb = N(h1, h2)
    target = Nb * Nb - 1
    assert target != 0, "seed would be a global unit of Z[phi] -- excluded by construction"

    factors = sorted(factorint(target).keys())
    print(f"=== {name}: (a,b) = ({a},{b})   [h1={h1}, h2={h2}] ===")
    print(f"  N(h1,h2)      = {Nb}")
    print(f"  N^2 - 1       = {target}")
    print(f"  prime factors = {factors}")
    print(f"  (Theorem 3.1: these are the ONLY primes that could ever capture this seed)")

    beta = (h1, h2)
    for q in factors:
        assert isprime(q)
        leg = legendre(5, q)
        assert leg != 0, f"q={q} is the ramified prime 5; needs the separate check of Theorem 2.4"
        M = (q - 1) if leg == 1 else 2 * (q + 1)
        L = true_order((0, 1), M, q)
        captured = bsgs_member((beta[0] % q, beta[1] % q), (0, 1), L, q)
        kind = "split" if leg == 1 else "inert"
        print(f"    q = {q:>12}  ({kind:5s}, ord(phi) = {L:>12}) -> "
              f"{'CAPTURES' if captured else 'does not capture'}")
        if captured:
            print(f"  RESULT: {name} is captured by q={q}. NOT an eternal survivor.\n")
            return False

    print(f"  RESULT: no candidate captures -- {name} is a CERTIFIED ETERNAL SURVIVOR.\n")
    return True


# ============================================================================
# Main
# ============================================================================

if __name__ == "__main__":
    validate_algorithm()
    ok1 = certify_survivor("Survivor 1", 3893, 2201)
    ok2 = certify_survivor("Survivor 2", 4361, 2615)
    assert ok1 and ok2
    print("Theorem 3.2 fully certified: both seeds survive forever.")