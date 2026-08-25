#!/usr/bin/env python3
"""Discharge the two arithmetic axioms in the Lean development.

`Lelantos.p_prime` and `Lelantos.ell_prime` are recorded as axioms because Mathlib's
`norm_num` primality extension is trial-division based and cannot certify a 254-bit or
251-bit number. This script checks them externally and checks the constants themselves
against the values the circuit toolchain actually uses.

For `p` there is a **Lucas certificate**: the full factorization of `p - 1` is checked to
multiply out, and a base `a` of multiplicative order exactly `p - 1` is exhibited. That is
a primality proof for `p`, modulo the primality of the factors themselves — which the
report labels honestly, deterministically certified by trial division where the factor is
small enough and Miller-Rabin otherwise.

The factorization is recorded rather than searched for: trial division of `p - 1` up to a
practical bound leaves a 173-bit composite cofactor, so a certificate built that way can
never complete. Every recorded factor is re-verified on each run, and a failure to certify
sets the exit status.

For `ell` only Miller-Rabin is run; `ell - 1`'s factorization is not recorded here.

Run:  python3 lean/scripts/check-prime.py
"""

import random
import sys

# BN254 scalar field modulus (circom's default prime r) -- Lelantos/Model/Field.lean :: p
P = 21888242871839275222246405745257275088548364400416034343698204186575808495617

# Complete factorization of P - 1, with multiplicity. Verified to multiply out below, so a
# transcription slip cannot pass silently.
P_MINUS_1_FACTORS = (
    [2] * 28
    + [3, 3, 13, 29, 983, 11003, 237073]
    + [405928799, 1670836401704629, 13818364434197438864469338081]
)

# Factors at most this large are certified prime by exhaustive trial division rather than
# by Miller-Rabin.
DETERMINISTIC_LIMIT = 2 * 10 ** 15

# Baby Jubjub prime-order subgroup order -- Lelantos/Model/Jubjub.lean :: ell
# This is the full curve order divided by the cofactor 8.
BABYJUB_ORDER = 21888242871839275222246405745257275088614511777268538073601725287587578984328
ELL = 2736030358979909402780800718157159386076813972158567259200215660948447373041


def is_probable_prime(n: int, rounds: int = 64) -> bool:
    """Miller-Rabin. With 64 random bases the error probability is below 2^-128."""
    if n < 2:
        return False
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for sp in small_primes:
        if n % sp == 0:
            return n == sp
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    rng = random.Random(20260804)  # deterministic, so runs are reproducible
    for _ in range(rounds):
        a = rng.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def is_prime_by_trial_division(n: int) -> bool:
    """Exhaustive trial division. A proof, not a probabilistic test -- but only usable on
    factors small enough that sqrt(n) is reachable."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def certify_factor(q: int) -> tuple[bool, str]:
    """Establish that a claimed factor is prime, saying which method was used."""
    if q <= DETERMINISTIC_LIMIT:
        return is_prime_by_trial_division(q), "trial division"
    return is_probable_prime(q), "Miller-Rabin"


def lucas_certificate(n: int, factors: list[int]) -> tuple[bool, str]:
    """Lucas primality test. If the *complete* factorization of `n - 1` is known and some
    base `a` satisfies

        a^(n-1) = 1 (mod n)   and   a^((n-1)/q) != 1 (mod n) for every prime q | n-1

    then `a` has multiplicative order exactly `n - 1`, so the group `(Z/n)*` has `n - 1`
    elements and `n` is prime.

    Returns (ok, detail). The caller is responsible for reporting how the primality of each
    `q` was established -- this function checks the factorization multiplies out, but takes
    the factors' primality as given."""
    product = 1
    for q in factors:
        product *= q
    if product != n - 1:
        return False, "claimed factorization does not multiply to n-1"
    qs = sorted(set(factors))
    for a in range(2, 1000):
        if pow(a, n - 1, n) != 1:
            continue
        if all(pow(a, (n - 1) // q, n) != 1 for q in qs):
            return True, f"witness base a = {a}, {len(qs)} distinct prime factors"
    return False, "no base of full order found in [2, 1000)"


def main() -> int:
    ok = True

    print(f"p   = {P}")
    print(f"  bits            : {P.bit_length()}")
    print(f"  Miller-Rabin    : {is_probable_prime(P)}")
    if not is_probable_prime(P):
        print("  FAIL: p is composite -- Lelantos.p_prime is FALSE")
        ok = False

    print("  p-1 factors     :")
    for q in sorted(set(P_MINUS_1_FACTORS)):
        q_prime, method = certify_factor(q)
        mult = P_MINUS_1_FACTORS.count(q)
        label = f"{q}^{mult}" if mult > 1 else f"{q}"
        print(f"      {label:<34} prime={q_prime} ({method})")
        if not q_prime:
            print(f"      FAIL: claimed factor {q} is not prime")
            ok = False

    lucas_ok, detail = lucas_certificate(P, P_MINUS_1_FACTORS)
    print(f"  Lucas certificate: {lucas_ok} -- {detail}")
    if not lucas_ok:
        print("  FAIL: no primality certificate for p -- only the probabilistic test stands")
        ok = False

    print(f"\nell = {ELL}")
    print(f"  bits            : {ELL.bit_length()}")
    print(f"  Miller-Rabin    : {is_probable_prime(ELL)}")
    if not is_probable_prime(ELL):
        print("  FAIL: ell is composite -- Lelantos.ell_prime is FALSE")
        ok = False

    print("\nconstant cross-checks")
    cofactor_ok = BABYJUB_ORDER == 8 * ELL
    print(f"  babyjub order == 8 * ell : {cofactor_ok}")
    ok = ok and cofactor_ok

    size_checks = {
        "2^64  < p": 2 ** 64 < P,
        "2^66  < p": 2 ** 66 < P,
        "2^67  < p": 2 ** 67 < P,
        "2^128 < p": 2 ** 128 < P,
        "2^252 < p": 2 ** 252 < P,
        "p < 2^254": P < 2 ** 254,
    }
    for label, val in size_checks.items():
        print(f"  {label:12} : {val}")
        ok = ok and val

    print("\nOK" if ok else "\nFAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
