"""
pcf-higher-casoratian — Casoratian (discrete-Wronskian) closed-form gate for
HIGHER-ORDER polynomial continued fractions / simultaneous (Hermite–Padé) PCFs.

The deposited PCF corpus treats only order-2 (three-term) recurrences.  This gate
validates, BEFORE any Lean formalization, the order-k Abel–Jacobi–Liouville law

    s(n+k) = sum_{j=0}^{k-1} c_j(n) s(n+j)
    Casoratian C(n) = det [ s^(t)(n+i) ]_{i,t = 0..k-1}
    ==>  C(n+1) = (-1)^{k-1} c_0(n) C(n),
         C(n)   = ( prod_{m=0}^{n-1} (-1)^{k-1} c_0(m) ) C(0).

Only the LOWEST coefficient c_0 enters.  k=2 reproduces the corpus sign -(c_0 n).

Run:  python harness_caso_k.py
"""
import sympy as sp


def casoratian(seqs, n, k):
    return sp.Matrix([[seqs[t][n + i] for t in range(k)] for i in range(k)]).det()


def extend(seqs_init, coeffs, k, N):
    """Grow each solution to length N via s(n+k)=sum_j c_j(n) s(n+j)."""
    seqs = []
    for init in seqs_init:
        s = [sp.sympify(v) for v in init]
        for n in range(0, N):
            s.append(sum(sp.sympify(coeffs[j](n)) * s[n + j] for j in range(k)))
        seqs.append(s)
    return seqs


def symbolic_proof_order3():
    """Complete symbolic proof for k=3: identity holds for ALL data and ALL c1,c2."""
    print("=== SYMBOLIC PROOF (k=3): C(1) = c0 * C(0), independent of c1,c2 ===")
    c0, c1, c2 = sp.symbols('c0 c1 c2')
    seqs = []
    for t in range(3):
        a, b, c = sp.symbols(f'y{t}_0 y{t}_1 y{t}_2')
        seqs.append({0: a, 1: b, 2: c, 3: c2 * c + c1 * b + c0 * a})
    C0 = sp.Matrix([[seqs[t][0 + i] for t in range(3)] for i in range(3)]).det()
    C1 = sp.Matrix([[seqs[t][1 + i] for t in range(3)] for i in range(3)]).det()
    residual = sp.expand(C1 - c0 * C0)
    indep = (not sp.expand(C1).has(c1)) and (not sp.expand(C1).has(c2))
    print(f"  expand(C(1) - c0*C(0)) = {residual}   (want 0)")
    print(f"  C(1) independent of c1,c2 after recurrence : {indep}")
    ok = (residual == 0) and indep
    print(f"  k=3 SYMBOLIC: {'PROVEN' if ok else 'FAIL'}\n")
    return ok


def numeric_general_k(kmax=7, trials=5):
    """Exact-rational random checks of the step law and product form for k=2..kmax."""
    import random
    print(f"=== EXACT-RATIONAL VERIFY (step law + product form), k=2..{kmax} ===")
    all_ok = True
    for k in range(2, kmax + 1):
        sign = (-1) ** (k - 1)
        ok_k = True
        for tr in range(trials):
            rng = random.Random(7 * k + 101 * tr + 5)
            coeffs = [(lambda n, p=(rng.randint(-3, 3), rng.randint(-2, 2), rng.randint(-1, 1)):
                       p[0] + p[1] * n + p[2] * n * n) for _ in range(k)]
            seqs_init = [[rng.randint(-5, 5) for _ in range(k)] for _ in range(k)]
            seqs = extend(seqs_init, coeffs, k, k + 6)
            C = lambda n: casoratian(seqs, n, k)
            C0 = C(0)
            for n in range(0, 4):
                if sp.simplify(C(n + 1) - sign * sp.Integer(coeffs[0](n)) * C(n)) != 0:
                    ok_k = False
                prod = sp.Integer(1)
                for m in range(n):
                    prod *= sign * sp.Integer(coeffs[0](m))
                if sp.simplify(C(n) - prod * C0) != 0:
                    ok_k = False
        print(f"  k={k}: C(n+1)=({sign})c0(n)C(n)  &  C(n)=prod ({sign})c0  ->  "
              f"{'PASS' if ok_k else 'FAIL'}")
        all_ok = all_ok and ok_k
    print(f"  general-k: {'PASS' if all_ok else 'FAIL'}\n")
    return all_ok


def named_instance_tribonacci():
    """Concrete order-3 instance: Tribonacci s(n+3)=s(n+2)+s(n+1)+s(n) (c0=1) =>
    Casoratian is constant.  A clean, fully reproducible witness."""
    print("=== NAMED INSTANCE: Tribonacci-type order-3 (c0=c1=c2=1) ===")
    k = 3
    coeffs = [lambda n: 1, lambda n: 1, lambda n: 1]
    seqs = extend([[1, 0, 0], [0, 1, 0], [0, 0, 1]], coeffs, k, 12)
    vals = [casoratian(seqs, n, k) for n in range(0, 10)]
    ok = all(v == vals[0] for v in vals) and vals[0] != 0
    print(f"  C(n) for n=0..9 : {vals}")
    print(f"  constant & nonzero (c0=1 => prod=1) : {'PASS' if ok else 'FAIL'}\n")
    return ok


def named_instance_polynomial():
    """Order-3 with genuine polynomial coefficients c0(n)=n+1, c1(n)=2n+1, c2(n)=1:
    Casoratian product form C(n) = (prod_{m<n}(m+1)) C(0) = n! * C(0)."""
    print("=== NAMED INSTANCE: c0(n)=n+1, c1(n)=2n+1, c2(n)=1  (=> C(n)=n!*C(0)) ===")
    k = 3
    coeffs = [lambda n: n + 1, lambda n: 2 * n + 1, lambda n: 1]
    seqs = extend([[1, 0, 0], [0, 1, 0], [0, 0, 1]], coeffs, k, 12)
    ok = True
    for n in range(0, 9):
        pred = sp.factorial(n) * casoratian(seqs, 0, k)
        if sp.simplify(casoratian(seqs, n, k) - pred) != 0:
            ok = False
    print(f"  C(n) = n! * C(0) for n=0..8 : {'PASS' if ok else 'FAIL'}\n")
    return ok


if __name__ == "__main__":
    print("Higher-order Casoratian gate (Abel–Jacobi–Liouville for order-k PCFs)\n")
    r = [symbolic_proof_order3(), numeric_general_k(), named_instance_tribonacci(),
         named_instance_polynomial()]
    print("OVERALL:", "ALL PASS" if all(r) else "SOME FAILED")
