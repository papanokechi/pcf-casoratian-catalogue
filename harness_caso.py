"""
pcf-casoratian-catalogue -- Casoratian closed-form gate (TEMPLATE + self-test).

Track (2): the "guaranteed-clean-deposit" line. Each family is a one-line
three-term recurrence whose Casoratian (Wronskian) W_n admits a factorial /
double-factorial / hypergeometric closed form, provable by a one-step induction
-> a clean Lean axiom cone. This script is the NUMERIC/SYMBOLIC gate that must
pass BEFORE any Lean formalization or write-up of a family: it confirms the
conjectured closed form against the actual recurrence (the "numerically verify
first" discipline), exactly as q_0..q_5 gate-checks were used in
pcf-casoratian-lean.

SELF-TEST family (the deposited 4/pi PCF, reduced recurrence):
    (2n-1) x_n = (3n+1) x_{n-1} - n x_{n-2}
For two independent solutions the Casoratian satisfies the first-order law
    W_n = (c_n / a_n) W_{n-1} = (n / (2n-1)) W_{n-1},
hence the closed form
    W_n = (n! / (2n-1)!!) * W_1.
Reproducing this is the gate that validates the harness; new families plug in
below with their own (a_n, b_n, c_n) and conjectured closed form.
"""
import sympy as sp


def double_factorial_odd(m):
    """(2m-1)!! = 1*3*5*...*(2m-1), with (2*0-1)!! := 1."""
    r = sp.Integer(1)
    for k in range(1, m + 1):
        r *= (2 * k - 1)
    return r


def generate_solution(a, b, c, x0, x1, N):
    """Sequence solving a(n) x_n = b(n) x_{n-1} - c(n) x_{n-2}, exact rationals."""
    xs = [sp.Integer(x0), sp.Integer(x1)]
    for n in range(2, N + 1):
        xn = sp.Rational(b(n) * xs[n - 1] - c(n) * xs[n - 2], a(n))
        xs.append(xn)
    return xs


def casoratian_gate(name, a, b, c, closed_ratio, N=8):
    """
    closed_ratio(n) must return the predicted W_n / W_1 (independent of solutions).
    Returns True iff W_n == closed_ratio(n) * W_1 for n = 1..N.
    """
    h = generate_solution(a, b, c, 1, 5, N)   # one solution (here h_n = n^2+3n+1)
    g = generate_solution(a, b, c, 0, 1, N)   # an independent solution
    W1 = h[1] * g[0] - h[0] * g[1]
    print(f"[{name}]  W_1 = {W1}")
    print(f"  {'n':>2} {'W_n':>16} {'predicted':>16} {'ok':>5}")
    ok_all = True
    for n in range(1, N + 1):
        W = h[n] * g[n - 1] - h[n - 1] * g[n]
        pred = closed_ratio(n) * W1
        ok = sp.simplify(W - pred) == 0
        ok_all = ok_all and ok
        print(f"  {n:>2} {str(W):>16} {str(pred):>16} {str(ok):>5}")
    print(f"  GATE [{name}]: {'PASS' if ok_all else 'FAIL'}\n")
    return ok_all


if __name__ == "__main__":
    print("Casoratian closed-form gate -- self-test on the deposited 4/pi PCF\n")
    a = lambda n: (2 * n - 1)
    b = lambda n: (3 * n + 1)
    c = lambda n: n
    closed_ratio = lambda n: sp.Rational(sp.factorial(n), double_factorial_odd(n))
    passed = casoratian_gate("4/pi PCF: (2n-1)x_n=(3n+1)x_{n-1}-n x_{n-2}",
                             a, b, c, closed_ratio, N=8)
    # Sanity: confirm h_n = n^2+3n+1 is the intended explicit solution.
    h = generate_solution(a, b, c, 1, 5, 6)
    explicit = [sp.Integer(n * n + 3 * n + 1) for n in range(0, 7)]
    print("h_n vs n^2+3n+1 :", "MATCH" if h == explicit else f"DIFFER {h} != {explicit}")
    print("\nOverall:", "PASS" if passed else "FAIL")
    print("\n(New families: add a (a,b,c) and a conjectured closed_ratio, then run.\n"
          " A PASS here is the prerequisite gate before any Lean formalization.)")
