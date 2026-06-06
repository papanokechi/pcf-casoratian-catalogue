# pcf-casoratian-catalogue

> **Disambiguation / status.** This repository is a *methodology scaffold* with
> **no mathematical results yet** — it defines the gate line for *future*
> machine-checkable Casoratian closed forms. It is **distinct from** the
> published companion repository
> [`papanokechi/pcf-casoratian-identities`](https://github.com/papanokechi/pcf-casoratian-identities),
> which accompanies the deposited paper *"Polynomial Continued Fractions: a
> Proved Logarithmic Ladder, a 4/π Casoratian Identity, and 482 Irrational
> Constants"* (Zenodo concept DOI
> [10.5281/zenodo.19491767](https://doi.org/10.5281/zenodo.19491767)) and contains
> the real, finished 4/π Casoratian-identity result. Nothing in *this* repository
> is deposited or claimed as a result; no entry exists until a genuinely new
> family passes `harness_caso.py` and reaches a clean Lean axiom cone (see
> Workflow below). Do **not** tag or deposit this repository as a result until
> then.

A catalogue of machine-checkable Casoratian closed forms for polynomial
continued fractions (PCFs), following the conditional-core pattern proven on the
deposited 4/pi PCF. This is the "guaranteed-clean-deposit" track: it formalizes
finitary algebraic identities with NO analytic hypothesis, so each entry can
reach a clean Lean axiom cone.

## Pattern

For a reduced three-term recurrence with two solutions h, g, the Casoratian
    W_n = h_n g_{n-1} - h_{n-1} g_n
obeys a first-order law W_n = (ratio_n) W_{n-1}, hence a closed product form.
Instantiate with a polynomial solution h_n and the convergent denominators g_n.

Worked deposited example (self-test gate, see harness_caso.py):
    4/pi PCF reduced recurrence (2n-1) x_n = (3n+1) x_{n-1} - n x_{n-2}
    => W_n = n! / (2n-1)!! * W_1   (confirmed n=1..8)
    h_n = n^2 + 3n + 1   (verified solution)

## Workflow per new family (gate BEFORE Lean)

1. Choose a PCF family; write its reduced 3-term recurrence.
2. Conjecture the closed Casoratian ratio.
3. Pass the sympy gate in harness_caso.py (exact rational match over n=1..N).
   A PASS is the prerequisite; a FAIL kills the conjecture cheaply.
4. ONLY THEN formalize the finitary core in Lean 4 / Mathlib and verify the
   axiom cone is exactly {propext, Classical.choice, Quot.sound}, zero sorry.
5. Deposit: tag a release; Zenodo concept DOI as isSupplementTo target.

## Epistemic status (four-grade SIARC convention)

- PROVEN  = clean Lean axiom cone {propext, Classical.choice, Quot.sound}, zero sorry.
- VERIFIED = sympy exact-rational gate passes for the stated finite range.
- STRUCTURAL = hand/symbolic argument, not machine-checked.
- CONJECTURED = believed, not yet established.

A catalogue entry is depositable at grade PROVEN only after step 4.

## Layout

    harness_caso.py   sympy gate self-test (run: python harness_caso.py)
    verify/           (later) Lean finitary cores, one per family + cone_check
    LICENSE           Apache-2.0

License: Apache-2.0.
