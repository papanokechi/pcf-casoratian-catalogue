# pcf-casoratian-catalogue

> **Disambiguation / status.** This repository is the *machine-checkable
> Casoratian closed-form catalogue*. It now holds its **first proven entry** — the
> higher-order (order ≥ 3) Casoratian Abel–Jacobi–Liouville law (entry **C1**
> below). It remains **distinct from** the
> published companion repository
> [`papanokechi/pcf-casoratian-identities`](https://github.com/papanokechi/pcf-casoratian-identities),
> which accompanies the deposited paper *"Polynomial Continued Fractions: a
> Proved Logarithmic Ladder, a 4/π Casoratian Identity, and 482 Irrational
> Constants"* (Zenodo concept DOI
> [10.5281/zenodo.19491767](https://doi.org/10.5281/zenodo.19491767)) and contains
> the real, finished 4/π Casoratian-identity result. The admission discipline is
> unchanged: an entry counts only once it passes the `harness_caso*.py` gate **and**
> reaches a clean Lean axiom cone (see Workflow below). Tag/deposit stay
> operator-gated; do **not** deposit this repository without operator sign-off.

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

## Catalogue entries

### C1 — Higher-order Casoratian (order ≥ 3, now uniform in `k`): the Abel–Jacobi–Liouville law · PROVEN

The deposited corpus formalizes only **order-2** (three-term) Casoratians. C1 opens
the **order ≥ 3** space — the algebraic backbone of *simultaneous / Hermite–Padé*
approximation (the engine of Apéry-type irrationality proofs). For the order-`k`
linear recurrence

    s(n+k) = Σ_{j=0}^{k-1} c_j(n) · s(n+j),

the order-`k` Casoratian (the `k×k` discrete Wronskian of `k` solutions)
`C(n) = det[ s^(t)(n+i) ]_{0 ≤ i,t < k}` obeys the **first-order law**

    C(n+1) = (-1)^{k-1} · c_0(n) · C(n),
    C(n)   = ( Π_{m<n} (-1)^{k-1} c_0(m) ) · C(0).

Only the **lowest** coefficient `c_0` survives; `c_1 … c_{k-1}` cancel. At `k = 2`
the sign is the corpus `-(c_0 n)`; at `k = 3` it is `+(c_0 n)`. The
`(-1)^{k-1}` sign is now established as a **single uniform theorem over all `k`**
(`verify/GeneralCaso.lean`), not merely the `k = 2, 3` instances.

| grade | object | location |
|-------|--------|----------|
| **PROVEN** | `casoMat_det_step` — uniform-in-`k` step `C(n+1) = (-1)^k·c₀(n)·C(n)` | `verify/GeneralCaso.lean` |
| **PROVEN** | `casoMat_det_eq` — uniform closed form `C(n) = (Π_{m<n} (-1)^k c₀ m)·C(0)` | ″ |
| **PROVEN** | `casoMat_det_eq_const` — constant-`c₀` power form `C(n) = ((-1)^k c₀)ⁿ·C(0)` | ″ |
| **PROVEN** | `casoMat_det_ne_zero_of_init` — domain non-degeneracy at all `k` | ″ |
| **PROVEN** | `caso3_step` — order-3 step `C₃(n+1) = c₀(n)·C₃(n)` | `verify/HigherCaso.lean` |
| **PROVEN** | `caso3_eq` — closed product form `C₃(n) = (Π_{m<n} c₀ m)·C₃(0)` | ″ |
| **PROVEN** | `caso3_eq_const` — constant-`c₀` case `C₃(n) = c₀ⁿ·C₃(0)` | ″ |
| **PROVEN** | `caso3_ne_zero_of_init` — domain non-degeneracy `C₃(n) ≠ 0` (independence certificate) | ″ |
| **PROVEN** | `caso2_step` — order-2 faithfulness witness `C₂(n+1) = -c₀(n)·C₂(n)` | ″ |
| **VERIFIED** | symbolic proof `k=3` + exact-rational `k=2..7` + named instances | `harness_caso_k.py` |

**Note (matrix convention).** `GeneralCaso.lean` indexes the order `k+1` by
`Fin (k+1)`, so its sign reads `(-1)^k` for the order-`(k+1)` Casoratian; with the
prose's order-`k` indexing this is the same `(-1)^{k-1}`. The general step is proved
by rewriting the last row of `C(n+1)` via the recurrence into a linear combination
of the **cyclically rotated** rows of `C(n)`: `Matrix.det_updateRow_sum` collapses
the combination to its `c₀` coefficient and `sign_finRotate` supplies the cyclic
sign `(-1)^k`. `HigherCaso.lean`'s by-hand `k = 2, 3` proofs remain as independent
faithfulness witnesses.

**Cone (the PROVEN gate).** All nine Lean theorems have axiom cones ⊆
`{propext, Classical.choice, Quot.sound}` with no `sorryAx` (the order-2/3 `_step`
lemmas need only `{propext, Quot.sound}`); the sources have zero
`sorry`/`admit`/`native_decide`. `verify/HigherCaso.lean` and
`verify/GeneralCaso.lean` are built and
cone-checked under the pinned `leanprover/lean4:v4.30.0` + Mathlib `v4.30.0`
toolchain inside the companion `pcf-delta` `PcfContinuant` project and its
`Check.lean` gate, where C1 is cross-listed alongside the order-2 general
Casoratian (`casoratian_eqG`).

**Named instances** (`harness_caso_k.py`): the Tribonacci-type recurrence
`s(n+3) = s(n+2)+s(n+1)+s(n)` (`c₀ ≡ 1`) has a *constant* Casoratian; the
recurrence with `c₀(n) = n+1` gives `C(n) = n!·C(0)`.

**Positioning / related Zenodo deposits (novelty check, 2026-06-10).** A scan of
the depositor's public corpus (ORCID `0009-0000-6192-8273`, 36 records) confirms
the Casoratian line was previously **order-2 only**; C1 is the first order-≥3
result. Direct predecessors this entry *continues* / *supplements*:

| relation | work | concept DOI |
|----------|------|-------------|
| continues | Lean formalization of the 4/π Casoratian closed form (Thm 6.3), **order-2** | [10.5281/zenodo.20500490](https://doi.org/10.5281/zenodo.20500490) |
| isSupplementTo | ladder paper — *Proved Logarithmic Ladder, 4/π Casoratian Identity, 482 Constants* | [10.5281/zenodo.19491767](https://doi.org/10.5281/zenodo.19491767) |
| isPartOf | companion `pcf-delta` (hosts the built Lean core + `Check.lean` gate) | [10.5281/zenodo.20578400](https://doi.org/10.5281/zenodo.20578400) |
| isPartOf | SIARC program statement | [10.5281/zenodo.19885549](https://doi.org/10.5281/zenodo.19885549) |

**Open / next (CONJECTURED).** A concrete simultaneous-Hermite–Padé PCF whose
order-3 Casoratian furnishes an Apéry-style irrationality certificate. The
`(-1)^{k-1}` uniform-`k` sign theorem, previously listed open here, is now
**PROVEN** (`casoMat_det_step`, gate-checked for all `k`).

## Layout

    harness_caso.py     order-2 sympy gate self-test (run: python harness_caso.py)
    harness_caso_k.py   order-k gate for entry C1: symbolic k=3 proof + exact-rational
                        k=2..7 + named instances (run: python harness_caso_k.py)
    verify/             Lean finitary cores, one per family + cone check
      HigherCaso.lean   entry C1 — order-2/3 Casoratian, by-hand (PROVEN; built and
                        cone-checked in the pinned pcf-delta PcfContinuant project)
      GeneralCaso.lean  entry C1 — uniform order-(k+1) Casoratian law (PROVEN; same
                        gate; the single-theorem general-k companion to HigherCaso)
    .zenodo.json        deposit metadata (Zenodo native; operator-gated, NOT YET
                        DEPOSITED — see notes field)
    CITATION.cff        citation metadata (CFF 1.2.0; DOI block added at deposit time)
    LICENSE             Apache-2.0

License: Apache-2.0.
