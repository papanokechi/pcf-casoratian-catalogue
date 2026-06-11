/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-!
# Higher-order Casoratians for polynomial continued fractions (Abel–Jacobi–Liouville law)

**New research space.**  The deposited PCF corpus formalizes only *order-2*
(three-term) recurrences: the Casoratian (discrete Wronskian) of two solutions
flips sign / scales by the lower coefficient (`casoratian_stepG`,
`casoratian_eqG`), and the convergent Wronskian `p(n+1)q(n) - p(n)q(n+1) = (-1)^n`
is the certificate behind Euler's irrationality criterion.

This file opens the *order ≥ 3* direction, the algebraic backbone of **simultaneous
/ Hermite–Padé approximation** (the engine of Apéry-type irrationality proofs).  For
the order-3 linear recurrence

  `s (n+3) = c₂ n · s (n+2) + c₁ n · s (n+1) + c₀ n · s n`

the order-3 Casoratian `C n` (the 3×3 discrete Wronskian of three solutions) obeys
the **Abel–Jacobi–Liouville first-order law**

  `C (n+1) = c₀ n · C n`,    hence   `C n = (∏_{m<n} c₀ m) · C 0`.

Only the *lowest* coefficient `c₀` enters; `c₁, c₂` cancel.  The sign is `(-1)^{k-1}`
for order `k`: at order 2 it is `-(c₀ n)` (the corpus sign, reproduced here as the
faithfulness witness `caso2_step`); at order 3 it is `+(c₀ n)`.

Everything here is finitary algebra over an arbitrary `CommRing` — no analysis, no
extra axioms beyond Mathlib defaults — so each result reaches a clean axiom cone.

## Results
* `caso2_step`  — order-2 faithfulness witness: `C₂(n+1) = -(c₀ n)·C₂ n` (corpus sign).
* `caso3_step`  — order-3 Abel–Jacobi step: `C₃(n+1) = (c₀ n)·C₃ n`.
* `caso3_eq`    — order-3 closed product form: `C₃ n = (∏_{m<n} c₀ m)·C₃ 0`.
* `caso3_eq_const` — constant-`c₀` specialization `C₃ n = (c₀)^n · C₃ 0`.
* `caso3_ne_zero_of_init` — non-degeneracy: if every `c₀ m` and `C₃ 0` are units/nonzero
  in a domain, `C₃ n ≠ 0` (the higher-order independence certificate).
-/

namespace PcfHigherCaso

variable {R : Type*} [CommRing R]

/-! ## Order-2 faithfulness witness (the corpus sign `(-1)^{2-1} = -1`) -/

/-- Order-2 linear recurrence `s (n+2) = c₁ n · s (n+1) + c₀ n · s n`. -/
def IsSol2 (c0 c1 s : ℕ → R) : Prop :=
  ∀ n, s (n + 2) = c1 n * s (n + 1) + c0 n * s n

/-- Order-2 Casoratian (2×2 discrete Wronskian), determinant of
`![![y n, z n], ![y (n+1), z (n+1)]]`. -/
def caso2 (y z : ℕ → R) (n : ℕ) : R :=
  y n * z (n + 1) - y (n + 1) * z n

/-- **Order-2 Casoratian step.**  Reproduces the corpus law: the 2×2 Casoratian
scales by `-(c₀ n)` each step (sign `(-1)^{2-1}`). -/
theorem caso2_step {c0 c1 y z : ℕ → R}
    (hy : IsSol2 c0 c1 y) (hz : IsSol2 c0 c1 z) (n : ℕ) :
    caso2 y z (n + 1) = -(c0 n) * caso2 y z n := by
  simp only [caso2, show n + 1 + 1 = n + 2 from rfl, hy n, hz n]
  ring

/-! ## Order-3 Casoratian and the Abel–Jacobi–Liouville law -/

/-- Order-3 linear recurrence `s (n+3) = c₂ n · s (n+2) + c₁ n · s (n+1) + c₀ n · s n`. -/
def IsSol3 (c0 c1 c2 s : ℕ → R) : Prop :=
  ∀ n, s (n + 3) = c2 n * s (n + 2) + c1 n * s (n + 1) + c0 n * s n

/-- The order-3 Casoratian (3×3 discrete Wronskian) of three sequences: the
determinant of the matrix whose rows are the shifts `n, n+1, n+2` and whose columns
are `y, z, w` (cofactor-expanded along the first row). -/
def caso3 (y z w : ℕ → R) (n : ℕ) : R :=
  y n * (z (n + 1) * w (n + 2) - w (n + 1) * z (n + 2))
  - z n * (y (n + 1) * w (n + 2) - w (n + 1) * y (n + 2))
  + w n * (y (n + 1) * z (n + 2) - z (n + 1) * y (n + 2))

/-- **Order-3 Casoratian step (Abel–Jacobi–Liouville).**  For three solutions of the
same order-3 recurrence, the Casoratian scales by `c₀ n` (sign `(-1)^{3-1} = +1`) at
each step.  Independent of `c₁, c₂` — only the lowest coefficient enters. -/
theorem caso3_step {c0 c1 c2 y z w : ℕ → R}
    (hy : IsSol3 c0 c1 c2 y) (hz : IsSol3 c0 c1 c2 z) (hw : IsSol3 c0 c1 c2 w) (n : ℕ) :
    caso3 y z w (n + 1) = c0 n * caso3 y z w n := by
  simp only [caso3, show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl,
    hy n, hz n, hw n]
  ring

/-- **Order-3 Casoratian closed product form.**  Hence the Casoratian equals
`(∏_{m<n} c₀ m)` times its value at `0`. -/
theorem caso3_eq {c0 c1 c2 y z w : ℕ → R}
    (hy : IsSol3 c0 c1 c2 y) (hz : IsSol3 c0 c1 c2 z) (hw : IsSol3 c0 c1 c2 w) (n : ℕ) :
    caso3 y z w n = (∏ m ∈ Finset.range n, c0 m) * caso3 y z w 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [caso3_step hy hz hw k, ih, Finset.prod_range_succ]
      ring

/-- Constant lower-coefficient specialization: if `c₀ ≡ a` then `C₃ n = aⁿ · C₃ 0`. -/
theorem caso3_eq_const {a : R} {c0 c1 c2 y z w : ℕ → R}
    (hc0 : ∀ m, c0 m = a)
    (hy : IsSol3 c0 c1 c2 y) (hz : IsSol3 c0 c1 c2 z) (hw : IsSol3 c0 c1 c2 w) (n : ℕ) :
    caso3 y z w n = a ^ n * caso3 y z w 0 := by
  rw [caso3_eq hy hz hw n]
  congr 1
  rw [Finset.prod_congr rfl (fun m _ => hc0 m), Finset.prod_const, Finset.card_range]

end PcfHigherCaso

/-! ## Non-degeneracy over an integral domain (the independence certificate) -/

namespace PcfHigherCaso

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Higher-order independence certificate.**  Over an integral domain, if the initial
Casoratian and every lower coefficient `c₀ m` are nonzero, then `C₃ n ≠ 0` for all `n`:
the three solutions stay linearly independent at every window.  This is the order-3
analogue of the corpus's `p(n+1)q(n) - p(n)q(n+1) = (-1)^n ≠ 0`. -/
theorem caso3_ne_zero_of_init {c0 c1 c2 y z w : ℕ → R}
    (hy : IsSol3 c0 c1 c2 y) (hz : IsSol3 c0 c1 c2 z) (hw : IsSol3 c0 c1 c2 w)
    (h0 : caso3 y z w 0 ≠ 0) (hc : ∀ m, c0 m ≠ 0) (n : ℕ) :
    caso3 y z w n ≠ 0 := by
  rw [caso3_eq hy hz hw n]
  apply mul_ne_zero _ h0
  exact Finset.prod_ne_zero_iff.mpr (fun m _ => hc m)

end PcfHigherCaso
