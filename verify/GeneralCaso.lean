/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

/-!
# The general-order (order `k+1`) Casoratian law

This file proves the Abel–Jacobi–Liouville law for the discrete Wronskian
(Casoratian) of a homogeneous linear recurrence of **arbitrary** order `k+1`,
uniformly in `k`. It is the general-`k` companion to `HigherCaso.lean`, which
established the `k = 2, 3` instances by hand.

For `k+1` sequences `s 0, …, s k : ℕ → R` that all satisfy the order-`k+1`
recurrence
`s t (n + (k+1)) = ∑ j, c j n * s t (n + j)`,
the Casoratian is the determinant of the `(k+1) × (k+1)` matrix whose `(i,t)`
entry is `s t (n + i)`:
`casoMat s n = Matrix.of (fun i t => s t (n + i))`.

The main result `casoMat_det_step` is
`(casoMat s (n+1)).det = (-1)^k * c 0 n * (casoMat s n).det`,
and `casoMat_det_eq` is its closed product form. Only the lowest coefficient
`c 0` survives; `c 1 … c k` cancel. At `k = 1` the sign is `-c 0` (the corpus
order-2 sign); at `k = 2` it is `+c 0` (the order-3 sign).

The proof is the classical one made finitary: the last row of `casoMat s (n+1)`
is, by the recurrence, a linear combination of the rows of the cyclically
rotated matrix `(casoMat s n).submatrix (finRotate (k+1)) id`; `det_updateRow_sum`
collapses that combination to its `c 0` coefficient, and `det_permute` with
`sign_finRotate` contributes the cyclic sign `(-1)^k`.
-/

namespace PcfGeneralCaso

open scoped BigOperators
open Matrix Equiv

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The `(k+1) × (k+1)` Casoratian matrix at index `n`: row `i` is the `i`-shift,
column `t` selects the `t`-th solution. Entry `(i,t)` is `s t (n + i)`. -/
def casoMat (s : Fin (k + 1) → ℕ → R) (n : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  Matrix.of fun i t => s t (n + (i : ℕ))

/-- **Abel–Jacobi–Liouville law, general order.** For any family of `k+1`
solutions of the order-`k+1` recurrence, the Casoratian satisfies the first-order
law `C(n+1) = (-1)^k · c₀(n) · C(n)`. Only the lowest coefficient survives. -/
theorem casoMat_det_step
    (s : Fin (k + 1) → ℕ → R) (c : Fin (k + 1) → ℕ → R)
    (hrec : ∀ (t : Fin (k + 1)) (n : ℕ),
      s t (n + (k + 1)) = ∑ j : Fin (k + 1), c j n * s t (n + (j : ℕ)))
    (n : ℕ) :
    (casoMat s (n + 1)).det = (-1) ^ k * c 0 n * (casoMat s n).det := by
  classical
  have key : casoMat s (n + 1)
      = ((casoMat s n).submatrix (finRotate (k + 1)) id).updateRow (Fin.last k)
          (∑ r, c (finRotate (k + 1) r) n •
            ((casoMat s n).submatrix (finRotate (k + 1)) id) r) := by
    ext i t
    by_cases hi : i = Fin.last k
    · subst hi
      rw [Matrix.updateRow_self, Finset.sum_apply]
      simp only [casoMat, Matrix.of_apply, Fin.val_last, Pi.smul_apply, smul_eq_mul,
        Matrix.submatrix_apply, id_eq]
      rw [Equiv.sum_comp (finRotate (k + 1)) fun j => c j n * s t (n + (j : ℕ)),
        ← hrec t n]
      congr 1
      omega
    · rw [Matrix.updateRow_ne hi]
      simp only [casoMat, Matrix.submatrix_apply, Matrix.of_apply, id_eq]
      rw [coe_finRotate_of_ne_last hi]
      congr 1
      omega
  rw [key, Matrix.det_updateRow_sum, Matrix.det_permute]
  simp only [finRotate_last, sign_finRotate, Nat.add_sub_cancel, smul_eq_mul]
  push_cast
  ring

/-- Closed product form of the general-order Casoratian law:
`C(n) = (∏_{m<n} (-1)^k · c₀(m)) · C(0)`. -/
theorem casoMat_det_eq
    (s : Fin (k + 1) → ℕ → R) (c : Fin (k + 1) → ℕ → R)
    (hrec : ∀ (t : Fin (k + 1)) (n : ℕ),
      s t (n + (k + 1)) = ∑ j : Fin (k + 1), c j n * s t (n + (j : ℕ)))
    (n : ℕ) :
    (casoMat s n).det
      = (∏ m ∈ Finset.range n, (-1) ^ k * c 0 m) * (casoMat s 0).det := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [casoMat_det_step s c hrec n, ih, Finset.prod_range_succ]
      ring

/-- Constant-lowest-coefficient case: if `c₀(m) = a` for all `m`, then
`C(n) = ((-1)^k · a)^n · C(0)`. -/
theorem casoMat_det_eq_const
    (s : Fin (k + 1) → ℕ → R) (c : Fin (k + 1) → ℕ → R) (a : R)
    (hrec : ∀ (t : Fin (k + 1)) (n : ℕ),
      s t (n + (k + 1)) = ∑ j : Fin (k + 1), c j n * s t (n + (j : ℕ)))
    (hc : ∀ m, c 0 m = a) (n : ℕ) :
    (casoMat s n).det = ((-1) ^ k * a) ^ n * (casoMat s 0).det := by
  rw [casoMat_det_eq s c hrec n]
  simp only [hc, Finset.prod_const, Finset.card_range]

/-- Non-degeneracy / linear-independence certificate. Over an integral domain, if
the initial Casoratian is nonzero and every lowest coefficient `c₀(m)` for `m < n`
is nonzero, then `C(n) ≠ 0`: the `k+1` solutions stay linearly independent. -/
theorem casoMat_det_ne_zero_of_init [IsDomain R]
    (s : Fin (k + 1) → ℕ → R) (c : Fin (k + 1) → ℕ → R)
    (hrec : ∀ (t : Fin (k + 1)) (n : ℕ),
      s t (n + (k + 1)) = ∑ j : Fin (k + 1), c j n * s t (n + (j : ℕ)))
    (n : ℕ) (h0 : (casoMat s 0).det ≠ 0)
    (hc : ∀ m ∈ Finset.range n, c 0 m ≠ 0) :
    (casoMat s n).det ≠ 0 := by
  rw [casoMat_det_eq s c hrec n]
  refine mul_ne_zero ?_ h0
  rw [Finset.prod_ne_zero_iff]
  intro m hm
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hc m hm)

end PcfGeneralCaso
