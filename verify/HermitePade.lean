/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import PcfContinuant.GeneralCaso
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Hermite–Padé / Apéry irrationality certificate from the Casoratian fundamental set

This file instantiates the machine-checked **fundamental set** of `GeneralCaso.lean`
on a concrete order-`3` (i.e. `k = 2`) linear recurrence and uses it to produce a
machine-checked **irrationality certificate** of Hermite–Padé / Apéry type.

The point is that the Casoratian (discrete Wronskian) does *real* number-theoretic
work. For an order-`(k+1)` recurrence with solutions `s 0, …, s k`, the window of a
linear form is exactly a matrix–vector product against the Casoratian matrix:
`(s‑window at n) = casoMat s n *ᵥ a`, where `a` are the form's coefficients
(`caso_mulVec_apply`). Hence when the Casoratian is non‑vanishing the matrix is
injective and a *nontrivial* linear form `Lₙ = ∑ t, a t · s t n` **cannot vanish on a
full window of `k+1` consecutive indices** (`linForm_window_ne_zero`). In particular
such a form is **frequently nonzero** (`linForm_frequently_ne_zero`). This is precisely
the non‑degeneracy that the Apéry/Hermite–Padé irrationality machinery consumes.

We combine this with the classical **irrationality criterion**
(`irrational_of_linearForm_frequently`): if integer sequences `p, q` give a linear
form `q n · α − p n` that is frequently nonzero and tends to `0`, then `α` is
irrational. The non‑vanishing input to the criterion is *discharged structurally* by
the Casoratian; the only genuinely analytic input is the limit `→ 0`, kept as a
labelled hypothesis in the project's established style (cf. Topic 3, Topic 5).

The capstone `irrational_of_fundamentalSet_form` packages this for an arbitrary
fundamental set over `ℤ` with a **real** coefficient vector `v` (the remainder
`q n · α − p n = ∑ t, v t · s t n` is then a genuine non-integer real that may shrink
to `0`, as the criterion requires). The non-vanishing input is discharged by casting the
nonzero integer Casoratian into `ℝ` (`RingHom.map_det` + `Int.cast` injectivity).

Two concrete order-`3` witnesses are given:
* the geometric recurrence `u (n+3) = 6·u (n+2) − 11·u (n+1) + 6·u n` with characteristic
  roots `1, 2, 3`, fundamental set `{1, 2ⁿ, 3ⁿ}`, explicit non-vanishing Casoratian
  `C(n) = 2·6ⁿ` (`gcaso_ne_zero`) and the "no three consecutive zeros" window certificate
  `geom_window_ne_zero`;
* the recurrence `u (n+3) = 2·u (n+2) − u n` with roots `φ, ψ, 1`, fundamental set
  `{1, Fₙ, Fₙ₊₁}` and the shrinking Hermite–Padé remainder `Fₙ·φ − Fₙ₊₁ = −ψⁿ → 0`,
  which re-proves `Irrational φ` **through the Casoratian fundamental set**
  (`goldenRatio_irrational_via_caso`) — an independent route from Mathlib's `√5`-based
  `Real.goldenRatio_irrational`.
-/

namespace PcfHermitePade

open scoped BigOperators
open scoped goldenRatio
open Matrix Filter Topology PcfGeneralCaso Real

variable {R : Type*} [CommRing R] {k : ℕ}

/-! ## The linear form as a Casoratian matrix–vector product -/

/-- The `i`-th entry of `casoMat s n *ᵥ a` is the value at index `n + i` of the linear
form `∑ t, a t · s t` with coefficient vector `a`. This is the bridge that turns the
combinatorics of linear forms into linear algebra over the Casoratian matrix. -/
theorem caso_mulVec_apply (s : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R)
    (n : ℕ) (i : Fin (k + 1)) :
    (casoMat s n *ᵥ a) i = ∑ t, a t * s t (n + (i : ℕ)) := by
  simp only [casoMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)

/-- **Window non‑vanishing certificate.** Over an integral domain, if the Casoratian
`(casoMat s n).det` is nonzero, then a *nontrivial* linear form `∑ t, a t · s t`
(coefficients `a ≠ 0`) cannot vanish simultaneously at all `k+1` consecutive indices
`n, n+1, …, n+k`. Equivalently: the only coefficient vector annihilating a full window
is the zero vector. This is the converse companion to `solution_isLinearCombo`: there
the Casoratian unit produced coordinates `a ↦ L`; here non‑vanishing makes `L ↦ a`
injective on windows. -/
theorem linForm_window_ne_zero [IsDomain R]
    (s : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R) (ha : a ≠ 0)
    (n : ℕ) (hdet : (casoMat s n).det ≠ 0) :
    ∃ i : Fin (k + 1), (∑ t, a t * s t (n + (i : ℕ))) ≠ 0 := by
  by_contra hcon
  apply ha
  have hv : casoMat s n *ᵥ a = 0 := by
    funext i
    simp only [Pi.zero_apply]
    rw [caso_mulVec_apply]
    by_contra hi
    exact hcon ⟨i, hi⟩
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hv

/-- **Frequent non‑vanishing.** If the Casoratian is nonzero at every index, then a
nontrivial linear form `∑ t, a t · s t` is nonzero for infinitely many indices: it is
*frequently* nonzero along `atTop`. (A full window `{N, …, N+k}` always contains a
nonzero value, and that index is `≥ N`.) -/
theorem linForm_frequently_ne_zero [IsDomain R]
    (s : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R) (ha : a ≠ 0)
    (hdet : ∀ n, (casoMat s n).det ≠ 0) :
    ∃ᶠ n in atTop, (∑ t, a t * s t n) ≠ 0 := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨i, hi⟩ := linForm_window_ne_zero s a ha N (hdet N)
  exact ⟨N + (i : ℕ), Nat.le_add_right N (i : ℕ), hi⟩

/-! ## The irrationality criterion -/

/-- **Irrationality criterion (standard linear-form criterion).** Let `α : ℝ` and let
`p q : ℕ → ℤ`. If the integer linear form `q n · α − p n` is *frequently nonzero* and
*tends to `0`*, then `α` is irrational.

Proof: if `α = na / nb` were rational with `nb ≠ 0`, then `nb · (q n α − p n)` is the
integer `q n · na − nb · p n`; whenever the form is nonzero this integer is nonzero,
hence has absolute value `≥ 1`, forcing `|q n α − p n| ≥ 1/|nb|`. That positive lower
bound holds frequently, contradicting convergence to `0`. -/
theorem irrational_of_linearForm_frequently
    (α : ℝ) (p q : ℕ → ℤ)
    (hfreq : ∃ᶠ n in atTop, (q n : ℝ) * α - p n ≠ 0)
    (htend : Tendsto (fun n => (q n : ℝ) * α - p n) atTop (𝓝 0)) :
    Irrational α := by
  rw [irrational_iff_ne_rational]
  intro na nb hnb hα
  have hnbR : (nb : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hnb
  have hbabs : (0 : ℝ) < |(nb : ℝ)| := abs_pos.mpr hnbR
  set c : ℝ := 1 / |(nb : ℝ)| with hcdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hba : (nb : ℝ) * α = (na : ℝ) := by rw [hα]; field_simp
  have bound : ∀ n, ((q n : ℝ) * α - p n ≠ 0) → c ≤ |(q n : ℝ) * α - p n| := by
    intro n hn
    set f : ℝ := (q n : ℝ) * α - p n with hf
    have hfm : (nb : ℝ) * f = ((q n * na - nb * p n : ℤ) : ℝ) := by
      have e1 : (nb : ℝ) * f
          = (q n : ℝ) * ((nb : ℝ) * α) - (nb : ℝ) * (p n : ℝ) := by rw [hf]; ring
      rw [e1, hba]; push_cast; ring
    have hbf : (nb : ℝ) * f ≠ 0 := mul_ne_zero hnbR hn
    rw [hfm] at hbf
    have hm0 : (q n * na - nb * p n) ≠ 0 := Int.cast_ne_zero.mp hbf
    have h1 : (1 : ℤ) ≤ |q n * na - nb * p n| := by
      rw [Int.abs_eq_natAbs]
      have hpos := Int.natAbs_pos.mpr hm0
      omega
    have h1R : (1 : ℝ) ≤ |(nb : ℝ)| * |f| := by
      have hcast : ((|q n * na - nb * p n| : ℤ) : ℝ) = |(nb : ℝ)| * |f| := by
        rw [Int.cast_abs, ← hfm, abs_mul]
      rw [← hcast]; exact_mod_cast h1
    have hkey : c * |(nb : ℝ)| = 1 := by
      rw [hcdef]; exact one_div_mul_cancel (ne_of_gt hbabs)
    have hmul : c * |(nb : ℝ)| ≤ |f| * |(nb : ℝ)| := by rw [hkey, mul_comm]; exact h1R
    exact le_of_mul_le_mul_right hmul hbabs
  have hball : ∀ᶠ n in atTop, (q n : ℝ) * α - p n ∈ Metric.ball (0 : ℝ) c :=
    htend.eventually_mem (Metric.ball_mem_nhds 0 hc)
  have hev : ∀ᶠ n in atTop, |(q n : ℝ) * α - p n| < c := by
    filter_upwards [hball] with n hn
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hn
    exact hn
  obtain ⟨n, hne, hlt⟩ := (hfreq.and_eventually hev).exists
  exact absurd (bound n hne) (not_le.mpr hlt)

/-! ## Capstone: irrationality from a Casoratian fundamental set -/

/-- **Irrationality certificate from a fundamental set.** Let `s : Fin (k+1) → ℕ → ℤ`
be a family of integer solutions whose integer Casoratian `(casoMat s n).det` is nonzero
for every `n` — a machine‑checked fundamental set over `ℤ`. Let `v : Fin (k+1) → ℝ` be a
*real* coefficient vector with `v ≠ 0`. Suppose the real remainder `∑ t, v t · s t n`
equals the `α`‑linear form `q n · α − p n` (the Hermite–Padé linkage `hlink`) and tends to
`0` (the single labelled analytic hypothesis `htend`). Then `α` is irrational.

The decisive point — and what makes this certificate genuinely *non‑vacuous* — is that the
coefficients `v` are **real**, not integer: the remainder `q n · α − p n` is then a true
non‑integer real that can shrink to `0` (as the criterion demands), while the underlying
solutions `s t n` stay integer. The "frequently nonzero" hypothesis of the criterion is
supplied *for free* by the Casoratian fundamental set: casting the nonzero integer
Casoratian into `ℝ` (via `Int.cast_det` and `Int.cast` injectivity) keeps it nonzero,
so `linForm_frequently_ne_zero` makes the real remainder frequently nonzero. -/
theorem irrational_of_fundamentalSet_form
    (s : Fin (k + 1) → ℕ → ℤ)
    (hdet : ∀ n, (casoMat s n).det ≠ 0)
    (α : ℝ) (p q : ℕ → ℤ) (v : Fin (k + 1) → ℝ) (hv : v ≠ 0)
    (hlink : ∀ n, (q n : ℝ) * α - p n = ∑ t, v t * (s t n : ℝ))
    (htend : Tendsto (fun n => (q n : ℝ) * α - p n) atTop (𝓝 0)) :
    Irrational α := by
  refine irrational_of_linearForm_frequently α p q ?_ htend
  have hfreq : ∃ᶠ n in atTop, (∑ t, v t * (s t n : ℝ)) ≠ 0 := by
    refine linForm_frequently_ne_zero (fun t n => (s t n : ℝ)) v hv ?_
    intro n
    have hmap : casoMat (fun t m => (s t m : ℝ)) n
        = (casoMat s n).map (fun x : ℤ => (x : ℝ)) := by
      ext i j
      simp [casoMat, Matrix.map_apply, Matrix.of_apply]
    rw [hmap, ← Int.cast_det]
    exact Int.cast_ne_zero.mpr (hdet n)
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro N
  obtain ⟨b, hbN, hbne⟩ := hfreq N
  exact ⟨b, hbN, by rw [hlink b]; exact hbne⟩

/-! ## Concrete order‑3 witness: the geometric recurrence with roots `1, 2, 3`

`gsol t n = (t+1)ⁿ` for `t ∈ {0,1,2}` gives the three solutions `1, 2ⁿ, 3ⁿ` of
`u (n+3) = 6·u (n+2) − 11·u (n+1) + 6·u n` (characteristic polynomial
`(x−1)(x−2)(x−3) = x³ − 6x² + 11x − 6`). Its Casoratian is the Vandermonde
determinant times `6ⁿ`, namely `2 · 6ⁿ ≠ 0`. -/

/-- The three geometric solutions `1, 2ⁿ, 3ⁿ` packaged as `gsol t n = (t+1)ⁿ`. -/
def gsol (t : Fin 3) (n : ℕ) : ℤ := ((t : ℕ) + 1) ^ n

/-- Recurrence coefficients `(c₀, c₁, c₂) = (6, −11, 6)`. -/
def gc (j : Fin 3) (_n : ℕ) : ℤ := ![6, -11, 6] j

/-- Each geometric solution satisfies the order‑3 recurrence
`s (n+3) = ∑ j, c j · s (n+j)`. -/
theorem gsol_rec (t : Fin 3) (n : ℕ) :
    gsol t (n + 3) = ∑ j : Fin 3, gc j n * gsol t (n + (j : ℕ)) := by
  simp only [gc, gsol, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.add_zero]
  fin_cases t <;> push_cast <;> ring

/-- The initial Casoratian of the geometric fundamental set is the Vandermonde
determinant `(2−1)(3−1)(3−2) = 2`. -/
theorem gcaso0 : (casoMat gsol 0).det = 2 := by
  rw [Matrix.det_fin_three]
  simp only [casoMat, Matrix.of_apply, gsol, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.zero_add]
  norm_num

/-- **Concrete fundamental set certificate.** The geometric Casoratian is nonzero at
every index: `(casoMat gsol n).det = 2 · 6ⁿ ≠ 0`. Hence `{1, 2ⁿ, 3ⁿ}` is a
machine‑checked fundamental set of the order‑3 recurrence. -/
theorem gcaso_ne_zero (n : ℕ) : (casoMat gsol n).det ≠ 0 := by
  refine casoMat_det_ne_zero_of_init gsol gc gsol_rec n ?_ ?_
  · rw [gcaso0]; norm_num
  · intro m _
    simp only [gc, Matrix.cons_val_zero]
    norm_num

/-- **Concrete window certificate.** A nontrivial integer combination
`a₀ · 1 + a₁ · 2ⁿ + a₂ · 3ⁿ` cannot vanish at three consecutive indices. -/
theorem geom_window_ne_zero (a : Fin 3 → ℤ) (ha : a ≠ 0) (n : ℕ) :
    ∃ i : Fin 3, (∑ t, a t * gsol t (n + (i : ℕ))) ≠ 0 :=
  linForm_window_ne_zero gsol a ha n (gcaso_ne_zero n)

/-! ## Concrete order‑3 irrationality certificate: the golden ratio via Fibonacci

The genuinely *non‑vacuous* witness. The order‑3 recurrence `u (n+3) = 2·u (n+2) − u n`
has characteristic polynomial `x³ − 2x² + 1 = (x² − x − 1)(x − 1)`, with roots `φ, ψ, 1`.
A fundamental set of integer solutions is `{1, Fₙ, Fₙ₊₁}` (the constant solution and two
shifts of Fibonacci); its initial Casoratian is `1` (a Cassini determinant), certified
here at every index by `casoMat_det_ne_zero_of_init`.

Because `|ψ| < 1`, the Hermite–Padé remainder shrinks: `Fₙ·φ − Fₙ₊₁ = −ψⁿ → 0` (Binet,
`Real.fib_succ_sub_goldenRatio_mul_fib`). Feeding this through the capstone with the
**real** coefficient vector `v = (0, φ, −1)` re‑derives `Irrational φ` entirely through the
discrete‑Wronskian (Casoratian) machinery — an independent route from Mathlib's `√5`‑based
`Real.goldenRatio_irrational`. This is the Apéry / Hermite–Padé mechanism in miniature. -/

/-- The order‑`3` fundamental set `{1, Fₙ, Fₙ₊₁}` of `u (n+3) = 2·u (n+2) − u n`. -/
def fibSol : Fin 3 → ℕ → ℤ :=
  ![fun _ => 1, fun n => (Nat.fib n : ℤ), fun n => (Nat.fib (n + 1) : ℤ)]

/-- Recurrence coefficients `(c₀, c₁, c₂) = (−1, 0, 2)`. -/
def fibC : Fin 3 → ℕ → ℤ := fun j _ => ![(-1), 0, 2] j

/-- Each of `1, Fₙ, Fₙ₊₁` satisfies the order‑`3` recurrence `s (n+3) = ∑ j, c j · s (n+j)`,
i.e. `s (n+3) = −s n + 2·s (n+2)`. -/
theorem fibSol_rec (t : Fin 3) (n : ℕ) :
    fibSol t (n + 3) = ∑ j : Fin 3, fibC j n * fibSol t (n + (j : ℕ)) := by
  have key : ∀ m : ℕ, (Nat.fib (m + 3) : ℤ) = 2 * Nat.fib (m + 2) - Nat.fib m := by
    intro m
    have a : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have b : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    omega
  fin_cases t <;>
    simp only [Fin.sum_univ_three, fibC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · change (1 : ℤ) = -1 * 1 + 0 * 1 + 2 * 1; norm_num
  · change (Nat.fib (n + 3) : ℤ) = -1 * Nat.fib n + 0 * Nat.fib (n + 1) + 2 * Nat.fib (n + 2)
    have h := key n; linarith [h]
  · change (Nat.fib (n + 3 + 1) : ℤ)
        = -1 * Nat.fib (n + 1) + 0 * Nat.fib (n + 1 + 1) + 2 * Nat.fib (n + 2 + 1)
    have h := key (n + 1)
    rw [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl] at h
    rw [show n + 3 + 1 = n + 4 from rfl, show n + 1 + 1 = n + 2 from rfl,
        show n + 2 + 1 = n + 3 from rfl]
    linarith [h]

/-- The initial Casoratian of the Fibonacci fundamental set is the Cassini determinant
`det ![[1,0,1],[1,1,1],[1,1,2]] = 1`. -/
theorem fibCaso0 : (casoMat fibSol 0).det = 1 := by
  rw [Matrix.det_fin_three]
  simp only [casoMat, Matrix.of_apply, fibSol, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.zero_add]
  norm_num [Nat.fib_zero, Nat.fib_one, Nat.fib_two, show Nat.fib 3 = 2 from rfl]

/-- **Concrete fundamental set certificate.** The Fibonacci Casoratian is nonzero at every
index. Hence `{1, Fₙ, Fₙ₊₁}` is a machine‑checked fundamental set of the order‑`3`
recurrence `u (n+3) = 2·u (n+2) − u n`. -/
theorem fibCaso_ne_zero (n : ℕ) : (casoMat fibSol n).det ≠ 0 := by
  refine casoMat_det_ne_zero_of_init fibSol fibC fibSol_rec n ?_ ?_
  · rw [fibCaso0]; norm_num
  · intro m _
    simp only [fibC, Matrix.cons_val_zero]
    norm_num

/-- **The shrinking Hermite–Padé remainder.** `Fₙ·φ − Fₙ₊₁ = −ψⁿ → 0`, because `|ψ| < 1`.
This is the single analytic ingredient; everything else is the Casoratian. -/
theorem fib_remainder_tendsto :
    Tendsto (fun n => (Nat.fib n : ℝ) * φ - (Nat.fib (n + 1) : ℝ)) atTop (𝓝 0) := by
  have hpsi : |ψ| < 1 := by
    rw [abs_lt]
    exact ⟨neg_one_lt_goldenConj, lt_trans goldenConj_neg one_pos⟩
  have hpow : Tendsto (fun n => ψ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hpsi
  have hneg : Tendsto (fun n => -ψ ^ n) atTop (𝓝 0) := by
    simpa using hpow.neg
  refine hneg.congr (fun n => ?_)
  have hc : (Nat.fib (n + 1) : ℝ) - φ * (Nat.fib n : ℝ) = ψ ^ n :=
    fib_succ_sub_goldenRatio_mul_fib n
  have : (Nat.fib n : ℝ) * φ - (Nat.fib (n + 1) : ℝ) = -(ψ ^ n) := by
    rw [← hc]; ring
  rw [this]

/-- **Concrete irrationality certificate (golden ratio).** The order‑`3` Casoratian
fundamental set `{1, Fₙ, Fₙ₊₁}` together with the shrinking remainder
`Fₙ·φ − Fₙ₊₁ = −ψⁿ → 0` proves the golden ratio irrational — entirely through the
discrete‑Wronskian machinery (`fibCaso_ne_zero` and the capstone
`irrational_of_fundamentalSet_form`), an independent route from Mathlib's `√5`‑based proof.
This instantiates the §7 fundamental set on a concrete order‑`3` Hermite–Padé recurrence to
yield a machine‑checked irrationality certificate. -/
theorem goldenRatio_irrational_via_caso : Irrational φ := by
  refine irrational_of_fundamentalSet_form fibSol fibCaso_ne_zero φ
    (fun n => (Nat.fib (n + 1) : ℤ)) (fun n => (Nat.fib n : ℤ)) ![0, φ, -1] ?_ ?_ ?_
  · intro h
    have h2 := congrFun h 2
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  · intro n
    rw [Fin.sum_univ_three]
    simp only [fibSol, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    push_cast
    ring
  · have h := fib_remainder_tendsto
    refine h.congr (fun n => ?_)
    push_cast
    ring

end PcfHermitePade
