/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Balanced Vector Optimization

## Main Statement (Theorem Blueprint)

This file formalizes the following result:

**Theorem.** Let `D : E(n,d) → ℚ₊` be a function on weak compositions (n-tuples of
non-negative integers summing to d) satisfying:
1. **Sₙ-Symmetry**: `D(e ∘ σ⁻¹) = D(e)` for all permutations `σ`
2. **Log-concavity condition**: `D(e)² ≥ D(e - δᵢ + δⱼ) · D(e + δᵢ - δⱼ)`
   for all `i ≠ j` with `eᵢ, eⱼ ≥ 1`
3. **Strict positivity**: `D(e) > 0` for all `e`

Then:
- **(Maximum)** `D` is maximized on **balanced** vectors (where `|eᵢ - eⱼ| ≤ 1` for all i,j)
- **(Minimum)** `D` is minimized on **concentrated** vectors (where `e = d·δₖ` for some k)

## Key Definitions (for verification)

| Definition              | Location | Informal meaning                              |
|-------------------------|----------|-----------------------------------------------|
| `WeakComposition n d`   | line 112 | n-tuple `e : Fin n → ℤ` with `∑eᵢ = d`, `eᵢ ≥ 0` |
| `IsBalanced e`          | line 196 | `∀ i j, eᵢ ≤ eⱼ + 1 ∧ eⱼ ≤ eᵢ + 1`           |
| `IsConcentrated d e`    | line 200 | `∃ k, eᵢ = if i = k then d else 0`           |
| `IsSymmetric D`         | line 342 | `D(e ∘ σ⁻¹) = D(e)` for all `σ ∈ Sₙ`         |
| `SatisfiesLogConcavity D` | line 351 | the log-concavity condition above          |
| `IsStrictlyPositive D`  | line 357 | `D(e) > 0` for all `e`                       |

## Main Theorems (for verification)

**Primary reference (clean formulation at end of file):**

| Theorem                 | Location   | Statement                                    |
|-------------------------|------------|----------------------------------------------|
| `main_theorem`          | line 1108  | Combined statement of both results           |
| `maximized_on_balanced` | line 1081  | `∀ e, ∃ e', IsBalanced e' ∧ D(e) ≤ D(e')`   |
| `minimized_on_concentrated` | line 1095 | `∀ e, ∃ e', IsConcentrated e' ∧ D(e') ≤ D(e)`|

**Supporting structure:**

| Definition                      | Location   | Purpose                                |
|---------------------------------|------------|----------------------------------------|
| `SymmetricLogConcaveFunction`   | line 1059  | Bundles D with its three properties    |

**Implementation (used by the above):**

| Theorem                 | Location  | Statement                                    |
|-------------------------|-----------|----------------------------------------------|
| `balanced_maximizes`    | line 660  | Core proof for maximum result                |
| `concentrated_minimizes`| line 964  | Core proof for minimum result                |

## Proof Strategy

1. **Slice analysis**: For fixed i ≠ j, the "slice sequence" `s(t) = D(composition with
   eᵢ = t, eⱼ = q - t)` is shown to be log-concave and palindromic.

2. **Unimodality lemma** (`unimodal_of_logconcave_palindromic`, line 248): Log-concave
   palindromic sequences on `[0,q]` are unimodal (increasing then decreasing around q/2).

3. **Balancing increases D**: When `eᵢ - eⱼ ≥ 2`, the modification `eᵢ ↦ eᵢ - 1`,
   `eⱼ ↦ eⱼ + 1` moves toward the midpoint of the slice, increasing D.

4. **Concentrating decreases D**: When `eⱼ ≤ eᵢ`, moving mass from j to i moves
   away from the midpoint, decreasing D.

5. **Termination**: Balancing uses imbalance `∑ eᵢ²` (decreases strictly).
   Concentrating uses `d - maxEntry(e)` (decreases strictly until maxEntry = d).
-/

open Finset BigOperators Function

variable {n : ℕ}

/-! ### Reusable sum lemma for two-point updates -/

/-- Key lemma: extract two positions from a sum with nested if-then-else. -/
lemma sum_ite_ite_eq_add_add_sum_erase_erase
    (f : Fin n → ℤ) (i j : Fin n) (hij : i ≠ j) (a b : ℤ) :
    (∑ k, (if k = i then a else if k = j then b else f k))
      = a + b + ∑ k ∈ (univ.erase i).erase j, f k := by
  classical
  have hjmem : j ∈ (univ.erase i : Finset (Fin n)) :=
    mem_erase.mpr ⟨hij.symm, mem_univ j⟩
  -- First, split the sum: extract the i-th term
  have step1 : ∑ k, (if k = i then a else if k = j then b else f k) =
      a + ∑ k ∈ univ.erase i, (if k = j then b else f k) := by
    rw [← add_sum_erase _ _ (mem_univ i)]
    simp only [ite_true]
    congr 1
    apply sum_congr rfl
    intro k hk
    simp only [mem_erase, ne_eq] at hk
    simp only [hk.1, ite_false]
  -- Then, extract the j-th term from the remaining sum
  have step2 : ∑ k ∈ univ.erase i, (if k = j then b else f k) =
      b + ∑ k ∈ (univ.erase i).erase j, f k := by
    rw [← add_sum_erase _ _ hjmem]
    simp only [ite_true]
    congr 1
    apply sum_congr rfl
    intro k hk
    simp only [mem_erase, ne_eq] at hk
    simp only [hk.1, ite_false]
  calc ∑ k, (if k = i then a else if k = j then b else f k)
      = a + ∑ k ∈ univ.erase i, (if k = j then b else f k) := step1
    _ = a + (b + ∑ k ∈ (univ.erase i).erase j, f k) := by rw [step2]
    _ = a + b + ∑ k ∈ (univ.erase i).erase j, f k := by ring

/-! ### Weak Compositions (using ℤ for easier arithmetic) -/

/-- A weak composition of `d` into `n` parts is a vector `e : Fin n → ℤ` with
    `∑ eᵢ = d` and all entries non-negative. -/
structure WeakComposition (n : ℕ) (d : ℤ) where
  toFun : Fin n → ℤ
  sum_eq : ∑ i, toFun i = d
  nonneg : ∀ i, 0 ≤ toFun i

namespace WeakComposition

variable {d : ℤ}

instance : CoeFun (WeakComposition n d) (fun _ => Fin n → ℤ) := ⟨WeakComposition.toFun⟩

@[ext]
lemma ext {e e' : WeakComposition n d} (h : ∀ i, e i = e' i) : e = e' := by
  cases e; cases e'; simp only [mk.injEq]; funext i; exact h i

/-- The concentrated vector: all zeros except `d` at position `k`. -/
def concentrated (hd : 0 ≤ d) (k : Fin n) : WeakComposition n d where
  toFun := fun i => if i = k then d else 0
  sum_eq := by simp only [sum_ite_eq', mem_univ, ite_true]
  nonneg := fun i => by split_ifs <;> omega

@[simp]
lemma concentrated_at (hd : 0 ≤ d) (k : Fin n) : (concentrated hd k) k = d := by
  simp only [concentrated, ite_true]

@[simp]
lemma concentrated_ne (hd : 0 ≤ d) (k j : Fin n) (h : j ≠ k) : (concentrated hd k) j = 0 := by
  simp only [concentrated, h, ite_false]

/-- Auxiliary: the sum of a function that modifies two positions.
    This captures: if we change e at i to (e i - 1) and at j to (e j + 1),
    the total sum is preserved. -/
lemma sum_modify_eq {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (hsum : ∑ k, e k = d) :
    ∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k) = d := by
  classical
  have hmod : (∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k))
      = (e i - 1) + (e j + 1) + ∑ k ∈ (univ.erase i).erase j, e k := by
    simpa using sum_ite_ite_eq_add_add_sum_erase_erase e i j hij (e i - 1) (e j + 1)

  have hi_sum : e i + ∑ k ∈ univ.erase i, e k = d := by
    rw [add_sum_erase _ _ (mem_univ i), hsum]

  have hj_sum : e j + ∑ k ∈ (univ.erase i).erase j, e k = ∑ k ∈ univ.erase i, e k := by
    have hjmem : j ∈ (univ.erase i : Finset (Fin n)) :=
      mem_erase.mpr ⟨hij.symm, mem_univ j⟩
    rw [add_sum_erase _ _ hjmem]

  have hdecomp : e i + e j + ∑ k ∈ (univ.erase i).erase j, e k = d := by
    linarith [hi_sum, hj_sum]

  calc (∑ k, (if k = i then e i - 1 else if k = j then e j + 1 else e k))
      = (e i - 1) + (e j + 1) + ∑ k ∈ (univ.erase i).erase j, e k := hmod
    _ = e i + e j + ∑ k ∈ (univ.erase i).erase j, e k := by ring
    _ = d := hdecomp

/-- Modify a composition by transferring one unit from position i to position j. -/
def modify (e : WeakComposition n d) (i j : Fin n) (hi : 1 ≤ e i) (hij : i ≠ j) :
    WeakComposition n d where
  toFun := fun k => if k = i then e i - 1 else if k = j then e j + 1 else e k
  sum_eq := sum_modify_eq hij e.sum_eq
  nonneg := fun k => by
    split_ifs with hki hkj
    · omega
    · have := e.nonneg j; omega
    · exact e.nonneg k

@[simp]
lemma modify_at_i (e : WeakComposition n d) (i j : Fin n) (hi : 1 ≤ e i) (hij : i ≠ j) :
    (e.modify i j hi hij) i = e i - 1 := by simp only [modify, ite_true]

@[simp]
lemma modify_at_j (e : WeakComposition n d) (i j : Fin n) (hi : 1 ≤ e i) (hij : i ≠ j) :
    (e.modify i j hi hij) j = e j + 1 := by simp only [modify, hij.symm, ite_false, ite_true]

@[simp]
lemma modify_at_other (e : WeakComposition n d) (i j k : Fin n) (hi : 1 ≤ e i) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : (e.modify i j hi hij) k = e k := by
  simp only [modify, hki, hkj, ite_false]

end WeakComposition

variable {d : ℤ}

/-! ### Balanced and Concentrated Vectors -/

/-- A vector is balanced if all entries differ by at most 1. -/
def IsBalanced (e : Fin n → ℤ) : Prop :=
  ∀ i j, e i ≤ e j + 1 ∧ e j ≤ e i + 1

/-- A vector is concentrated if it equals `d • δₖ` for some `k`. -/
def IsConcentrated (d : ℤ) (e : Fin n → ℤ) : Prop :=
  ∃ k, ∀ i, e i = if i = k then d else 0

/-! ### Log-Concave and Palindromic Sequences -/

/-- A sequence `s : ℤ → ℚ` is log-concave on `[0, q]`. -/
def LogConcaveOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ q - 1 → s t ^ 2 ≥ s (t - 1) * s (t + 1)

/-- A sequence is palindromic on `[0, q]`. -/
def IsPalindromicOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ q → s t = s (q - t)

/-- A sequence is positive on `[0, q]`. -/
def IsPositiveOn (s : ℤ → ℚ) (q : ℤ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ q → 0 < s t

/-! ### Key Lemma: Log-concave palindromic sequences are unimodal -/

-- Helper: 1 ≤ x² and x > 0 implies 1 ≤ x
private lemma one_le_of_one_le_sq_pos {x : ℚ} (hx : 0 < x) (hsq : 1 ≤ x ^ 2) : 1 ≤ x := by
  by_contra h
  push_neg at h
  have hsq' : x ^ 2 < 1 := by nlinarith
  linarith

-- Helper: ratio antitone via Nat induction
private lemma ratio_antitone_aux (r : ℤ → ℚ) (q : ℤ)
    (hr_step : ∀ t, 0 ≤ t → t + 2 ≤ q → r (t + 1) ≤ r t) :
    ∀ a b, 0 ≤ a → b + 1 ≤ q → a ≤ b → r b ≤ r a := by
  intro a b ha0 hbq hab
  obtain ⟨d, hd⟩ : ∃ d : ℕ, b = a + d := ⟨(b - a).toNat, by omega⟩
  subst hd
  clear hab
  induction d with
  | zero => simp
  | succ n ih =>
    have hn1q : a + ↑n + 1 ≤ q := by omega
    have ih' := ih hn1q
    have hn0 : 0 ≤ a + n := by omega
    have hn2q : (a + ↑n) + 2 ≤ q := by omega
    have hstep := hr_step (a + n) hn0 hn2q
    calc r (a + (↑n + 1))
        = r (a + ↑n + 1) := by ring_nf
      _ ≤ r (a + ↑n) := hstep
      _ ≤ r a := ih'

/-- The main unimodality lemma. -/
theorem unimodal_of_logconcave_palindromic {s : ℤ → ℚ} {q : ℤ} (hq : 0 ≤ q)
    (hpos : IsPositiveOn s q) (hlc : LogConcaveOn s q) (hpal : IsPalindromicOn s q) :
    (∀ t, 0 ≤ t → 2 * t < q → s t ≤ s (t + 1)) ∧
    (∀ t, 2 * t > q → t ≤ q → s t ≤ s (t - 1)) := by
  classical
  -- Define ratio r(t) = s(t+1)/s(t)
  let r : ℤ → ℚ := fun t => s (t + 1) / s t

  have hs_pos : ∀ t, 0 ≤ t → t ≤ q → 0 < s t := hpos

  have hr_pos : ∀ t, 0 ≤ t → t + 1 ≤ q → 0 < r t := by
    intro t ht0 ht1q
    have hst : 0 < s t := hs_pos t ht0 (by omega)
    have hst1 : 0 < s (t + 1) := hs_pos (t + 1) (by omega) ht1q
    exact div_pos hst1 hst

  -- From log-concavity: r(t+1) ≤ r(t) on the valid range
  have hr_antitone_step : ∀ t, 0 ≤ t → t + 2 ≤ q → r (t + 1) ≤ r t := by
    intro t ht0 ht2q
    have ht1_lo : 1 ≤ t + 1 := by omega
    have ht1_hi : t + 1 ≤ q - 1 := by omega
    have hlc_at := hlc (t + 1) ht1_lo ht1_hi
    have hst : 0 < s t := hs_pos t ht0 (by omega)
    have hst1 : 0 < s (t + 1) := hs_pos (t + 1) (by omega) (by omega)
    simp only [r]
    rw [div_le_div_iff₀ hst1 hst]
    have h3 : s (t + 1 - 1) = s t := by ring_nf
    have h4 : s (t + 1 + 1) = s (t + 2) := by ring_nf
    have h5 : t + 1 + 1 = t + 2 := by ring
    calc s (t + 1 + 1) * s t
        = s (t + 2) * s t := by rw [h5]
      _ = s t * s (t + 2) := by ring
      _ ≤ s (t + 1) ^ 2 := by simp only [h3, h4] at hlc_at; exact hlc_at
      _ = s (t + 1) * s (t + 1) := by ring

  -- Use auxiliary lemma for antitone
  have hr_antitone : ∀ a b, 0 ≤ a → b + 1 ≤ q → a ≤ b → r b ≤ r a :=
    ratio_antitone_aux r q hr_antitone_step

  -- Palindromicity gives: r(q-1-t) = 1/r(t)
  have hr_pal : ∀ t, 0 ≤ t → t + 1 ≤ q → r (q - 1 - t) = (r t)⁻¹ := by
    intro t ht0 ht1q
    have hst : 0 < s t := hs_pos t ht0 (by omega)
    have hst1 : 0 < s (t + 1) := hs_pos (t + 1) (by omega) ht1q
    have hpal_t : s t = s (q - t) := hpal t ht0 (by omega)
    have hpal_t1 : s (t + 1) = s (q - (t + 1)) := hpal (t + 1) (by omega) ht1q
    have h1 : q - 1 - t + 1 = q - t := by ring
    have h2 : q - (t + 1) = q - 1 - t := by ring
    simp only [r]
    rw [h1, inv_div]
    rw [hpal_t.symm, ← h2, hpal_t1]

  -- Increasing part: when 2t < q, s(t) ≤ s(t+1)
  have hincr : ∀ t, 0 ≤ t → 2 * t < q → s t ≤ s (t + 1) := by
    intro t ht0 htmid
    have ht1q : t + 1 ≤ q := by omega
    have hrt_pos : 0 < r t := hr_pos t ht0 ht1q
    have ht_le : t ≤ q - 1 - t := by omega
    have hb1q : (q - 1 - t) + 1 ≤ q := by omega
    have hrat_cmp : r (q - 1 - t) ≤ r t := hr_antitone t (q - 1 - t) ht0 hb1q ht_le
    rw [hr_pal t ht0 ht1q] at hrat_cmp
    have hsq : 1 ≤ (r t) ^ 2 := by
      have hne : r t ≠ 0 := ne_of_gt hrt_pos
      have h : (r t)⁻¹ * r t ≤ r t * r t := by nlinarith
      simp only [inv_mul_cancel₀ hne] at h
      calc 1 ≤ r t * r t := h
        _ = (r t) ^ 2 := by ring
    have hrt_ge1 : 1 ≤ r t := one_le_of_one_le_sq_pos hrt_pos hsq
    have hst_pos : 0 < s t := hs_pos t ht0 (by omega)
    have hne : s t ≠ 0 := ne_of_gt hst_pos
    calc s t
        = s t * 1 := by ring
      _ ≤ s t * r t := by nlinarith
      _ = s t * (s (t + 1) / s t) := rfl
      _ = s (t + 1) := by field_simp

  -- Decreasing part: follows from increasing via palindromicity
  have hdecr : ∀ t, 2 * t > q → t ≤ q → s t ≤ s (t - 1) := by
    intro t htbig htq
    have htm1_lo : 0 ≤ t - 1 := by omega
    have htm1_hi : t - 1 ≤ q := by omega
    rw [hpal t (by omega) htq, hpal (t - 1) htm1_lo htm1_hi]
    set u := q - t with hu_def
    have hu_lo : 0 ≤ u := by omega
    have hu_mid : 2 * u < q := by omega
    have heq : q - (t - 1) = u + 1 := by omega
    rw [heq]
    exact hincr u hu_lo hu_mid

  exact ⟨hincr, hdecr⟩

/-! ### The Main Theorem Setup -/

/-- A function on weak compositions that is symmetric under the Sₙ action. -/
def IsSymmetric {d : ℤ} (D : WeakComposition n d → ℚ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (e : WeakComposition n d),
    D ⟨e ∘ σ.symm,
       by simp only [comp_apply]
          have : ∑ x, e.toFun (σ.symm x) = ∑ x, e.toFun x := Equiv.sum_comp σ.symm e.toFun
          rw [this]; exact e.sum_eq,
       fun i => by simp only [comp_apply]; exact e.nonneg _⟩ = D e

/-- The log-concavity condition for D. -/
def SatisfiesLogConcavity {d : ℤ} (D : WeakComposition n d → ℚ) : Prop :=
  ∀ (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (hi : 1 ≤ e i) (hj : 1 ≤ e j),
    D e ^ 2 ≥ D (e.modify i j hi hij) * D (e.modify j i hj hij.symm)

/-- D is strictly positive. -/
def IsStrictlyPositive {d : ℤ} (D : WeakComposition n d → ℚ) : Prop :=
  ∀ e, 0 < D e

/-! ### Imbalance measure for termination -/

/-- The "imbalance" of a vector: sum of squares. -/
def imbalance (e : Fin n → ℤ) : ℤ := ∑ i, (e i) ^ 2

/-- Key algebraic fact: (a-1)² + (b+1)² < a² + b² when a ≥ b + 2. -/
lemma sq_transfer_decreases {a b : ℤ} (h : a ≥ b + 2) :
    (a - 1)^2 + (b + 1)^2 < a^2 + b^2 := by
  have expand : (a - 1)^2 + (b + 1)^2 = a^2 + b^2 + 2*(b - a + 1) := by ring
  have neg : b - a + 1 ≤ -1 := by omega
  omega

/-- If e_i ≥ e_j + 2, then modifying from i to j decreases imbalance. -/
lemma imbalance_decreases {d : ℤ} (e : WeakComposition n d) (i j : Fin n)
    (hij : i ≠ j) (hi : 1 ≤ e i) (hdiff : e j + 2 ≤ e i) :
    imbalance (e.modify i j hi hij).toFun < imbalance e.toFun := by
  classical
  unfold imbalance
  set rest : ℤ := ∑ k ∈ (univ.erase i).erase j, (e k)^2 with hrest

  have hpow_mod : ∀ k, (e.modify i j hi hij).toFun k ^ 2 =
      (if k = i then (e i - 1)^2 else if k = j then (e j + 1)^2 else (e k)^2) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [WeakComposition.modify]
    · by_cases hkj : k = j
      · subst hkj; simp [WeakComposition.modify, hki]
      · simp [WeakComposition.modify, hki, hkj]

  have hsum_mod : (∑ k, (e.modify i j hi hij).toFun k ^ 2)
      = (e i - 1)^2 + (e j + 1)^2 + rest := by
    calc (∑ k, (e.modify i j hi hij).toFun k ^ 2)
        = ∑ k, (if k = i then (e i - 1)^2 else if k = j then (e j + 1)^2 else (e k)^2) := by
            refine sum_congr rfl ?_; intro k _; exact hpow_mod k
      _ = (e i - 1)^2 + (e j + 1)^2 + ∑ k ∈ (univ.erase i).erase j, (e k)^2 := by
            simpa using sum_ite_ite_eq_add_add_sum_erase_erase
              (fun k => (e k)^2) i j hij ((e i - 1)^2) ((e j + 1)^2)
      _ = (e i - 1)^2 + (e j + 1)^2 + rest := rfl

  have hsum_orig : (∑ k, (e k)^2) = (e i)^2 + (e j)^2 + rest := by
    have h := sum_ite_ite_eq_add_add_sum_erase_erase (fun k => (e k)^2) i j hij ((e i)^2) ((e j)^2)
    convert h using 1
    apply sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst hki; simp
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]

  have hsq : (e i - 1)^2 + (e j + 1)^2 < (e i)^2 + (e j)^2 :=
    sq_transfer_decreases hdiff

  calc ∑ k, (e.modify i j hi hij).toFun k ^ 2
      = (e i - 1)^2 + (e j + 1)^2 + rest := hsum_mod
    _ < (e i)^2 + (e j)^2 + rest := by linarith
    _ = ∑ k, (e k)^2 := hsum_orig.symm

/-- If a vector is not balanced, there exist i, j with e_i ≥ e_j + 2. -/
lemma exists_imbalanced_pair (e : Fin n → ℤ) (h : ¬ IsBalanced e) :
    ∃ i j, i ≠ j ∧ e j + 2 ≤ e i := by
  unfold IsBalanced at h
  simp only [not_forall, not_and_or, not_le] at h
  obtain ⟨i, j, hij⟩ := h
  rcases hij with h1 | h2
  · exact ⟨i, j, fun heq => by simp only [heq] at h1; omega, by omega⟩
  · exact ⟨j, i, fun heq => by simp only [heq] at h2; omega, by omega⟩

/-! ### Slice Analysis -/

/-- Auxiliary: sum is preserved when we put t at position i and (q-t) at position j. -/
lemma sum_slice_eq {e : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (hsum : ∑ k, e k = d)
    (t : ℤ) :
    ∑ k, (if k = i then t else if k = j then e i + e j - t else e k) = d := by
  classical
  have hslice : (∑ k, (if k = i then t else if k = j then e i + e j - t else e k))
      = t + (e i + e j - t) + ∑ k ∈ (univ.erase i).erase j, e k := by
    simpa using sum_ite_ite_eq_add_add_sum_erase_erase e i j hij t (e i + e j - t)

  have hi_sum : e i + ∑ k ∈ univ.erase i, e k = d := by
    rw [add_sum_erase _ _ (mem_univ i), hsum]

  have hj_sum : e j + ∑ k ∈ (univ.erase i).erase j, e k = ∑ k ∈ univ.erase i, e k := by
    have hjmem : j ∈ (univ.erase i : Finset (Fin n)) :=
      mem_erase.mpr ⟨hij.symm, mem_univ j⟩
    rw [add_sum_erase _ _ hjmem]

  have hdecomp : e i + e j + ∑ k ∈ (univ.erase i).erase j, e k = d := by
    linarith [hi_sum, hj_sum]

  calc (∑ k, (if k = i then t else if k = j then e i + e j - t else e k))
      = t + (e i + e j - t) + ∑ k ∈ (univ.erase i).erase j, e k := hslice
    _ = e i + e j + ∑ k ∈ (univ.erase i).erase j, e k := by ring
    _ = d := hdecomp

/-- Given a weak composition e and distinct positions i, j, construct the composition
    with value t at position i and (e_i + e_j - t) at position j. -/
def sliceComposition {d : ℤ} (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (t : ℤ) (ht : 0 ≤ t) (htq : t ≤ e i + e j) : WeakComposition n d where
  toFun := fun k => if k = i then t else if k = j then e i + e j - t else e k
  sum_eq := sum_slice_eq hij e.sum_eq t
  nonneg := fun k => by
    split_ifs with hki hkj
    · exact ht
    · omega
    · exact e.nonneg k

/-- The slice sequence for D. -/
noncomputable def sliceSeq {d : ℤ} (D : WeakComposition n d → ℚ) (e : WeakComposition n d)
    (i j : Fin n) (hij : i ≠ j) : ℤ → ℚ := fun t =>
  if h : 0 ≤ t ∧ t ≤ e i + e j then
    D (sliceComposition e i j hij t h.1 h.2)
  else 0

/-- The slice sequence is palindromic when D is symmetric. -/
lemma sliceSeq_palindromic {d : ℤ} (D : WeakComposition n d → ℚ)
    (hsym : IsSymmetric D) (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) :
    IsPalindromicOn (sliceSeq D e i j hij) (e i + e j) := by
  intro t ht htq
  set q := e i + e j with hq
  -- Both t and q-t are in range
  have ht' : 0 ≤ q - t := by omega
  have htq' : q - t ≤ q := by omega
  -- Unfold sliceSeq on both sides
  unfold sliceSeq
  rw [dif_pos ⟨ht, htq⟩, dif_pos ⟨ht', htq'⟩]
  -- The slice at t has i↦t, j↦q-t
  -- The slice at q-t has i↦q-t, j↦t (since q-(q-t) = t)
  -- Use the swap permutation σ = Equiv.swap i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  -- Apply symmetry with swap permutation
  have hsym_app := hsym σ (sliceComposition e i j hij (q - t) ht' htq')
  -- Show the swapped composition equals sliceComposition at t
  suffices h : (⟨(sliceComposition e i j hij (q - t) ht' htq') ∘ σ.symm,
      by simp only [comp_apply]
         have hsum : ∑ x, (sliceComposition e i j hij (q - t) ht' htq').toFun (σ.symm x) =
             ∑ x, (sliceComposition e i j hij (q - t) ht' htq').toFun x :=
           Equiv.sum_comp σ.symm _
         rw [hsum]; exact (sliceComposition e i j hij (q - t) ht' htq').sum_eq,
      fun k => by simp only [comp_apply]; exact (sliceComposition e i j hij (q - t) ht' htq').nonneg _⟩ :
      WeakComposition n d) = sliceComposition e i j hij t ht htq by
    rw [← h, hsym_app]
  -- Prove the compositions are equal pointwise
  refine WeakComposition.ext (fun k => ?_)
  simp only [sliceComposition, comp_apply]
  by_cases hki : k = i
  · -- k = i: σ.symm k = j, so we get the j-value from the (q-t) slice
    have hswap_k : σ.symm k = j := by rw [hki, hσ, Equiv.symm_swap, Equiv.swap_apply_left]
    rw [hswap_k]
    simp only [hki, hij.symm, ite_false, ite_true]
    ring
  · by_cases hkj : k = j
    · -- k = j: σ.symm k = i, so we get the i-value from the (q-t) slice
      have hswap_k : σ.symm k = i := by rw [hkj, hσ, Equiv.symm_swap, Equiv.swap_apply_right]
      rw [hswap_k]
      simp only [hkj, ite_true, if_neg hij.symm]; ring
    · -- k ≠ i and k ≠ j: σ.symm k = k
      have hswap_other : σ.symm k = k := by
        rw [hσ, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj]
      rw [hswap_other]
      simp only [hki, hkj, ite_false]

/-- The slice sequence is log-concave when D satisfies log-concavity. -/
lemma sliceSeq_logconcave {d : ℤ} (D : WeakComposition n d → ℚ)
    (hlc : SatisfiesLogConcavity D) (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) :
    LogConcaveOn (sliceSeq D e i j hij) (e i + e j) := by
  intro t ht htq
  set q := e i + e j with hq
  -- Bounds for t-1 and t+1
  have htm1_lo : 0 ≤ t - 1 := by omega
  have htm1_hi : t - 1 ≤ q := by omega
  have htp1_lo : 0 ≤ t + 1 := by omega
  have htp1_hi : t + 1 ≤ q := by omega
  have ht_lo : 0 ≤ t := by omega
  have ht_hi : t ≤ q := by omega
  -- The central slice e0 at position t
  set e0 := sliceComposition e i j hij t ht_lo ht_hi with he0
  -- e0 has i-value = t and j-value = q - t
  have he0_i : e0 i = t := by simp only [he0, sliceComposition, ite_true]
  have he0_j : e0 j = q - t := by
    simp only [he0, sliceComposition, hij.symm, ite_false, ite_true]
    rw [hq]
  -- Since 1 ≤ t and t ≤ q-1, we have:
  have hi_ge1 : 1 ≤ e0 i := by rw [he0_i]; omega
  have hj_ge1 : 1 ≤ e0 j := by rw [he0_j]; omega
  -- Apply log-concavity to e0
  have hlc_app := hlc e0 i j hij hi_ge1 hj_ge1
  -- e0.modify i j gives i ↦ t-1, j ↦ (q-t)+1 = q-(t-1)
  -- e0.modify j i gives i ↦ t+1, j ↦ (q-t)-1 = q-(t+1)
  -- Show these equal the neighboring slice compositions
  have hmod_ij : e0.modify i j hi_ge1 hij = sliceComposition e i j hij (t - 1) htm1_lo htm1_hi := by
    refine WeakComposition.ext (fun m => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hmi : m = i
    · -- m = i: LHS is e0 i - 1 = t - 1, RHS is t - 1
      simp only [hmi, ite_true, he0_i]
    · by_cases hmj : m = j
      · -- m = j: LHS is e0 j + 1 = (q-t) + 1, RHS is q - (t-1)
        simp only [hmj, ite_true, if_neg hij.symm, he0_j]; ring
      · -- m ≠ i and m ≠ j: e0 m = e m
        simp only [hmi, hmj, ite_false, he0, sliceComposition]
  have hmod_ji : e0.modify j i hj_ge1 hij.symm = sliceComposition e i j hij (t + 1) htp1_lo htp1_hi := by
    refine WeakComposition.ext (fun m => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hmi : m = i
    · -- m = i: LHS is e0 i + 1 = t + 1, RHS is t + 1
      simp only [hmi, ite_true, if_neg hij, he0_i]
    · by_cases hmj : m = j
      · -- m = j: LHS is e0 j - 1 = (q-t) - 1, RHS is q - (t+1)
        simp only [hmj, ite_true, if_neg hij.symm, he0_j]; ring
      · -- m ≠ i and m ≠ j: e0 m = e m
        simp only [hmi, hmj, ite_false, he0, sliceComposition]
  -- Rewrite the log-concavity inequality
  rw [hmod_ij, hmod_ji] at hlc_app
  -- Unfold sliceSeq at each point
  unfold sliceSeq
  rw [dif_pos ⟨ht_lo, ht_hi⟩, dif_pos ⟨htm1_lo, htm1_hi⟩, dif_pos ⟨htp1_lo, htp1_hi⟩]
  -- Now hlc_app says D(e0)^2 ≥ D(slice at t-1) * D(slice at t+1)
  exact hlc_app

/-- The slice sequence is positive when D is positive. -/
lemma sliceSeq_positive {d : ℤ} (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) :
    IsPositiveOn (sliceSeq D e i j hij) (e i + e j) := by
  intro t ht htq
  simp only [sliceSeq, ht, htq, and_self, ↓reduceDIte]
  exact hpos _

/-! ### Main Theorems -/

/-- The balancing step weakly increases D when entries differ by ≥ 2. -/
lemma balancing_increases_D {d : ℤ} (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D)
    (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) (hi : 1 ≤ e i) (hdiff : e j + 2 ≤ e i) :
    D e ≤ D (e.modify i j hi hij) := by
  -- Use the slice analysis: consider the slice sequence on indices i, j
  -- The slice sequence s(t) = D(composition with i↦t, j↦q-t) where q = e.i + e.j
  -- Current e is slice at t = e.i
  -- Modified e is slice at t = e.i - 1
  -- Since e.i - e.j ≥ 2, we have 2·(e.i) > q, so e.i is past the midpoint
  -- By unimodality (decreasing part): s(e.i) ≤ s(e.i - 1)
  set q := e i + e j with hq_def
  -- The slice sequence is unimodal
  have hpal := sliceSeq_palindromic D hsym e i j hij
  have hlc' := sliceSeq_logconcave D hlc e i j hij
  have hpos' := sliceSeq_positive D hpos e i j hij
  have hq_nonneg : 0 ≤ q := by
    have := e.nonneg i
    have := e.nonneg j
    omega
  -- Get unimodality
  have hunimodal := unimodal_of_logconcave_palindromic hq_nonneg hpos' hlc' hpal
  -- Bounds
  have hei_lo : 0 ≤ e i := e.nonneg i
  have hei_hi : e i ≤ q := by simp only [hq_def]; linarith [e.nonneg j]
  have hem1_lo : 0 ≤ e i - 1 := by omega
  have hem1_hi : e i - 1 ≤ q := by simp only [hq_def]; omega
  -- e is the slice at position e.i
  have he_eq_slice : e = sliceComposition e i j hij (e i) hei_lo hei_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [sliceComposition]
    by_cases hki : k = i
    · simp only [hki, ite_true]
    · by_cases hkj : k = j
      · simp only [hkj, ite_true, if_neg hij.symm]; ring
      · simp only [hki, hkj, ite_false]
  -- The modified composition is the slice at position e.i - 1
  have hmod_eq_slice : e.modify i j hi hij = sliceComposition e i j hij (e i - 1) hem1_lo hem1_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hki : k = i
    · simp only [hki, ite_true]
    · by_cases hkj : k = j
      · simp only [hkj, ite_true, if_neg hij.symm]; ring
      · simp only [hki, hkj, ite_false]
  -- Use the decreasing part of unimodality
  -- Condition: 2 * (e i) > q and e i ≤ q
  have h2ei_gt_q : 2 * (e i) > q := by simp only [hq_def]; omega
  -- Get the decreasing inequality from unimodality
  have hdecr := hunimodal.2 (e i) h2ei_gt_q hei_hi
  -- hdecr says sliceSeq at (e i) ≤ sliceSeq at (e i - 1)
  -- Compute sliceSeq values using the definition
  have hslice_ei : sliceSeq D e i j hij (e i) = D (sliceComposition e i j hij (e i) hei_lo hei_hi) := by
    unfold sliceSeq
    rw [dif_pos ⟨hei_lo, hei_hi⟩]
  have hslice_em1 : sliceSeq D e i j hij (e i - 1) =
      D (sliceComposition e i j hij (e i - 1) hem1_lo hem1_hi) := by
    unfold sliceSeq
    rw [dif_pos ⟨hem1_lo, hem1_hi⟩]
  rw [hslice_ei, hslice_em1, ← he_eq_slice, ← hmod_eq_slice] at hdecr
  exact hdecr

/-- Imbalance is non-negative for weak compositions. -/
lemma imbalance_nonneg {d : ℤ} (e : WeakComposition n d) : 0 ≤ imbalance e.toFun := by
  unfold imbalance
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

/-- Any vector can be transformed to a balanced vector while increasing D. -/
theorem balanced_maximizes {d : ℤ} (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D) :
    ∀ e : WeakComposition n d, ∃ e' : WeakComposition n d, IsBalanced e'.toFun ∧ D e ≤ D e' := by
  -- Use well-founded induction on imbalance
  intro e
  -- Convert imbalance to ℕ for well-founded recursion
  have h_nonneg : 0 ≤ imbalance e.toFun := imbalance_nonneg e
  generalize hm : (imbalance e.toFun).toNat = m
  induction m using Nat.strong_induction_on generalizing e with
  | _ m ih =>
    by_cases hbal : IsBalanced e.toFun
    · -- e is balanced: take e' = e
      exact ⟨e, hbal, le_refl _⟩
    · -- e is not balanced: find imbalanced pair and modify
      obtain ⟨i, j, hij, hdiff⟩ := exists_imbalanced_pair e.toFun hbal
      have hi : 1 ≤ e i := by linarith [e.nonneg j]
      -- The modified composition
      set e1 := e.modify i j hi hij with he1
      -- D increases
      have hD_incr : D e ≤ D e1 := balancing_increases_D D hpos hsym hlc e i j hij hi hdiff
      -- Imbalance decreases
      have himb_decr : imbalance e1.toFun < imbalance e.toFun :=
        imbalance_decreases e i j hij hi hdiff
      -- Apply induction hypothesis
      have h1_nonneg : 0 ≤ imbalance e1.toFun := imbalance_nonneg e1
      -- Need to show imbalance e > 0 (since e is not balanced)
      have h_pos : 0 < imbalance e.toFun := by
        have hej_nonneg : 0 ≤ e j := e.nonneg j
        have hei : 2 ≤ e i := by omega
        have hsq : 4 ≤ (e i)^2 := by nlinarith
        calc imbalance e.toFun
            = ∑ k, (e k)^2 := rfl
          _ ≥ (e i)^2 := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
          _ ≥ 4 := hsq
          _ > 0 := by omega
      have hm1 : (imbalance e1.toFun).toNat < m := by
        rw [← hm]
        rw [Int.toNat_lt_toNat h_pos]
        exact himb_decr
      obtain ⟨e', hbal', hD'⟩ := ih (imbalance e1.toFun).toNat hm1 e1 h1_nonneg rfl
      exact ⟨e', hbal', le_trans hD_incr hD'⟩

/-- When e_i > e_j, moving mass from j to i (concentrating) decreases D. -/
lemma concentrating_decreases_D {d : ℤ} (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D)
    (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j) (hj : 1 ≤ e j) (hdiff : e j < e i) :
    D (e.modify j i hj hij.symm) ≤ D e := by
  -- Use the slice analysis
  -- The slice sequence on j, i at position t = e.j
  -- Since e.j < e.i, we have 2*e.j < e.j + e.i = q, so we're in the increasing part
  -- Moving to t - 1 (decreasing e.j) moves toward the boundary, decreasing D
  set q := e j + e i with hq_def
  have hpal := sliceSeq_palindromic D hsym e j i hij.symm
  have hlc' := sliceSeq_logconcave D hlc e j i hij.symm
  have hpos' := sliceSeq_positive D hpos e j i hij.symm
  have hq_nonneg : 0 ≤ q := by linarith [e.nonneg i, e.nonneg j]
  have hunimodal := unimodal_of_logconcave_palindromic hq_nonneg hpos' hlc' hpal
  -- Bounds
  have hej_lo : 0 ≤ e j := e.nonneg j
  have hej_hi : e j ≤ q := by simp only [hq_def]; linarith [e.nonneg i]
  have hejm1_lo : 0 ≤ e j - 1 := by omega
  have hejm1_hi : e j - 1 ≤ q := by simp only [hq_def]; omega
  -- e is the slice at position e.j
  have he_eq_slice : e = sliceComposition e j i hij.symm (e j) hej_lo hej_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  -- The modified composition is the slice at position e.j - 1
  have hmod_eq_slice : e.modify j i hj hij.symm =
      sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  -- Since e.j < e.i, we have 2*e.j < q, so we're in the increasing part
  have h2ej_lt_q : 2 * (e j - 1) < q := by simp only [hq_def]; omega
  -- By unimodality (increasing part): s(e.j - 1) ≤ s(e.j)
  have hincr := hunimodal.1 (e j - 1) hejm1_lo h2ej_lt_q
  -- hincr says sliceSeq at (e.j - 1) ≤ sliceSeq at e.j
  have hslice_ej : sliceSeq D e j i hij.symm (e j) =
      D (sliceComposition e j i hij.symm (e j) hej_lo hej_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hej_lo, hej_hi⟩]
  have hslice_ejm1 : sliceSeq D e j i hij.symm (e j - 1) =
      D (sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hejm1_lo, hejm1_hi⟩]
  simp only [Int.sub_add_cancel] at hincr
  rw [hslice_ejm1, hslice_ej, ← hmod_eq_slice, ← he_eq_slice] at hincr
  exact hincr

/-! ### MaxEntry for termination of concentrated_minimizes -/

/-- The maximum entry of a vector. -/
noncomputable def maxEntry (e : Fin n → ℤ) (hn : 0 < n) : ℤ :=
  ((Finset.univ : Finset (Fin n)).image e).max'
    (by
      refine ⟨e ⟨0, hn⟩, ?_⟩
      exact Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩)

lemma exists_eq_maxEntry (e : Fin n → ℤ) (hn : 0 < n) :
    ∃ i : Fin n, e i = maxEntry e hn := by
  unfold maxEntry
  set s : Finset ℤ := (Finset.univ : Finset (Fin n)).image e
  have hs : s.Nonempty := ⟨e ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hmem : s.max' hs ∈ s := Finset.max'_mem s hs
  obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
  exact ⟨i, hi⟩

lemma le_maxEntry (e : Fin n → ℤ) (hn : 0 < n) (i : Fin n) :
    e i ≤ maxEntry e hn := by
  unfold maxEntry
  set s : Finset ℤ := (Finset.univ : Finset (Fin n)).image e
  have hs : s.Nonempty := ⟨e ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hi : e i ∈ s := Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  exact Finset.le_max' s (e i) hi

namespace WeakComposition

lemma maxEntry_le_d (e : WeakComposition n d) (hn : 0 < n) :
    maxEntry e.toFun hn ≤ d := by
  obtain ⟨i, hi⟩ := exists_eq_maxEntry e.toFun hn
  have hle : e i ≤ ∑ k, e k :=
    Finset.single_le_sum (fun k _ => e.nonneg k) (Finset.mem_univ i)
  rw [e.sum_eq] at hle
  linarith

/-- If some entry equals `d`, then the composition is concentrated at that index. -/
lemma concentrated_of_entry_eq_d (e : WeakComposition n d) (i : Fin n) (hi : e i = d) :
    IsConcentrated d e.toFun := by
  refine ⟨i, ?_⟩
  intro j
  by_cases hji : j = i
  · simp only [hji, ite_true, hi]
  · simp only [hji, ite_false]
    have hsplit : (∑ k, e k) = e i + ∑ k ∈ (Finset.univ.erase i), e k := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : (∑ k ∈ (Finset.univ.erase i), e k) = 0 := by
      have := e.sum_eq
      linarith
    have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin n)) := by simp [hji]
    have hle : e j ≤ ∑ k ∈ (Finset.univ.erase i), e k :=
      Finset.single_le_sum (fun k _ => e.nonneg k) hjmem
    have hge : 0 ≤ e j := e.nonneg j
    omega

lemma concentrated_of_maxEntry_eq_d (e : WeakComposition n d) (hn : 0 < n)
    (hmax : maxEntry e.toFun hn = d) : IsConcentrated d e.toFun := by
  obtain ⟨i, hi⟩ := exists_eq_maxEntry e.toFun hn
  have hid : e i = d := by linarith
  exact concentrated_of_entry_eq_d e i hid

/-- Moving mass to a maximizer increases maxEntry by 1. -/
lemma maxEntry_modify_to_maximizer
    (e : WeakComposition n d) (hn : 0 < n)
    (i j : Fin n) (hij : i ≠ j)
    (hj : 1 ≤ e j)
    (hiMax : e i = maxEntry e.toFun hn) :
    maxEntry (e.modify j i hj hij.symm).toFun hn = maxEntry e.toFun hn + 1 := by
  set e1 := e.modify j i hj hij.symm with he1

  have h_i_val : e1 i = e i + 1 := modify_at_j e j i hj hij.symm
  have h_j_val : e1 j = e j - 1 := modify_at_i e j i hj hij.symm

  have hlow : maxEntry e.toFun hn + 1 ≤ maxEntry e1.toFun hn := by
    have hle : e1 i ≤ maxEntry e1.toFun hn := le_maxEntry e1.toFun hn i
    linarith

  obtain ⟨k, hk⟩ := exists_eq_maxEntry e1.toFun hn
  have hk_bound : e1 k ≤ maxEntry e.toFun hn + 1 := by
    by_cases hki : k = i
    · rw [hki, h_i_val, hiMax]
    · by_cases hkj : k = j
      · have hj_le : e j ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn j
        rw [hkj, h_j_val]
        omega
      · have h_other : e1 k = e k := modify_at_other e j i k hj hij.symm hkj hki
        have hk_le : e k ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn k
        linarith

  have hup : maxEntry e1.toFun hn ≤ maxEntry e.toFun hn + 1 := by linarith
  omega

lemma measure_decreases_of_maxEntry_increases
    (e e1 : WeakComposition n d) (hn : 0 < n)
    (hmax : maxEntry e1.toFun hn = maxEntry e.toFun hn + 1)
    (hmax_lt : maxEntry e.toFun hn < d) :
    (d - maxEntry e1.toFun hn).toNat < (d - maxEntry e.toFun hn).toNat := by
  have hpos : 0 < d - maxEntry e.toFun hn := by omega
  have hlt : d - maxEntry e1.toFun hn < d - maxEntry e.toFun hn := by omega
  have hpos' : 0 ≤ d - maxEntry e1.toFun hn := by omega
  omega

end WeakComposition

/-- Count of non-zero entries. -/
def nonzeroCount (e : Fin n → ℤ) : ℕ := (Finset.univ.filter (fun i => e i ≠ 0)).card

/-- If e is not concentrated and d > 0, there exist distinct i, j with e.i > 0 and e.j > 0. -/
lemma exists_two_positive {d : ℤ} (hd : 0 < d) (e : WeakComposition n d)
    (h : ¬ IsConcentrated d e.toFun) : ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j := by
  -- If concentrated, all mass is on one index
  -- Not concentrated means at least two indices have positive values
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : ∀ i j, i ≠ j → 0 < e i → e j ≤ 0
  -- This means at most one index has positive value
  -- We show e is concentrated, contradicting h
  have hone : ∃ k₀, ∀ i, i ≠ k₀ → e i = 0 := by
    by_cases hall : ∀ i, e i = 0
    · -- All zero contradicts d > 0
      have hsum_eq : d = ∑ i, e i := e.sum_eq.symm
      simp only [hall, Finset.sum_const_zero] at hsum_eq
      omega
    · push_neg at hall
      obtain ⟨k₀, hk₀⟩ := hall
      use k₀
      intro i hik
      by_contra hi
      have hpos_k₀ : 0 < e k₀ := by have := e.nonneg k₀; omega
      have hpos_i : 0 < e i := by have := e.nonneg i; omega
      have hcontr_app := hcontra i k₀ hik hpos_i
      omega
  obtain ⟨k₀, hk₀⟩ := hone
  apply h
  use k₀
  intro i
  by_cases hik : i = k₀
  · -- i = k₀: show e i = d
    simp only [hik, ite_true]
    have hsum : d = ∑ m, e m := e.sum_eq.symm
    have hsplit : ∑ m, e m = e k₀ + ∑ m ∈ Finset.univ.erase k₀, e m := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
    rw [hsplit] at hsum
    have hrest : ∑ m ∈ Finset.univ.erase k₀, e m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      exact hk₀ m (Finset.ne_of_mem_erase hm)
    omega
  · simp only [hik, ite_false]
    exact hk₀ i hik

/-- Helper: D decreases when moving toward the max, even in the equal case.
    This uses the increasing part of unimodality. -/
private lemma concentrating_to_max_decreases_D {d : ℤ} (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D)
    (e : WeakComposition n d) (i j : Fin n) (hij : i ≠ j)
    (hj : 1 ≤ e j) (hdiff : e j ≤ e i) :
    D (e.modify j i hj hij.symm) ≤ D e := by
  -- Use slice analysis on indices j, i
  -- e.j ≤ e.i means we're at or before the midpoint of the slice (increasing region)
  -- Moving from j to i (decreasing the j-coordinate) moves toward 0
  set q := e j + e i with hq_def
  have hpal := sliceSeq_palindromic D hsym e j i hij.symm
  have hlc' := sliceSeq_logconcave D hlc e j i hij.symm
  have hpos' := sliceSeq_positive D hpos e j i hij.symm
  have hq_nonneg : 0 ≤ q := by linarith [e.nonneg i, e.nonneg j]
  have hunimodal := unimodal_of_logconcave_palindromic hq_nonneg hpos' hlc' hpal
  -- Bounds
  have hej_lo : 0 ≤ e j := e.nonneg j
  have hej_hi : e j ≤ q := by simp only [hq_def]; linarith [e.nonneg i]
  have hejm1_lo : 0 ≤ e j - 1 := by omega
  have hejm1_hi : e j - 1 ≤ q := by simp only [hq_def]; omega
  -- e is the slice at position e.j
  have he_eq_slice : e = sliceComposition e j i hij.symm (e j) hej_lo hej_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  -- Modified composition is the slice at position e.j - 1
  have hmod_eq_slice : e.modify j i hj hij.symm =
      sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi := by
    refine WeakComposition.ext (fun k => ?_)
    simp only [WeakComposition.modify, sliceComposition]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]
    · by_cases hki : k = i
      · simp only [hki, ite_true, if_neg hij]; ring
      · simp only [hkj, hki, ite_false]
  -- The key: 2*(e.j - 1) < q when e.j ≤ e.i
  -- 2*(e.j - 1) = 2*e.j - 2 < e.j + e.i = q iff e.j - 2 < e.i iff e.j < e.i + 2
  -- This is always true when e.j ≤ e.i.
  have h2ej_lt_q : 2 * (e j - 1) < q := by simp only [hq_def]; omega
  -- By unimodality (increasing part): s(e.j - 1) ≤ s(e.j)
  have hincr := hunimodal.1 (e j - 1) hejm1_lo h2ej_lt_q
  have hslice_ej : sliceSeq D e j i hij.symm (e j) =
      D (sliceComposition e j i hij.symm (e j) hej_lo hej_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hej_lo, hej_hi⟩]
  have hslice_ejm1 : sliceSeq D e j i hij.symm (e j - 1) =
      D (sliceComposition e j i hij.symm (e j - 1) hejm1_lo hejm1_hi) := by
    unfold sliceSeq; rw [dif_pos ⟨hejm1_lo, hejm1_hi⟩]
  simp only [Int.sub_add_cancel] at hincr
  rw [hslice_ejm1, hslice_ej, ← hmod_eq_slice, ← he_eq_slice] at hincr
  exact hincr

/-- Any vector can be transformed to a concentrated vector while decreasing D. -/
theorem concentrated_minimizes {d : ℤ} (hn : 0 < n) (hd : 0 ≤ d) (D : WeakComposition n d → ℚ)
    (hpos : IsStrictlyPositive D) (hsym : IsSymmetric D) (hlc : SatisfiesLogConcavity D) :
    ∀ e : WeakComposition n d, ∃ e' : WeakComposition n d,
      IsConcentrated d e'.toFun ∧ D e' ≤ D e := by
  intro e
  -- Handle d = 0 case: only composition is all zeros
  by_cases hd0 : d = 0
  · use e
    constructor
    · use ⟨0, hn⟩
      intro i
      have hsum : 0 = ∑ j, e j := by rw [← hd0]; exact e.sum_eq.symm
      have hall_zero : ∀ j, e j = 0 := by
        intro j
        have hnonneg := e.nonneg j
        have hle : e j ≤ ∑ k, e k := Finset.single_le_sum (fun k _ => e.nonneg k) (Finset.mem_univ j)
        omega
      rw [hall_zero i, hd0]
      simp only [ite_self]
    · exact le_refl _
  have hd_pos : 0 < d := by omega
  -- Use well-founded induction on (d - maxEntry).toNat
  generalize hm : (d - maxEntry e.toFun hn).toNat = m
  induction m using Nat.strong_induction_on generalizing e with
  | _ m ih =>
    -- Check if already concentrated
    by_cases hmax_eq : maxEntry e.toFun hn = d
    · exact ⟨e, WeakComposition.concentrated_of_maxEntry_eq_d e hn hmax_eq, le_refl _⟩
    -- Not concentrated: maxEntry < d
    have hmax_lt : maxEntry e.toFun hn < d := by
      have hle := WeakComposition.maxEntry_le_d e hn
      omega
    -- Pick i = maximizer, j = any other positive index
    obtain ⟨i, hi_max⟩ := exists_eq_maxEntry e.toFun hn
    -- Since not concentrated, there exists another positive entry
    have hconc : ¬ IsConcentrated d e.toFun := by
      intro hc
      obtain ⟨k, hk⟩ := hc
      have hi_eq_d : e i = d := by
        have hei := hk i
        by_cases hik : i = k
        · -- i = k, so e i = e k = d
          rw [hik]
          have hek := hk k
          simp only [ite_true] at hek
          exact hek
        · -- i ≠ k, so e i = 0
          simp only [hik, ite_false] at hei
          -- But i achieves max, so max = e i = 0
          -- And e k = d > 0 ≤ max. Contradiction.
          have hek := hk k
          simp only [ite_true] at hek
          have hk_le : e k ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn k
          linarith
      linarith
    obtain ⟨i', j', hij', hi'_pos, hj'_pos⟩ := exists_two_positive hd_pos e hconc
    -- We need a positive index j ≠ i. Use whichever of i', j' is not i.
    have hj_exists : ∃ j, j ≠ i ∧ 0 < e j := by
      by_cases hi'i : i' = i
      · exact ⟨j', fun h => hij' (hi'i.trans h.symm), hj'_pos⟩
      · exact ⟨i', hi'i, hi'_pos⟩
    obtain ⟨j, hji, hj_pos⟩ := hj_exists
    have hij : i ≠ j := hji.symm
    have hj_ge1 : 1 ≤ e j := by omega
    have hj_le_i : e j ≤ e i := by
      have hi_le : e i ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn i
      have hj_le : e j ≤ maxEntry e.toFun hn := le_maxEntry e.toFun hn j
      linarith
    -- Modify j → i
    set e1 := e.modify j i hj_ge1 hji with he1
    -- D decreases (using the new helper lemma that handles both strict and equal cases)
    have hD_decr : D e1 ≤ D e := concentrating_to_max_decreases_D D hpos hsym hlc e i j hij hj_ge1 hj_le_i
    -- maxEntry increases by 1, so measure decreases
    have hmax_incr : maxEntry e1.toFun hn = maxEntry e.toFun hn + 1 :=
      WeakComposition.maxEntry_modify_to_maximizer e hn i j hij hj_ge1 hi_max
    have hm1 : (d - maxEntry e1.toFun hn).toNat < m := by
      rw [← hm]
      exact WeakComposition.measure_decreases_of_maxEntry_increases e e1 hn hmax_incr hmax_lt
    obtain ⟨e', hconc', hD'⟩ := ih (d - maxEntry e1.toFun hn).toNat hm1 e1 rfl
    exact ⟨e', hconc', le_trans hD' hD_decr⟩

/-! ==========================================================================
## Main Results (Clean Formulation)

This section provides the main theorems in their cleanest form, suitable for
citation and verification against informal statements.

**Informal Theorem.** Let D : E(n,d) → ℚ₊ be a function on weak compositions
satisfying Sₙ-symmetry, the log-concavity condition D(e)² ≥ D(e-δᵢ+δⱼ)·D(e+δᵢ-δⱼ),
and strict positivity. Then D is maximized on balanced vectors and minimized on
concentrated vectors.
========================================================================== -/

/-- A function `D` on weak compositions satisfying the three conditions:
    Sₙ-symmetry, log-concavity, and strict positivity. -/
structure SymmetricLogConcaveFunction (n : ℕ) (d : ℤ) where
  /-- The function D : E(n,d) → ℚ -/
  D : WeakComposition n d → ℚ
  /-- D(e ∘ σ⁻¹) = D(e) for all permutations σ -/
  symmetric : IsSymmetric D
  /-- D(e)² ≥ D(e - δᵢ + δⱼ) · D(e + δᵢ - δⱼ) when eᵢ, eⱼ ≥ 1 -/
  logConcave : SatisfiesLogConcavity D
  /-- D(e) > 0 for all e -/
  strictlyPositive : IsStrictlyPositive D

namespace SymmetricLogConcaveFunction

variable {n : ℕ} {d : ℤ}

/--
**Main Theorem (Maximum).**
Every symmetric log-concave function on weak compositions is maximized on balanced vectors.

More precisely: for any `e ∈ E(n,d)`, there exists a balanced `e' ∈ E(n,d)` with `D(e) ≤ D(e')`.

A vector is *balanced* if all entries differ by at most 1: `∀ i j, |eᵢ - eⱼ| ≤ 1`.
-/
theorem maximized_on_balanced (F : SymmetricLogConcaveFunction n d) (e : WeakComposition n d) :
    ∃ e' : WeakComposition n d, IsBalanced e'.toFun ∧ F.D e ≤ F.D e' :=
  balanced_maximizes F.D F.strictlyPositive F.symmetric F.logConcave e

/--
**Main Theorem (Minimum).**
Every symmetric log-concave function on weak compositions is minimized on concentrated vectors.

More precisely: for any `e ∈ E(n,d)`, there exists a concentrated `e' ∈ E(n,d)` with `D(e') ≤ D(e)`.

A vector is *concentrated* if it equals `d · δₖ` for some index `k`.

Requires `n > 0` and `d ≥ 0`.
-/
theorem minimized_on_concentrated (hn : 0 < n) (hd : 0 ≤ d)
    (F : SymmetricLogConcaveFunction n d) (e : WeakComposition n d) :
    ∃ e' : WeakComposition n d, IsConcentrated d e'.toFun ∧ F.D e' ≤ F.D e :=
  concentrated_minimizes hn hd F.D F.strictlyPositive F.symmetric F.logConcave e

end SymmetricLogConcaveFunction

/--
**Combined Main Theorem.**
For any symmetric log-concave function D on weak compositions E(n,d):
- The maximum of D is achieved on balanced vectors
- The minimum of D is achieved on concentrated vectors
-/
theorem main_theorem (hn : 0 < n) (hd : 0 ≤ d) (F : SymmetricLogConcaveFunction n d) :
    (∀ e, ∃ e_bal, IsBalanced e_bal.toFun ∧ F.D e ≤ F.D e_bal) ∧
    (∀ e, ∃ e_conc, IsConcentrated d e_conc.toFun ∧ F.D e_conc ≤ F.D e) :=
  ⟨F.maximized_on_balanced, F.minimized_on_concentrated hn hd⟩
