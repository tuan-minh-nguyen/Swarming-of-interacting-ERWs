/-
# The running-maximum / reflection transport for the ACTUAL auxiliary walk
`Swarming.Trajectory.symmetricWalk`

This module is the **transport layer** of the fair-walk law.  It contains

* the exact increment `symmInc` and the telescoping identity
  `symmetricWalk p m U i n = ∑ k ∈ range n, symmInc p m U i k` for the actual
  auxiliary process (no stochastic input at all);
* the *path map* `pathBits` from the array to `Fin n → Bool`, together with the
  identities `psum (pathBits …) = symmetricWalk …` and `runMax = rmax (pathBits …)`
  which place the actual walk exactly inside the verified reflection module
  `results/lean/areas/reflection/Reflect/*`;
* **one** stochastic input, the exact finite-cylinder law of the actual process,
  isolated as the predicate `PathLawFinset` (equivalently `PathLawPattern`, the
  fair-Rademacher increment masses `(1/2)^n`); from it we derive the exact
  running-maximum law of the actual walk, the paper's
  `P(max_{k ≤ n} S_k < b) ≤ 2√2·b/√(n+1)` bound, and the complementary hitting
  lower bound.

No unproved holes and no custom axioms; `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound` for every declaration.
-/
import Swarm.Trajectory
import Swarm.UniformArray
import Swarm.Reflect.Basic
import Swarm.Reflect.Main
import Swarm.Reflect.Law
import Swarm.Reflect.Choose
import Swarm.Reflect.SqrtBound

open MeasureTheory ProbabilityTheory Set Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

set_option maxHeartbeats 800000

namespace Swarming.SymmTransport

/-! ## 1. The exact increment of the actual auxiliary process -/

/-- The increment actually used by `symmetricWalk` at departure `n`: the unbiased
(threshold `1/2`) step driven by the array coordinate consulted at the departure
of walker `i` at time `n`. -/
noncomputable def symmInc {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) : ℤ :=
  symmetricStep (U (departureCoord p m U n i))

/-- Definitional unfolding. -/
theorem symmInc_def {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    symmInc p m U i n =
      symmetricStep
        (U (i, (trajectory p m U n).pos i,
          (trajectory p m U n).ell i ((trajectory p m U n).pos i))) := rfl

/-- Every increment is `+1` or `-1`. -/
theorem symmInc_eq_one_or_neg_one {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    symmInc p m U i n = 1 ∨ symmInc p m U i n = -1 := by
  unfold symmInc symmetricStep
  split <;> simp

/-- **The path recursion of the actual process**, by definition. -/
theorem symmetricWalk_succ {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    symmetricWalk p m U i (n + 1) = symmetricWalk p m U i n + symmInc p m U i n := rfl

/-- **Step 3: the actual walk is the partial sum of its increments.** -/
theorem symmetricWalk_eq_sum {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ n : ℕ, symmetricWalk p m U i n = ∑ k ∈ Finset.range n, symmInc p m U i k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [symmetricWalk_succ, ih, Finset.sum_range_succ]

/-! ## 2. The path map into the reflection module -/

/-- The `ℕ`-indexed sign of the actual walk at departure `k`. -/
noncomputable def pathBitFn {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (k : ℕ) : Bool :=
  if symmInc p m U i k = 1 then true else false

/-- The length-`n` sign path of the actual walk: the object on which the verified
reflection/counting results act. -/
noncomputable def pathBits {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    Fin n → Bool :=
  fun k => if symmInc p m U i (k : ℕ) = 1 then true else false

theorem pathBits_apply {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ)
    (k : Fin n) : pathBits p m U i n k = pathBitFn p m U i (k : ℕ) := rfl

/-- The sign path records exactly the sign of the increment. -/
theorem step_pathBits {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ)
    (k : Fin n) : SwarmReflect.step (pathBits p m U i n k) = symmInc p m U i (k : ℕ) := by
  rcases symmInc_eq_one_or_neg_one p m U i (k : ℕ) with h | h <;>
    simp [pathBits, SwarmReflect.step, h]

/-- `psum` of a length-`n` path is the sum of the first `k` steps. -/
theorem psum_pathBits_eq {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ (n k : ℕ), k ≤ n →
      SwarmReflect.psum (pathBits p m U i n) k = ∑ j ∈ Finset.range k, symmInc p m U i j := by
  intro n k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ n := by omega
      rw [SwarmReflect.psum_succ_of_lt _ (by omega), ih hk', Finset.sum_range_succ,
        step_pathBits]

/-- On its own index range the sign path reproduces the actual walk. -/
theorem psum_pathBits_eq_symmetricWalk {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N)
    {n k : ℕ} (hk : k ≤ n) :
    SwarmReflect.psum (pathBits p m U i n) k = symmetricWalk p m U i k := by
  rw [psum_pathBits_eq p m U i n k hk, symmetricWalk_eq_sum]

/-- **Running maximum of the actual walk** (max over times `0, …, n`). -/
noncomputable def runMax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) : ℕ → ℤ
  | 0 => symmetricWalk p m U i 0
  | (k + 1) => max (runMax p m U i k) (symmetricWalk p m U i (k + 1))

@[simp] theorem runMax_zero {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    runMax p m U i 0 = 0 := by
  simp [runMax]

theorem runMax_succ {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (k : ℕ) :
    runMax p m U i (k + 1) = max (runMax p m U i k) (symmetricWalk p m U i (k + 1)) := rfl

/-- The running maximum dominates every visited position. -/
theorem symmetricWalk_le_runMax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ {j n : ℕ}, j ≤ n → symmetricWalk p m U i j ≤ runMax p m U i n := by
  intro j n hjn
  induction n with
  | zero =>
      have : j = 0 := by omega
      subst this; simp
  | succ n ih =>
      rcases Nat.lt_or_ge j (n + 1) with h | h
      · exact le_trans (ih (by omega)) (le_max_left _ _)
      · have : j = n + 1 := by omega
        subst this
        rw [runMax_succ]
        exact le_max_right _ _

/-- A threshold is met by the running maximum iff it is met by a visited position. -/
theorem runMax_ge_iff {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (b : ℤ) :
    ∀ n : ℕ, b ≤ runMax p m U i n ↔ ∃ k ≤ n, b ≤ symmetricWalk p m U i k := by
  intro n
  induction n with
  | zero =>
      simp only [runMax_zero]
      constructor
      · intro h; exact ⟨0, le_rfl, h⟩
      · rintro ⟨k, hk, hk'⟩
        have : k = 0 := by omega
        subst this; simpa using hk'
  | succ n ih =>
      rw [runMax_succ, le_max_iff]
      constructor
      · rintro (h1 | h2)
        · obtain ⟨k, hk, hk'⟩ := ih.mp h1
          exact ⟨k, by omega, hk'⟩
        · exact ⟨n + 1, le_rfl, h2⟩
      · rintro ⟨k, hk, hk'⟩
        by_cases h : k ≤ n
        · exact Or.inl (ih.mpr ⟨k, h, hk'⟩)
        · have : k = n + 1 := by omega
          subst this
          exact Or.inr hk'

/-! ## 3. Bridging the actual walk to the verified reflection module -/

/-- `rmax` of the sign path of the actual walk is the running maximum of the walk
(any truncation length `k ≤ n` may be used). -/
theorem rmax_pathBits_eq_runMax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ (n k : ℕ), k ≤ n → SwarmReflect.rmax (pathBits p m U i n) k = runMax p m U i k := by
  intro n k
  induction k with
  | zero => intro _; simp [runMax]
  | succ k ih =>
      intro hk
      have hk' : k ≤ n := by omega
      rw [SwarmReflect.rmax_succ, ih hk', psum_pathBits_eq_symmetricWalk p m U i (show k + 1 ≤ n by omega),
        runMax_succ]

/-- **The actual running maximum is `rmax` of the actual sign path.** -/
theorem runMax_eq_rmax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    runMax p m U i n = SwarmReflect.rmax (pathBits p m U i n) n :=
  (rmax_pathBits_eq_runMax p m U i n n le_rfl).symm

/-- The running maximum is below `b` iff every visited position is. -/
theorem runMax_lt_iff {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (b : ℤ) :
    ∀ n : ℕ, runMax p m U i n < b ↔ ∀ k ≤ n, symmetricWalk p m U i k < b := by
  intro n
  induction n with
  | zero =>
      simp only [runMax_zero]
      constructor
      · intro h k hk
        have : k = 0 := by omega
        subst this; simpa using h
      · intro h; simpa using h 0 le_rfl
  | succ n ih =>
      rw [runMax_succ, max_lt_iff]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_or_ge k (n + 1) with h | h
        · exact ih.mp h1 k (by omega)
        · have : k = n + 1 := by omega
          subst this; exact h2
      · intro h
        exact ⟨ih.mpr (fun k hk => h k (by omega)), h (n + 1) le_rfl⟩

/-! ## 4. The isolated stochastic input and the transport to the reflection module

The single stochastic input is `PathLawFinset`: the exact finite-cylinder law of the
*actual* process, as `real`-measure masses of finsets of sign paths.  Its increment
form `PathLawPattern` (fair Rademacher masses `(1/2)^n`) is proved equivalent to it
in §5 below. -/

/-- Exact finite-cylinder law of the actual auxiliary process `symmetricWalk`. -/
def PathLawFinset {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) : Prop :=
  ∀ (n : ℕ) (A : Finset (Fin n → Bool)),
    (arrayMeasure N).real {U : Array N | pathBits p m U i n ∈ A} = (A.card : ℝ) / 2 ^ n

/-- Generic transfer: a property of the array that agrees pointwise with membership in a
finset of sign paths has the finitely supported mass `♯A / 2^n`. -/
theorem prob_of_finset {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    {n : ℕ} {A : Finset (Fin n → Bool)} {P : Array N → Prop}
    (h : ∀ U, (pathBits p m U i n ∈ A ↔ P U)) :
    (arrayMeasure N).real {U : Array N | P U} = (A.card : ℝ) / 2 ^ n := by
  rw [← hLaw n A]
  congr 1
  ext U
  exact (h U).symm

/-- **Step 4 (exact law of the running maximum).** -/
theorem prob_nonhit_eq {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    (n : ℕ) (b : ℤ) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < b}
      = ((Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)).card : ℝ)
          / 2 ^ n := by
  refine prob_of_finset hLaw
    (A := Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)) ?_
  intro U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← runMax_eq_rmax p m U i n, runMax_lt_iff]

/-- **The running-maximum bound for the actual walk** (the paper's
`P(max_{k ≤ n} S_k < b) ≤ C b n^{-1/2}`, `C = 2√2`). -/
theorem prob_nonhit_le_sqrt {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  rw [prob_nonhit_eq hLaw n (b : ℤ)]
  have hcard : (((Finset.univ.filter
        (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < (b : ℤ))).card : ℝ))
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1) :=
    SwarmReflect.card_rmax_lt_le_sqrt (n := n) hb
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  calc ((Finset.univ.filter
        (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < (b : ℤ))).card : ℝ) / 2 ^ n
      ≤ ((2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1)) / 2 ^ n := by
        gcongr
    _ = (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
        field_simp

/-- **Step 4 (exact hitting law).** The probability that the actual walk reaches level `b`
before time `n` is the reflection count `♯{S_n ≥ b} + ♯{S_n > b}` over `2^n` paths. -/
theorem prob_hit_eq {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    (n : ℕ) {b : ℤ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∃ k ≤ n, b ≤ symmetricWalk p m U i k}
      = (((Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.psum ω n)).card : ℝ)
          + ((Finset.univ.filter (fun ω : Fin n → Bool => b < SwarmReflect.psum ω n)).card : ℝ))
        / 2 ^ n := by
  have hset : {U : Array N | ∃ k ≤ n, b ≤ symmetricWalk p m U i k}
      = {U : Array N | pathBits p m U i n ∈
          (Finset.univ.filter (fun ω : Fin n → Bool => ¬ SwarmReflect.rmax ω n < b))} := by
    ext U
    simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
      ← runMax_eq_rmax p m U i n, runMax_ge_iff]
  rw [hset, hLaw n _]
  have hf : (Finset.univ.filter (fun ω : Fin n → Bool => ¬ SwarmReflect.rmax ω n < b))
      = (Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.rmax ω n)) := by
    apply Finset.filter_congr
    intro ω _
    rw [not_lt]
  rw [hf, SwarmReflect.card_rmax_ge hb, Nat.cast_add]

/-- The same hitting law written with the complement count. -/
theorem prob_hit_eq_compl {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    (n : ℕ) (b : ℤ) :
    (arrayMeasure N).real {U : Array N | ∃ k ≤ n, b ≤ symmetricWalk p m U i k}
      = (((2 ^ n - (Finset.univ.filter
            (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)).card) : ℕ) : ℝ) / 2 ^ n := by
  have hset : {U : Array N | ∃ k ≤ n, b ≤ symmetricWalk p m U i k}
      = {U : Array N | pathBits p m U i n ∈
          (Finset.univ \ Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b))} := by
    ext U
    simp only [Set.mem_ofPred_eq, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt, ← runMax_eq_rmax p m U i n, runMax_ge_iff]
  rw [hset, hLaw n _]
  have hsub : (Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b))
      ⊆ (Finset.univ : Finset (Fin n → Bool)) := Finset.subset_univ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  have hle : (Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)).card
      ≤ 2 ^ n := by
    rw [← hcard]; omega
  have : (Finset.univ \ Finset.univ.filter
      (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)).card
      = 2 ^ n - (Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)).card := by
    omega
  rw [this]

/-- **Complementary hitting bound for the actual walk.** -/
theorem prob_hit_ge_one_sub_sqrt {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hLaw : PathLawFinset p m i) (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    1 - (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1)
      ≤ (arrayMeasure N).real
          {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ symmetricWalk p m U i k} := by
  rw [prob_hit_eq_compl hLaw n (b : ℤ)]
  set c : ℕ := (Finset.univ.filter
    (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < (b : ℤ))).card with hc
  have hcard : (c : ℝ) ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1) := by
    rw [hc]
    exact SwarmReflect.card_rmax_lt_le_sqrt (n := n) hb
  have hcle : c ≤ 2 ^ n := by
    have hsub : (Finset.univ.filter
        (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < (b : ℤ)))
        ⊆ (Finset.univ : Finset (Fin n → Bool)) := Finset.subset_univ _
    calc c ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_card hsub
      _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hcast : (((2 ^ n - c : ℕ)) : ℝ) = 2 ^ n - (c : ℝ) := by
    push_cast [Nat.cast_sub hcle]
    ring
  rw [hcast]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hc2 : (c : ℝ) / 2 ^ n
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc (c : ℝ) * (2 ^ n)⁻¹
        ≤ ((2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1)) * (2 ^ n)⁻¹ := by
          gcongr
      _ = (2 * (b : ℝ) + 1) * Real.sqrt 2 * (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
          have hsqrt : (Real.sqrt ((n : ℝ) + 1)) ≠ 0 := by positivity
          have h2' : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp
  have hfin : (2 ^ n - (c : ℝ)) / 2 ^ n = 1 - (c : ℝ) / 2 ^ n := by
    rw [sub_div, div_self (ne_of_gt h2)]
  rw [hfin]
  linarith

/-! ## 5. The interface in increment (fair Rademacher) form

The problem's step 2 asks for the joint law of the increments
`symmInc p m U i k = symmetricStep (U (departureCoord p m U k i))`: every finite
pattern has mass `(1/2)^r`.  We state that as `PathLawPattern` and prove

* `PathLawFinset → PathLawPattern` (unconditional), and
* `PathLawPattern → PathLawFinset` (given measurability of the increments, which is
  part of any `iIndepFun` statement about them),

so the two interfaces carry exactly the same stochastic content. -/

/-- **Fair Rademacher finite pattern law** for the increments of the actual process. -/
def PathLawPattern {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) : Prop :=
  ∀ (r : ℕ) (σ : Fin r → ℤ), (∀ k, σ k = 1 ∨ σ k = -1) →
    (arrayMeasure N).real {U : Array N | ∀ k : Fin r, symmInc p m U i (k : ℕ) = σ k}
      = (1 / 2) ^ r

/-- The `Bool` reading of a `±1` integer step. -/
theorem step_ite (z : ℤ) (hz : z = 1 ∨ z = -1) :
    SwarmReflect.step (if z = 1 then true else false) = z := by
  rcases hz with h | h <;> simp [SwarmReflect.step, h]

theorem step_inj {b₁ b₂ : Bool} (h : SwarmReflect.step b₁ = SwarmReflect.step b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | rfl | (simp [SwarmReflect.step] at h)

/-- The `±1` reading of a `Bool` step is faithful. -/
theorem ite_step (b : Bool) : (if SwarmReflect.step b = 1 then true else false) = b := by
  cases b <;> simp [SwarmReflect.step]

/-- The sign path determines the increment sequence and conversely. -/
theorem pathBits_eq_iff {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) {r : ℕ}
    (σ : Fin r → Bool) :
    pathBits p m U i r = σ
      ↔ ∀ k : Fin r, symmInc p m U i (k : ℕ) = SwarmReflect.step (σ k) := by
  constructor
  · intro h k
    have hk : SwarmReflect.step (pathBits p m U i r k) = SwarmReflect.step (σ k) := by rw [h]
    rwa [step_pathBits] at hk
  · intro h
    funext k
    simp only [pathBits]
    rw [h k, ite_step]

/-- The finset interface implies the fair-Rademacher pattern law. -/
theorem pathLawPattern_of_finset {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hLaw : PathLawFinset p m i) : PathLawPattern p m i := by
  intro r σ hσ
  set τ : Fin r → Bool := fun k => if σ k = 1 then true else false with hτ
  have hmem : ∀ U, (pathBits p m U i r ∈ ({τ} : Finset (Fin r → Bool)) ↔
      ∀ k : Fin r, symmInc p m U i (k : ℕ) = σ k) := by
    intro U
    rw [Finset.mem_singleton, pathBits_eq_iff]
    constructor
    · intro h k
      rw [h k]
      exact step_ite (σ k) (hσ k)
    · intro h k
      rw [h k]
      exact (step_ite (σ k) (hσ k)).symm
  have hP := prob_of_finset hLaw (A := ({τ} : Finset (Fin r → Bool))) hmem
  rw [hP, Finset.card_singleton, Nat.cast_one, div_eq_mul_inv]
  rw [show (1 : ℝ) * (2 ^ r)⁻¹ = (1 / 2 : ℝ) ^ r from by
    rw [one_mul, one_div, inv_pow]]

/-- Measurability of the increments (a byproduct of any `iIndepFun` statement about them). -/
def IncMeasurable {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) : Prop :=
  ∀ k : ℕ, Measurable (fun U : Array N => symmInc p m U i k)

theorem measurable_pathBits {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hmeas : IncMeasurable p m i) (n : ℕ) :
    Measurable (fun U : Array N => pathBits p m U i n) := by
  apply measurable_pi_lambda
  intro k
  have hk : (fun U : Array N => pathBits p m U i n k)
      = (fun z : ℤ => if z = 1 then true else false) ∘ (fun U => symmInc p m U i (k : ℕ)) := rfl
  rw [hk]
  exact Measurable.comp (measurable_of_countable _) (hmeas (k : ℕ))

/-- The fair-Rademacher pattern law (plus measurability) implies the finset interface. -/
theorem pathLawFinset_of_pattern {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hpat : PathLawPattern p m i) (hmeas : IncMeasurable p m i) : PathLawFinset p m i := by
  intro n A
  have hbits := measurable_pathBits hmeas n
  have hsingle : ∀ σ ∈ A, MeasurableSet ((fun U : Array N => pathBits p m U i n) ⁻¹' {σ}) :=
    fun σ _ => hbits (measurableSet_singleton σ)
  have hsum := MeasureTheory.sum_measureReal_preimage_singleton (μ := arrayMeasure N) A
    (f := fun U : Array N => pathBits p m U i n) hsingle
  have hgoal : (fun U : Array N => pathBits p m U i n) ⁻¹' (A : Set (Fin n → Bool))
      = {U : Array N | pathBits p m U i n ∈ A} := by
    ext U
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Finset.mem_coe]
  have hterm : ∀ σ ∈ A, (arrayMeasure N).real
      ((fun U : Array N => pathBits p m U i n) ⁻¹' ({σ} : Set (Fin n → Bool))) = (1 / 2) ^ n := by
    intro σ _
    have hσ : ∀ k : Fin n, (SwarmReflect.step (σ k) = 1 ∨ SwarmReflect.step (σ k) = -1) :=
      fun k => SwarmReflect.step_eq (σ k)
    have hset : (fun U : Array N => pathBits p m U i n) ⁻¹' ({σ} : Set (Fin n → Bool))
        = {U : Array N | ∀ k : Fin n, symmInc p m U i (k : ℕ) = SwarmReflect.step (σ k)} := by
      ext U
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact pathBits_eq_iff p m U i σ
    rw [hset]
    exact hpat n (fun k => SwarmReflect.step (σ k)) hσ
  rw [← hgoal, ← hsum, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
    show (1 * 2⁻¹ : ℝ) = 2⁻¹ by norm_num, inv_pow, div_eq_mul_inv]

/-! ## 6. Pattern law over `Finset.range`, endpoint law and the two-sided reflection form -/

/-- The fair-Rademacher pattern law in `Finset.range` form: arbitrary finite path patterns
of the increments of the actual process have mass `(1/2)^r`. -/
theorem pattern_range {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hpat : PathLawPattern p m i)
    (r : ℕ) (σ : ℕ → ℤ) (hσ : ∀ k < r, σ k = 1 ∨ σ k = -1) :
    (arrayMeasure N).real {U : Array N | ∀ k ∈ Finset.range r, symmInc p m U i k = σ k}
      = (1 / 2) ^ r := by
  have hset : {U : Array N | ∀ k ∈ Finset.range r, symmInc p m U i k = σ k}
      = {U : Array N | ∀ k : Fin r, symmInc p m U i (k : ℕ) = σ (k : ℕ)} := by
    ext U
    simp only [Set.mem_ofPred_eq, Finset.mem_range]
    constructor
    · intro h k; exact h k k.isLt
    · intro h k hk; exact h ⟨k, hk⟩
  rw [hset]
  exact hpat r (fun k => σ (k : ℕ)) (fun k => hσ k k.isLt)

/-- **Endpoint law of the actual walk.** -/
theorem prob_endpoint_eq {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    (n : ℕ) (k : ℤ) :
    (arrayMeasure N).real {U : Array N | symmetricWalk p m U i n = k}
      = ((Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.psum ω n = k)).card : ℝ)
          / 2 ^ n := by
  refine prob_of_finset hLaw
    (A := Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.psum ω n = k)) ?_
  intro U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, psum_pathBits_eq_symmetricWalk p m U i
    (le_refl n)]

/-- The endpoint law in binomial form: for `k = 2m - n` the mass is `n.choose m / 2^n`. -/
theorem prob_endpoint_eq_choose {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hLaw : PathLawFinset p m i) (n j : ℕ) :
    (arrayMeasure N).real
        {U : Array N | symmetricWalk p m U i n = 2 * (j : ℤ) - (n : ℤ)}
      = (n.choose j : ℝ) / 2 ^ n := by
  rw [prob_endpoint_eq hLaw n (2 * (j : ℤ) - (n : ℤ)), SwarmReflect.card_psum_eq_choose]

/-- One side of the reflection law: the hitting probability is at most twice the endpoint
mass above the level. -/
theorem prob_hit_le {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N} (hLaw : PathLawFinset p m i)
    (n : ℕ) {b : ℤ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∃ k ≤ n, b ≤ symmetricWalk p m U i k}
      ≤ 2 * (arrayMeasure N).real {U : Array N | b ≤ symmetricWalk p m U i n} := by
  have hend : (arrayMeasure N).real {U : Array N | b ≤ symmetricWalk p m U i n}
      = ((Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.psum ω n)).card : ℝ)
          / 2 ^ n := by
    refine prob_of_finset hLaw
      (A := Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.psum ω n)) ?_
    intro U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      psum_pathBits_eq_symmetricWalk p m U i (le_refl n)]
  rw [prob_hit_eq hLaw n hb, hend]
  set c1 : ℕ := (Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.psum ω n)).card with hc1
  set c2 : ℕ := (Finset.univ.filter (fun ω : Fin n → Bool => b < SwarmReflect.psum ω n)).card with hc2
  set cR : ℕ := (Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.rmax ω n)).card with hcR
  have hge := SwarmReflect.card_rmax_ge (n := n) hb
  have hle := SwarmReflect.card_rmax_ge_le (n := n) hb
  have hle' : cR ≤ 2 * c1 := by rw [hcR, hc1]; exact hle
  have hge' : cR = c1 + c2 := by rw [hcR, hc1, hc2]; exact hge
  have hsum : (c1 : ℝ) + (c2 : ℝ) ≤ 2 * (c1 : ℝ) := by
    have hnat : c1 + c2 ≤ 2 * c1 := by rw [← hge']; exact hle'
    exact_mod_cast hnat
  calc ((c1 : ℝ) + (c2 : ℝ)) / 2 ^ n ≤ (2 * (c1 : ℝ)) / 2 ^ n := by gcongr
    _ = 2 * ((c1 : ℝ) / 2 ^ n) := by rw [mul_div_assoc]

/-! ## 7. The `iIndepFun` interface: fair increments imply the path law

This closes the loop with the increment-law direction.  The stochastic content assumed
here is *exactly* the pair of statements that direction must produce for the actual
process: the increments `symmInc p m U i ·` are `iIndepFun` under `arrayMeasure N`, and
each has the two-point fair Rademacher law.  Everything else is proved. -/

/-- Fair two-point marginal law of one increment. -/
def FairMarginal {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) : Prop :=
  ∀ k : ℕ,
    (arrayMeasure N).real {U : Array N | symmInc p m U i k = 1} = 1 / 2 ∧
    (arrayMeasure N).real {U : Array N | symmInc p m U i k = -1} = 1 / 2

/-- `iIndepFun` increments with fair two-point marginals give the finite pattern law. -/
theorem pattern_range_of_iIndepFun {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hInd : iIndepFun (fun (k : ℕ) (U : Array N) => symmInc p m U i k) (arrayMeasure N))
    (hm : FairMarginal p m i) (r : ℕ) (σ : ℕ → ℤ)
    (hσ : ∀ k < r, σ k = 1 ∨ σ k = -1) :
    (arrayMeasure N).real {U : Array N | ∀ k ∈ Finset.range r, symmInc p m U i k = σ k}
      = (1 / 2) ^ r := by
  have hE := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hInd) (Finset.range r)
    (sets := fun k => ({σ k} : Set ℤ)) (fun k _ => measurableSet_singleton _)
  have hreal : (arrayMeasure N).real
      (⋂ k ∈ Finset.range r, (fun U : Array N => symmInc p m U i k) ⁻¹' ({σ k} : Set ℤ))
      = ∏ k ∈ Finset.range r,
          (arrayMeasure N).real ((fun U : Array N => symmInc p m U i k) ⁻¹' ({σ k} : Set ℤ)) := by
    rw [MeasureTheory.measureReal_def, hE, ENNReal.toReal_prod]
    simp only [MeasureTheory.measureReal_def]
  have hset : {U : Array N | ∀ k ∈ Finset.range r, symmInc p m U i k = σ k}
      = ⋂ k ∈ Finset.range r, (fun U : Array N => symmInc p m U i k) ⁻¹' ({σ k} : Set ℤ) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset, hreal]
  have hterm : ∀ k ∈ Finset.range r,
      (arrayMeasure N).real ((fun U : Array N => symmInc p m U i k) ⁻¹' ({σ k} : Set ℤ)) = 1 / 2 := by
    intro k hk
    rcases hσ k (Finset.mem_range.mp hk) with h | h
    · rw [h]; exact (hm k).1
    · rw [h]; exact (hm k).2
  rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]

/-- Reindexing the `Finset.range` pattern law to `Fin r` patterns. -/
theorem pathLawPattern_of_range {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (h : ∀ (r : ℕ) (σ : ℕ → ℤ), (∀ k < r, σ k = 1 ∨ σ k = -1) →
      (arrayMeasure N).real {U : Array N | ∀ k ∈ Finset.range r, symmInc p m U i k = σ k}
        = (1 / 2) ^ r) : PathLawPattern p m i := by
  intro r σ hσ
  have hset : {U : Array N | ∀ k : Fin r, symmInc p m U i (k : ℕ) = σ k}
      = {U : Array N | ∀ k ∈ Finset.range r,
          symmInc p m U i k = (fun j => if hj : j < r then σ ⟨j, hj⟩ else 1) k} := by
    ext U
    simp only [Set.mem_ofPred_eq, Finset.mem_range]
    constructor
    · intro h1 k hk
      rw [dif_pos hk]
      exact h1 ⟨k, hk⟩
    · intro h1 k
      have hk := h1 k k.isLt
      rwa [dif_pos k.isLt] at hk
  rw [hset]
  exact h r (fun j => if hj : j < r then σ ⟨j, hj⟩ else 1) (fun k hk => by
    rw [dif_pos hk]
    exact hσ ⟨k, hk⟩)

/-- **The fair increment law (`iIndepFun` form) gives the pattern law.** -/
theorem pathLawPattern_of_iIndepFun {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hInd : iIndepFun (fun (k : ℕ) (U : Array N) => symmInc p m U i k) (arrayMeasure N))
    (hm : FairMarginal p m i) : PathLawPattern p m i :=
  pathLawPattern_of_range (fun r σ hσ => pattern_range_of_iIndepFun hInd hm r σ hσ)

/-- **Everything from the `iIndepFun` interface**: the exact finite-cylinder law. -/
theorem pathLawFinset_of_iIndepFun {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hInd : iIndepFun (fun (k : ℕ) (U : Array N) => symmInc p m U i k) (arrayMeasure N))
    (hm : FairMarginal p m i) (hmeas : IncMeasurable p m i) : PathLawFinset p m i :=
  pathLawFinset_of_pattern (pathLawPattern_of_iIndepFun hInd hm) hmeas

/-- **The running-maximum bound for the actual walk, from the `iIndepFun` interface.** -/
theorem prob_nonhit_le_sqrt_of_iIndepFun {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hInd : iIndepFun (fun (k : ℕ) (U : Array N) => symmInc p m U i k) (arrayMeasure N))
    (hm : FairMarginal p m i) (hmeas : IncMeasurable p m i) (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) :=
  prob_nonhit_le_sqrt (pathLawFinset_of_iIndepFun hInd hm hmeas) n hb

/-! ## 7b. Measurability-free running-maximum bound from the increment pattern law

The paper's running-maximum estimate needs no measurability of the path map: the
finset-subadditivity `measureReal_biUnion_finset_le` suffices.  Hence the bound below
follows from the fair-Rademacher increment pattern law alone. -/

/-- The mass of a single sign path is `2^{-n}` under the increment pattern law. -/
theorem pathBits_eq_pattern_mass {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hpat : PathLawPattern p m i) (n : ℕ) (σ : Fin n → Bool) :
    (arrayMeasure N).real {U : Array N | pathBits p m U i n = σ} = (1 / 2) ^ n := by
  have hset : {U : Array N | pathBits p m U i n = σ}
      = {U : Array N | ∀ k : Fin n, symmInc p m U i (k : ℕ) = SwarmReflect.step (σ k)} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    exact pathBits_eq_iff p m U i σ
  rw [hset]
  exact hpat n (fun k => SwarmReflect.step (σ k)) (fun k => SwarmReflect.step_eq (σ k))

theorem card_mul_half_pow_eq_div (c n : ℕ) : (c : ℝ) * (1 / 2) ^ n = (c : ℝ) / 2 ^ n := by
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, inv_pow, div_eq_mul_inv]

/-- Arithmetic helper: the reflection count bound, divided by `2^n`. -/
theorem card_div_two_pow_le_sqrt {c n b : ℕ}
    (hcard : (c : ℝ) ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1)) :
    (c : ℝ) / 2 ^ n ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  calc (c : ℝ) / 2 ^ n
      ≤ ((2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1)) / 2 ^ n := by
        gcongr
    _ = (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
      have hsqrt : (Real.sqrt ((n : ℝ) + 1)) ≠ 0 := by positivity
      have h2' : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp

/-- **The running-maximum bound for the actual walk from the increment pattern law.** -/
theorem prob_nonhit_le_sqrt_of_pattern {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hpat : PathLawPattern p m i) (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  set A : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < (b : ℤ)) with hA
  have hset : {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      = ⋃ σ ∈ A, {U : Array N | pathBits p m U i n = σ} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      have hmem : pathBits p m U i n ∈ A := by
        rw [hA, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← runMax_eq_rmax, runMax_lt_iff]; exact h⟩
      exact ⟨pathBits p m U i n, hmem, rfl⟩
    · rintro ⟨σ, hσ, hU⟩ k hk
      rw [hA, Finset.mem_filter] at hσ
      obtain ⟨-, hσ⟩ := hσ
      rw [← hU] at hσ
      rw [← psum_pathBits_eq_symmetricWalk p m U i hk]
      calc SwarmReflect.psum (pathBits p m U i n) k
          ≤ SwarmReflect.rmax (pathBits p m U i n) k := SwarmReflect.psum_le_rmax _ k
        _ ≤ SwarmReflect.rmax (pathBits p m U i n) n := SwarmReflect.rmax_mono _ hk
        _ < (b : ℤ) := hσ
  rw [hset]
  refine le_trans (MeasureTheory.measureReal_biUnion_finset_le A _) ?_
  have hterm : ∀ σ ∈ A,
      (arrayMeasure N).real {U : Array N | pathBits p m U i n = σ} = (1 / 2) ^ n :=
    fun σ _ => pathBits_eq_pattern_mass hpat n σ
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, card_mul_half_pow_eq_div]
  refine card_div_two_pow_le_sqrt ?_
  rw [hA]
  exact SwarmReflect.card_rmax_lt_le_sqrt (n := n) hb

/-- **The textbook running-maximum law for the actual walk**:
`P(max_{k ≤ n} S_k < b) = P(S_n = b) + P(|S_n| < b)`. -/
theorem prob_nonhit_eq_classical {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hLaw : PathLawFinset p m i) (n : ℕ) {b : ℤ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < b}
      = (((Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.psum ω n = b)).card : ℝ)
          + ((Finset.univ.filter (fun ω : Fin n → Bool => |SwarmReflect.psum ω n| < b)).card : ℝ))
        / 2 ^ n := by
  rw [prob_nonhit_eq hLaw n b, SwarmReflect.card_rmax_lt (n := n) hb, Nat.cast_add]

/-- The running-maximum mass in binomial form, `≤ (2b+1)·C(n, n/2)/2^n`. -/
theorem prob_nonhit_le_middle {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hLaw : PathLawFinset p m i) (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      ≤ ((2 * b + 1) * n.choose (n / 2) : ℕ) / 2 ^ n := by
  rw [prob_nonhit_eq hLaw n (b : ℤ)]
  have hcard := SwarmReflect.card_rmax_lt_le_middle (n := n) b hb
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  gcongr

/-- The paper's running-maximum estimate, restated from `PathLawFinset`. -/
theorem prob_nonhit_le_sqrt' {N : ℕ} {p : ℝ} {m : ℕ} {i : Fin N}
    (hLaw : PathLawFinset p m i) (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) :=
  prob_nonhit_le_sqrt hLaw n hb

end Swarming.SymmTransport

/-! ## 8. Axiom audit -/


