/-
  **`(diam)` input, part 1: the group potential as a `posFilt`-measurable functional
  and its explicit bound.**

  This file supplies the ingredients that are pure measure theory:

  * an explicit linear bound on `hfix w` for `1/2 ≤ w ≤ 1` (and hence on `H^w`), which is
    what makes the potential increment integrable;
  * equality of the path-prefix σ-algebra with the position filtration `posFilt`;
  * `posFilt`-measurability (the paper's natural filtration of the walks) of the
    functionals `U ↦ wA p m U n A x`, `U ↦ hfix (wA p m · n A) u` and of the composed
    jump step `hZpot` at the random positions `X_n^i` and `X_n^i - 1`.

  Nothing probabilistic is assumed; all statements are about the actual model.
-/
import Swarm.Imports
import Swarm.Swarming
import Swarm.SepGroup
import Swarm.SeparatedGroups
import Swarm.CondExp
import Swarm.PullOut

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SwarmM3

open Swarming Swarming.Uniform Swarming.Trajectory SepGroup.Model

variable {N : ℕ}

/-- Constant functions are measurable for the position filtration (with the σ-algebra
pinned, so that no ambient product instance is picked up). -/
theorem measurable_const_posFilt (p : ℝ) (m n : ℕ) (c : ℝ) :
    Measurable[posFilt N p m n] (fun _ : Array N => c) := measurable_const

theorem measurable_const_posFilt_int (p : ℝ) (m n : ℕ) (c : ℤ) :
    Measurable[posFilt N p m n] (fun _ : Array N => c) := measurable_const

/-! ### An explicit linear bound for the potential step function -/

/-- `hfix w n ≤ 2 n + 3` when `1/2 ≤ w ≤ 1`. -/
theorem hfix_le_lin (w : ℕ → ℝ) (hw0 : ∀ n, 1 / 2 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    ∀ n, Cookie.hfix w n ≤ 2 * (n : ℝ) + 3
  | 0 => by
      rw [Cookie.hfix_eq, Cookie.hprev_zero]
      have hpos : 0 < w 0 := by linarith [hw0 0]
      rw [div_le_iff₀ hpos]
      nlinarith [hw0 0, hw1 0]
  | (k + 1) => by
      have hk := hfix_le_lin w hw0 hw1 k
      have hpos : 0 < w (k + 1) := by linarith [hw0 (k + 1)]
      have hge : (1 : ℝ) ≤ Cookie.hfix w k :=
        Cookie.one_le_hfix w (fun j => by linarith [hw0 j]) hw1 k
      have h0 : (0 : ℝ) ≤ Cookie.hfix w k := by linarith
      have hstep : (1 + (1 - w (k + 1)) * Cookie.hfix w k) / w (k + 1)
          ≤ 2 + Cookie.hfix w k := by
        rw [div_le_iff₀ hpos]
        have h2 := hw0 (k + 1)
        nlinarith [h2, h0]
      calc Cookie.hfix w (k + 1)
          = (1 + (1 - w (k + 1)) * Cookie.hfix w k) / w (k + 1) := by
            rw [Cookie.hfix_eq, Cookie.hprev_succ]
        _ ≤ 2 + Cookie.hfix w k := hstep
        _ ≤ 2 + (2 * (k : ℝ) + 3) := by linarith
        _ = 2 * ((k + 1 : ℕ) : ℝ) + 3 := by push_cast; ring

/-- `Hfix w k ≤ k (2k+3)` under the same hypothesis. -/
theorem Hfix_le_lin (w : ℕ → ℝ) (hw0 : ∀ n, 1 / 2 ≤ w n) (hw1 : ∀ n, w n ≤ 1) (k : ℕ) :
    Cookie.Hfix w k ≤ (k : ℝ) * (2 * (k : ℝ) + 3) := by
  have hterm : ∀ u ∈ Finset.range k, Cookie.hfix w u ≤ 2 * (k : ℝ) + 3 := by
    intro u hu
    have hu' : u ≤ k := le_of_lt (Finset.mem_range.mp hu)
    have h := hfix_le_lin w hw0 hw1 u
    have huc : (u : ℝ) ≤ (k : ℝ) := by exact_mod_cast hu'
    linarith
  calc Cookie.Hfix w k = ∑ u ∈ Finset.range k, Cookie.hfix w u := rfl
    _ ≤ ∑ _u ∈ Finset.range k, (2 * (k : ℝ) + 3) := Finset.sum_le_sum hterm
    _ = (k : ℝ) * (2 * (k : ℝ) + 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Explicit bound for the `ℤ`-valued potential `H^w` on `|x| ≤ n`. -/
theorem abs_HZ_le {w : ℕ → ℝ} (hw0 : ∀ n, 1 / 2 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    {x : ℤ} {n : ℕ} (hx : |x| ≤ (n : ℤ)) :
    |SepGroup.HZ w x| ≤ (n : ℝ) * (2 * (n : ℝ) + 3) + 3 := by
  have hpos : ∀ j, 0 < w j := fun j => by linarith [hw0 j]
  have hone : ∀ j, 1 ≤ Cookie.hfix w j := Cookie.one_le_hfix w hpos hw1
  rcases lt_or_ge x 0 with hneg | hnonneg
  · rw [SepGroup.HZ_neg hneg]
    have hxR : (x : ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hxR]
    have h1 : -x ≤ (n : ℤ) := by
      have := (abs_le.mp hx).1
      omega
    have h2 : ((-x : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h3 : ((-x : ℤ) : ℝ) = -(x : ℝ) := by push_cast; ring
    have h5 : -(x : ℝ) ≤ (n : ℝ) := by rw [← h3]; exact h2
    have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  · rw [SepGroup.HZ_nonneg hnonneg]
    have hxle : x.toNat ≤ n := by
      have h := (abs_le.mp hx).2
      omega
    have hxleR : (x.toNat : ℝ) ≤ (n : ℝ) := by exact_mod_cast hxle
    have hnn : (0 : ℝ) ≤ Cookie.Hfix w x.toNat := by
      rw [Cookie.Hfix]
      exact Finset.sum_nonneg fun u _ => by linarith [hone u]
    rw [abs_of_nonneg hnn]
    have hbound := Hfix_le_lin w hw0 hw1 x.toNat
    have hmono : (x.toNat : ℝ) * (2 * (x.toNat : ℝ) + 3) ≤ (n : ℝ) * (2 * (n : ℝ) + 3) := by
      have h0 : (0 : ℝ) ≤ (x.toNat : ℝ) := Nat.cast_nonneg _
      have h0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith

/-! ### The position filtration is the path-prefix filtration -/

/-- The path-prefix σ-algebra of time `n` is contained in the position filtration: every
path-prefix cylinder is a finite intersection of position equalities. -/
theorem pathMeas_le_posFilt (p : ℝ) (m : ℕ) (n : ℕ) :
    SwarmCross.pathMeas p m n ≤ posFilt N p m n := by
  intro s hs
  obtain ⟨t, -, rfl⟩ := hs
  have heq : SwarmCross.pathPrefix p m n ⁻¹' t
      = ⋃ q ∈ t, SwarmCross.pathPrefix p m n ⁻¹' ({q} : Set (Fin (n + 1) → Fin N → ℤ)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨SwarmCross.pathPrefix p m n ω, h, rfl⟩, fun ⟨q, hq, hω⟩ => hω ▸ hq⟩
  rw [heq]
  refine MeasurableSet.biUnion (Set.to_countable t) fun q _ => ?_
  have hfib : SwarmCross.pathPrefix p m n ⁻¹' ({q} : Set (Fin (n + 1) → Fin N → ℤ))
      = ⋂ k : Fin (n + 1), ⋂ i : Fin N,
          {ω : Array N | (trajectory p m ω (k : ℕ)).pos i = q k i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq,
      SwarmCross.pathPrefix]
    constructor
    · intro h k i
      exact congrFun (congrFun h k) i
    · intro h
      funext k i
      exact h k i
  rw [hfib]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun i => ?_
  exact measurable_pos_posFilt p m i (Nat.lt_succ_iff.mp k.2) (measurableSet_singleton (q k i))

/-- Conversely the position filtration is contained in the path-prefix σ-algebra. -/
theorem posFilt_le_pathMeas (p : ℝ) (m : ℕ) :
    posFilt N p m ≤ SwarmCross.pathFilt p m :=
  (Swarming.Trajectory.posFilt_le_iff (N := N) (p := p) (m := m)
    (𝒢 := SwarmCross.pathFilt p m)).mpr fun n i => SwarmCross.pos_adapted p m i n

theorem pathMeas_eq_posFilt (p : ℝ) (m : ℕ) (n : ℕ) :
    SwarmCross.pathMeas p m n = posFilt N p m n :=
  le_antisymm (pathMeas_le_posFilt p m n) ((posFilt_le_pathMeas p m) n)

/-- The one-step right-jump conditional law, in the **position** filtration. -/
theorem condExp_stepUp_posFilt {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (i : Fin N) :
    (arrayMeasure N)[SwarmCross.stepUpInd p m n i | posFilt N p m n]
      =ᵐ[arrayMeasure N] SwarmCross.alphaFun p m n i := by
  have h := SwarmCross.condExp_stepUp (N := N) hp0 hp1 m n i
  rwa [pathMeas_eq_posFilt] at h

/-! ### Measurability of the group weight in the position filtration -/

theorem measurable_wA_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    Measurable[posFilt N p m n] (fun U : Array N => wA p m U n A x) := by
  have hL : ∀ i ∈ A, Measurable[posFilt N p m n]
      (fun U : Array N => L p m U n i (x : ℤ)) :=
    fun i _ => measurable_ell_posFilt p m i (x : ℤ) le_rfl
  have hsum : Measurable[posFilt N p m n]
      (fun U : Array N => ∑ i ∈ A, L p m U n i (x : ℤ)) :=
    Finset.measurable_sum A hL
  have hif : Measurable[posFilt N p m n]
      (fun U : Array N =>
        if m ≤ ∑ i ∈ A, L p m U n i (x : ℤ) then (1 : ℝ) else 0) := by
    refine Measurable.ite ?_ (measurable_const_posFilt p m n 1)
      (measurable_const_posFilt p m n 0)
    exact hsum measurableSet_Ici
  have hmul : Measurable[posFilt N p m n]
      (fun U : Array N =>
        (p - 1 / 2) * (if m ≤ ∑ i ∈ A, L p m U n i (x : ℤ) then (1 : ℝ) else 0)) :=
    (measurable_const_posFilt p m n (p - 1 / 2)).mul hif
  have hhalf : Measurable[posFilt N p m n] (fun _ : Array N => (1 / 2 : ℝ)) :=
    measurable_const_posFilt p m n (1 / 2)
  have hlast : Measurable[posFilt N p m n]
      (fun U : Array N =>
        (p - 1 / 2) * (if m ≤ ∑ i ∈ A, L p m U n i (x : ℤ) then (1 : ℝ) else 0)
          + 1 / 2) := hmul.add hhalf
  simpa [SepGroup.Model.wA, add_comm] using hlast

/-- `hfix` at a fixed site is measurable in the position filtration. -/
theorem measurable_hfix_wA_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (u : ℕ) :
    Measurable[posFilt N p m n]
      (fun U : Array N => Cookie.hfix (wA p m U n A) u) := by
  induction u with
  | zero =>
      have hw := measurable_wA_posFilt (N := N) p m n A 0
      have hfun : (fun U : Array N => Cookie.hfix (wA p m U n A) 0)
          = fun U => (1 + (1 - wA p m U n A 0) * 1) / wA p m U n A 0 := by
        funext U; rw [Cookie.hfix_eq, Cookie.hprev_zero]
      rw [hfun]
      exact ((measurable_const_posFilt p m n 1).add
        (((measurable_const_posFilt p m n 1).sub hw).mul
          (measurable_const_posFilt p m n 1))).div hw
  | succ k ih =>
      have hw := measurable_wA_posFilt (N := N) p m n A (k + 1)
      have hfun : (fun U : Array N => Cookie.hfix (wA p m U n A) (k + 1))
          = fun U => (1 + (1 - wA p m U n A (k + 1)) * Cookie.hfix (wA p m U n A) k)
              / wA p m U n A (k + 1) := by
        funext U; rw [Cookie.hfix_eq, Cookie.hprev_succ]
      rw [hfun]
      exact ((measurable_const_posFilt p m n 1).add
        (((measurable_const_posFilt p m n 1).sub hw).mul ih)).div hw

/-- `Hfix` at a fixed site is measurable in the position filtration. -/
theorem measurable_Hfix_wA_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (k : ℕ) :
    Measurable[posFilt N p m n]
      (fun U : Array N => Cookie.Hfix (wA p m U n A) k) := by
  have hfun : (fun U : Array N => Cookie.Hfix (wA p m U n A) k)
      = fun U => ∑ u ∈ Finset.range k, Cookie.hfix (wA p m U n A) u := rfl
  rw [hfun]
  exact Finset.measurable_sum _ fun u _ => measurable_hfix_wA_posFilt p m n A u

/-- `H^w` at a *fixed* integer site is measurable in the position filtration. -/
theorem measurable_HA_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (x : ℤ) :
    Measurable[posFilt N p m n] (fun U : Array N => HA p m U n A x) := by
  have hfun : (fun U : Array N => HA p m U n A x)
      = fun U => if x < 0 then (x : ℝ) else Cookie.Hfix (wA p m U n A) x.toNat := by
    funext U
    rw [HA, SepGroup.HZ]
  rw [hfun]
  by_cases hx : x < 0
  · simp only [if_pos hx]; exact measurable_const_posFilt p m n (x : ℝ)
  · simp only [if_neg hx]
    exact measurable_Hfix_wA_posFilt p m n A x.toNat

/-! ### The potential at a random integer site -/

/-- `hfix w y.toNat` as a sum over `0 … n` that selects the term `y.toNat`. -/
theorem hfix_eq_sum_ite_int {w : ℕ → ℝ} {y : ℤ} {n : ℕ} (h0 : 0 ≤ y) (hn : y ≤ (n : ℤ)) :
    Cookie.hfix w y.toNat
      = ∑ u ∈ Finset.range (n + 1), (if y = (u : ℤ) then Cookie.hfix w u else (0 : ℝ)) := by
  have hmem : y.toNat ∈ Finset.range (n + 1) := by
    simp only [Finset.mem_range]
    omega
  have hsingle : (∑ u ∈ Finset.range (n + 1),
      (if y = (u : ℤ) then Cookie.hfix w u else (0 : ℝ)))
      = (if y = ((y.toNat : ℕ) : ℤ) then Cookie.hfix w y.toNat else (0 : ℝ)) :=
    Finset.sum_eq_single y.toNat
      (fun u _ hu => if_neg (fun h => hu (by rw [h, Int.toNat_natCast])))
      (fun h => absurd hmem h)
  rw [hsingle, if_pos (by omega)]

/-- Measurability of the potential jump step `hZpot (hfix (wA ·))` at a random site `Y`
bounded by `M` in absolute value. -/
theorem measurable_hZpot_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N))
    {Y : Array N → ℤ} (hY : Measurable[posFilt N p m n] Y) (M : ℕ)
    (hYb : ∀ U, |Y U| ≤ (M : ℤ)) :
    Measurable[posFilt N p m n]
      (fun U : Array N => Swarming.Enl.hZpot (hA p m U n A) (Y U)) := by
  have hfun : (fun U : Array N => Swarming.Enl.hZpot (hA p m U n A) (Y U))
      = fun U => if Y U ≤ -1 then (1 : ℝ) else
          ∑ u ∈ Finset.range (M + 1),
            (if Y U = (u : ℤ) then Cookie.hfix (wA p m U n A) u else (0 : ℝ)) := by
    funext U
    by_cases h : Y U ≤ -1
    · simp only [Swarming.Enl.hZpot, h, if_true]
    · have h0 : (0 : ℤ) ≤ Y U := by omega
      have hn : Y U ≤ (M : ℤ) := (abs_le.mp (hYb U)).2
      simp only [Swarming.Enl.hZpot, h, if_false]
      exact hfix_eq_sum_ite_int h0 hn
  rw [hfun]
  refine Measurable.ite ?_ (measurable_const_posFilt p m n 1) ?_
  · exact measurableSet_le hY (measurable_const_posFilt_int p m n (-1))
  · refine Finset.measurable_sum _ fun u _ => ?_
    refine Measurable.ite (hY (measurableSet_singleton _)) ?_
      (measurable_const_posFilt p m n 0)
    exact measurable_hfix_wA_posFilt p m n A u

/-- The actual position is bounded by the time. -/
theorem abs_X_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    |X p m U n i| ≤ (n : ℤ) := by
  have h : ∀ n : ℕ, -(n : ℤ) ≤ X p m U n i ∧ X p m U n i ≤ (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [X]
    | succ k ih =>
        obtain ⟨h1, h2⟩ := ih
        rcases Swarming.StepCross.pos_succ_eq_or p m U k i with hs | hs
        · have : X p m U (k + 1) i = X p m U k i + 1 := hs
          omega
        · have : X p m U (k + 1) i = X p m U k i - 1 := hs
          omega
  exact abs_le.mpr (h n)

/-- `posFilt`-measurability of the potential jump step at the actual position. -/
theorem measurable_hZpot_X_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (i : Fin N) :
    Measurable[posFilt N p m n]
      (fun U : Array N => Swarming.Enl.hZpot (hA p m U n A) (X p m U n i)) :=
  measurable_hZpot_posFilt p m n A (measurable_pos_posFilt p m i le_rfl) n
    (fun U => abs_X_le p m U n i)

/-- `posFilt`-measurability of the potential jump step one site below the actual position. -/
theorem measurable_hZpot_Xsub1_posFilt (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N))
    (i : Fin N) :
    Measurable[posFilt N p m n]
      (fun U : Array N => Swarming.Enl.hZpot (hA p m U n A) (X p m U n i - 1)) := by
  have hY : Measurable[posFilt N p m n]
      (fun U : Array N => X p m U n i - 1) :=
    (measurable_pos_posFilt p m i le_rfl).sub measurable_const
  refine measurable_hZpot_posFilt p m n A hY (n + 1) ?_
  intro U
  have h := abs_X_le p m U n i
  rw [abs_le] at h ⊢
  omega

end SwarmM3
