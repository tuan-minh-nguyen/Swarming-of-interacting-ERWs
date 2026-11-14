/-## The coarse-scale halving (`HblkCoarse`) does not supply the block estimate `hblk`

`HblkCoarse.coarse_halving_actual` proves, unconditionally at the canonical array, that the
halving clause `(half)` of the paper's block estimate cannot fail at scales `ℓ ≥ θ r`: at a record
time the defect is the spread, `spread(n)/n → 0` and `τ_y ≤ N₀ + (2/κ) y`.  Its stated reading
(`HblkCoarse.badBlk_iff_badTime_coarse_actual`) is that at coarse scales the bad event *is* the
record-advance failure, so that on the diagonal `ℓ ≈ r/(2C₀)` "only `(time)`" is left.

That reading is about the Borel–Cantelli step.  It does **not** produce the input the certificate
argument consumes.  The certificate argument (`SwarmM4.PCtxR.measure_certSet_le`) applies `hblk`

  `μ ({d_r ≤ ℓ} ∩ {¬ Good r ℓ}) ≤ p ℓ`   for **all** `r ≥ C₀ ℓ`

inside a window `r ∈ [u - 4Bℓ, u]` at the *fixed* scale `ℓ`, and sums the resulting weights
`(4Bℓ+1) p ℓ` over `ℓ`.  Most pairs `(r, ℓ)` occurring there have `r ≫ ℓ`, i.e. are *fine*-scale
pairs, where `HblkCoarse` says nothing.  Worse, a coarse-scale almost-sure statement is an
eventual-in-`r` statement and carries no rate, so it cannot be turned into the profile `p` at all.

This file makes that precise, machine-checked, with an explicit model.  There is a probability
space, a defect sequence and a block predicate such that

* the certificate structure `hS` of `PCtxR` holds,
* `hterm` holds,
* the coarse-scale halving holds in the **strongest possible form**: at every `ω` and every level
  `r`, *every* scale `ℓ ≥ r` is a good block (so `HblkCoarse.coarse_halving`-style statements are
  satisfied at every `ω`, not just almost surely),
* the tightness conclusion `∃ K, ∀ u, μ {K < d_u} ≤ ε` holds,

and yet **no** profile `p` satisfies `hblk` together with the certificate summability
`∑_ℓ (4Bℓ+1) p ℓ ≠ ⊤`: at the fine scale `r = C₀ ℓ` the bad event is the whole space, so
`p ℓ ≥ 1` for every `ℓ ≥ 1`.

Hence the fine-scale halving `h₂` is irreducible in the integrated reduction
(`HblkFinal.record_tightness_of_two_actual`): it cannot be replaced by the coarse halving, and it
cannot be dropped in favour of the almost-sure diagonal statement used by the Borel–Cantelli step.
-/
import Swarm.HblkFinal

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace AuditCoarse

/-! ### The model

`Ω = Unit`, `μ = dirac ()`, and the block predicate is `Good r ℓ ↔ r ≤ ℓ`: the block is good
whenever the scale is at least the level.  This is deliberately the *strongest* coarse-scale
halving possible; the defect is identically zero, so the certificate structure and the conclusion
of tightness hold trivially. -/

/-- The defect sequence of the model: identically zero. -/
def d0 : Unit → ℕ → ℕ := fun _ _ => 0

/-- The block predicate of the model: `Good r ℓ ↔ r ≤ ℓ`. -/
def GoodC : Unit → ℕ → ℕ → Prop := fun _ r ℓ => r ≤ ℓ

/-- The probability space of the model. -/
noncomputable def μU : Measure Unit := Measure.dirac ()

theorem μU_univ : μU Set.univ = 1 := by
  haveI : IsProbabilityMeasure (Measure.dirac ()) := Measure.dirac.isProbabilityMeasure
  show (Measure.dirac () : Measure Unit) Set.univ = 1
  exact measure_univ

/-- The certificate structure `hS` of `PCtxR` holds: the defect is identically zero. -/
theorem hS_model (B C₀ : ℕ) :
    ∀ ω r L, GoodC ω r L → d0 ω r ≤ L →
      d0 ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d0 ω u ≤ C₀ * L := by
  intro ω r L _ _
  exact ⟨by simp [d0], fun u _ _ => by simp [d0]⟩

/-- `hterm` holds: every level has arbitrarily large good dyadic blocks. -/
theorem hterm_model (B : ℕ) : ∀ r L : ℕ, 1 ≤ L →
    ∀ᵐ ω ∂μU, ∃ j : ℕ, GoodC ω r (2 ^ j * L) := by
  intro r L hL
  refine Eventually.of_forall fun _ => ⟨r, ?_⟩
  show r ≤ 2 ^ r * L
  have h2 : r ≤ 2 ^ r := by
    induction r with
    | zero => simp
    | succ m ih =>
        have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        rw [pow_succ]
        nlinarith
  calc r ≤ 2 ^ r := h2
    _ ≤ 2 ^ r * L := by nlinarith [Nat.one_le_two_pow (n := r), hL]

/-- **The coarse-scale halving holds at every `ω` and every level**, in the strongest available
form: every scale `ℓ` at least the level is a good block.  No almost-sure qualifier is needed. -/
theorem coarse_model :
    ∀ᵐ ω ∂μU, ∀ᶠ r : ℕ in atTop, ∀ ℓ : ℕ, (r : ℝ) ≤ (ℓ : ℝ) → GoodC ω r ℓ :=
  Eventually.of_forall fun _ => Eventually.of_forall fun r ℓ h => by
    have : r ≤ ℓ := by exact_mod_cast h
    exact this

/-- The tightness conclusion holds in the model. -/
theorem tight_model : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ u : ℕ, μU {ω : Unit | K < d0 ω u} ≤ ε := by
  intro ε _
  exact ⟨0, fun u => by simp [d0]⟩

/-- **No summable certificate profile exists in the model.**  At the fine scale `r = C₀ ℓ` the
bad event `{d_r ≤ ℓ} ∩ {¬ Good r ℓ}` is the whole space, so `p ℓ ≥ 1` for every `ℓ ≥ 1`, and the
certificate weight `(4Bℓ+1) p ℓ` is bounded below by `4Bℓ+1`, whose series diverges. -/
theorem no_summable_profile {B C₀ : ℕ} (hC₀ : 2 ≤ C₀) {p : ℕ → ℝ≥0∞}
    (hp : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      μU ({ω : Unit | d0 ω r ≤ ℓ} ∩ {ω : Unit | ¬ GoodC ω r ℓ}) ≤ p ℓ) :
    (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ) = ⊤ := by
  -- the bad event at the fine scale `r = C₀ ℓ` is the whole space
  have hbad : ∀ ℓ : ℕ, 1 ≤ ℓ →
      ({ω : Unit | d0 ω (C₀ * ℓ) ≤ ℓ} ∩ {ω : Unit | ¬ GoodC ω (C₀ * ℓ) ℓ}) = Set.univ := by
    intro ℓ hℓ
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨by simp [d0], ?_⟩
    simp only [GoodC, not_le]
    have : C₀ * ℓ ≥ 2 * ℓ := Nat.mul_le_mul_right ℓ hC₀
    omega
  have hone : ∀ ℓ : ℕ, 1 ≤ ℓ → 1 ≤ p ℓ := by
    intro ℓ hℓ
    have h := hp ℓ hℓ (C₀ * ℓ) le_rfl
    rw [hbad ℓ hℓ, μU_univ] at h
    exact h
  -- the certificate weight dominates `1` termwise on `ℓ ≥ 1`
  rw [ENNReal.tsum_eq_iSup_sum]
  refine top_unique ?_
  rw [← ENNReal.iSup_natCast]
  refine iSup_le fun N => ?_
  refine le_trans (b := ∑ ℓ ∈ Finset.Icc 1 N, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ) ?_
    (le_iSup (fun s : Finset ℕ => ∑ ℓ ∈ s, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ)
      (Finset.Icc 1 N))
  calc (N : ℝ≥0∞) = ∑ ℓ ∈ Finset.Icc 1 N, (1 : ℝ≥0∞) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp
    _ ≤ ∑ ℓ ∈ Finset.Icc 1 N, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.1 hℓ).1
        refine one_le_mul_of_one_le_of_one_le ?_ (hone ℓ hℓ1)
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le (4 * B * ℓ))

end AuditCoarse
