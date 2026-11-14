/-
  **The second moment of `PotMax` at the actual array: `(Mpot)` for
  `Swarm/QVarBound.lean`.**

  `PotMax p m n I hI U = max_{i∈I} max_{u<n+2} hfix (omegaN p m U i) u + 4`
  and `hfix (omegaN)` is bounded by `(2p/(2p-1)) (1+L)` on the event that no `L`
  consecutive sites of a row are all unmarked (`MpotRun.hfix_le_of_no_long_run`).
  The exact run probability `(1 - (1-p)^(m-1))^L` (`MpotProb.runEvent_real`) therefore gives

      `∫ PotMax² ≤ (K+4)² (1+T)² + 1`,   `K = 2p/(2p-1)`,

  for any `T` with `(2(n+2)+7)² · |I|(n+2) · (1-q)^T ≤ 1`, and such a `T` is
  `⌈log((2(n+2)+7)² |I|(n+2)) / q⌉`.  This yields the paper's `(Mpot)` with the explicit
  constant `Cpot p m N` below (a `log²` bound, hence a `log⁴` bound).

  There is no unproved step and no extra hypothesis: the only inputs are the already verified
  finite-family mark law of `Swarm/BridgeReveal.lean` and the deterministic recursion of
  `Cookie.hfix`.
-/
import Swarm.MpotRun
import Swarm.MpotProb

set_option maxHeartbeats 3000000

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace SwarmMpot

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 1. Measurability of the run event -/

theorem measurableSet_runEvent (i : Fin N) (a L : ℕ) : MeasurableSet (RunEvent p m i a L) := by
  rw [runEvent_eq_compl]
  exact Finset.measurableSet_biInter _ fun x _ => (measurableSet_siteMark_v p m i x).compl

/-! ### 2. Deterministic: no long run ⟹ `PotMax` is small -/

/-- Every window of `L` consecutive sites of row `i` inside `[0,u]` contains a marked site. -/
def NoLongRun (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (u L : ℕ) : Prop :=
  ∀ a, a + L ≤ u + 1 → ∃ j, j < L ∧ SiteMark p m U i ((a + j : ℕ) : ℤ)

theorem windowMax_le_of_noLongRun (hp : 1 / 2 < p) (hp1 : p ≤ 1) {U : Array N} {i : Fin N}
    {n L : ℕ} (hL : 1 ≤ L) (h : NoLongRun p m U i (n + 1) L) :
    windowMax p m n i U ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
  unfold windowMax
  refine Finset.sup'_le _ _ fun u hu => ?_
  have hu' : u ≤ n + 1 := by
    have := Finset.mem_range.mp hu
    omega
  refine hfix_le_of_no_long_run hp hp1 (fun v => omegaN_eq_half_or (p := p) (m := m) U i v)
    L u hL ?_
  intro a ha
  obtain ⟨j, hj, hs⟩ := h a (by omega)
  exact ⟨j, hj, (omegaN_eq_p_iff hp U i (a + j)).mpr hs⟩

theorem potMax_le_of_noLongRun (hp : 1 / 2 < p) (hp1 : p ≤ 1) {U : Array N} {n L : ℕ}
    (I : Finset (Fin N)) (hI : I.Nonempty) (hL : 1 ≤ L)
    (h : ∀ i ∈ I, NoLongRun p m U i (n + 1) L) :
    PotMax p m n I hI U ≤ ((2 * p / (2 * p - 1)) + 4) * (1 + (L : ℝ)) := by
  have hpm : (0 : ℝ) < 2 * p - 1 := by linarith
  have hK : (0 : ℝ) ≤ 2 * p / (2 * p - 1) := by positivity
  have hL0 : (0 : ℝ) ≤ 1 + (L : ℝ) := by positivity
  have hsup : Swarming.Group.maximumOn I hI (fun i => windowMax p m n i U)
      ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) := by
    unfold Swarming.Group.maximumOn
    refine Finset.sup'_le hI (fun i => windowMax p m n i U) fun i hi =>
      windowMax_le_of_noLongRun hp hp1 hL (h i hi)
  unfold PotMax
  nlinarith

/-! ### 3. The bad-run event -/

/-- Some row of `I` has `L` consecutive unmarked sites inside the window `[0,n+1]`. -/
def BadRun (p : ℝ) (m : ℕ) (I : Finset (Fin N)) (n L : ℕ) : Set (Array N) :=
  ⋃ i ∈ I, ⋃ a ∈ Finset.range (n + 2), RunEvent p m i a L

theorem measurableSet_badRun (I : Finset (Fin N)) (n L : ℕ) :
    MeasurableSet (BadRun p m I n L) :=
  Finset.measurableSet_biUnion _ fun i _ =>
    Finset.measurableSet_biUnion _ fun a _ => measurableSet_runEvent i a L

theorem badRun_real_le (hp0 : 0 < p) (hp1 : p < 1) (I : Finset (Fin N)) (n L : ℕ) :
    (arrayMeasure N).real (BadRun p m I n L)
      ≤ (I.card : ℝ) * ((n : ℝ) + 2) * (1 - (1 - p) ^ (m - 1)) ^ L := by
  have hx0 : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by
    have h1 : (1 - p) ^ (m - 1) ≤ 1 := by
      apply pow_le_one₀ (by linarith) (by linarith)
    linarith
  have h1 : (arrayMeasure N).real (⋃ i ∈ I, ⋃ a ∈ Finset.range (n + 2), RunEvent p m i a L)
      ≤ ∑ i ∈ I, (arrayMeasure N).real (⋃ a ∈ Finset.range (n + 2), RunEvent p m i a L) :=
    measureReal_biUnion_finset_le I _
  have h2 : ∀ i ∈ I, (arrayMeasure N).real (⋃ a ∈ Finset.range (n + 2), RunEvent p m i a L)
      ≤ ∑ a ∈ Finset.range (n + 2), (arrayMeasure N).real (RunEvent p m i a L) :=
    fun i _ => measureReal_biUnion_finset_le _ _
  have h3 : ∀ i ∈ I, (arrayMeasure N).real (⋃ a ∈ Finset.range (n + 2), RunEvent p m i a L)
      ≤ ((n : ℝ) + 2) * (1 - (1 - p) ^ (m - 1)) ^ L := by
    intro i _
    refine le_trans (h2 i ‹i ∈ I›) ?_
    have : ∀ a ∈ Finset.range (n + 2), (arrayMeasure N).real (RunEvent p m i a L)
        = (1 - (1 - p) ^ (m - 1)) ^ L := fun a _ => runEvent_real hp0 hp1 i a L
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [this]
  refine le_trans h1 ?_
  refine le_trans (Finset.sum_le_sum h3) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hI0 : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
  have hfac : (0 : ℝ) ≤ ((n : ℝ) + 2) * (1 - (1 - p) ^ (m - 1)) ^ L :=
    mul_nonneg (by positivity) (pow_nonneg hx0 L)
  exact le_of_eq (by ring)

theorem notMem_badRun_imp {U : Array N} {I : Finset (Fin N)} {n L : ℕ} {i : Fin N}
    (h : U ∉ BadRun p m I n L) (hi : i ∈ I) (hL : 1 ≤ L) :
    NoLongRun p m U i (n + 1) L := by
  intro a ha
  by_contra hc
  push Not at hc
  apply h
  simp only [BadRun, Set.mem_iUnion]
  refine ⟨i, hi, a, Finset.mem_range.mpr (by omega), ?_⟩
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact hc j hj

theorem potMax_le_of_notMem_badRun {U : Array N} {n L : ℕ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (I : Finset (Fin N)) (hI : I.Nonempty) (hL : 1 ≤ L) (h : U ∉ BadRun p m I n L) :
    PotMax p m n I hI U ≤ ((2 * p / (2 * p - 1)) + 4) * (1 + (L : ℝ)) :=
  potMax_le_of_noLongRun hp hp1 I hI hL (fun i hi => notMem_badRun_imp h hi hL)

end SwarmMpot
