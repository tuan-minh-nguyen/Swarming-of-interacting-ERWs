/-
# Simultaneous `(locgroup)` on the actual record window

This file instantiates the windowed `(locgroup)` martingale of `WinTrunc` at the paper's record
window and discharges its inputs by measured events of the actual model:

* `LocMaxBad` — the `(locmax)` event of display `(locmax)` on the record window
  `[r-((T+2)L+2), r+(T+2)L]`, whose measure is at most `exp(-c L^{1/16})` by
  `WideRepair.array_locmax_hG_wide_T` (the accepted `(locmax)` bound, read at the record scale);
* `RecHyp` — the paper's `{d_r ≤ L}` at the record time `n0`, together with the unit-step
  geometry (`WinTrunc.RecHyp_runMax_bounds`, `RecHyp_pos_ge`) that confines every record and every
  position to `[r-(T+1)L, r+TL]` throughout `[n0, n0+TL]`;
* the a.e. convergence of the forward potential `G` (`ae_bddAbove_Gtrunc_arrayMeasure`, transferred
  from the mark layer along `SwarmLogRatio.measurePreserving_siteMarks`), which is what turns the
  `(locmax)` bound on the *supremum* `Gsup` into a bound on the finite truncation `Gtail` used by
  the predictable envelope.

The conclusion is the paper's display `(locgroup)` **simultaneously for every sub-window**
`n0 ≤ s ≤ t ≤ n0+TL` on which `(sep)` holds, off a set of measure at most
`C_T exp(-c_T L^{1/16})`, with the display constant `1` (the paper asks for `C_T`).
-/
import Swarm.WinTrunc
import Swarm.WideLocMaxG
import Swarm.SpatialG
import Swarm.LocMaxWindow

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1

namespace LocGroupSimul

variable {N : ℕ}

/-! ## 1. The `(locmax)` event of the record window -/

/-- The `(locmax)` window event of the record scale: some walker's forward potential `h_j` or `G_j`
exceeds `L^{1/16}` somewhere in the record window `[r-((T+2)L+2), r+TL+2)`. -/
def LocMaxBad (p : ℝ) (m : ℕ) (r T L : ℕ) : Set (Array N) :=
  {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)),
    xOf L ≤ hof p (siteMarks p m U j) y ∨ xOf L ≤ Gsup p (siteMarks p m U j) y}

/-- **The measured `(locmax)` bound at the record window.** -/
theorem exists_locMaxBad_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (r : ℕ), (T + 3) * L ≤ r →
      (arrayMeasure N) (LocMaxBad (N := N) p m r T L)
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨c, hc, L₀, h⟩ := WideRepair.array_locmax_hG_wide_T (N := N) hp0 hp1 hm T hT
  refine ⟨c, hc, max L₀ 2, ?_⟩
  intro L hL r hr
  have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  refine h L hL₀ r ((T + 2) * L + 2) (T * L + 2) ?_ ?_
  · -- (T+2)L + 2 ≤ r
    have h1 : (T + 2) * L + 2 ≤ (T + 3) * L := by
      have : (T + 3) * L = (T + 2) * L + L := by ring
      omega
    omega
  · -- (T+2)L + 2 + (T L + 2) ≤ (2T+4) L
    have h2 : ((T + 2) * L + 2) + (T * L + 2) = (2 * T + 2) * L + 4 := by ring
    have h3 : (2 * T + 2) * L + 4 ≤ (2 * T + 4) * L := by
      have h4 : (2 * T + 4) * L = (2 * T + 2) * L + 2 * L := by ring
      omega
    omega

/-! ## 2. Almost-sure convergence of the forward potential, for the array measure -/

/-- **`BddAbove` of the forward-potential truncations, a.e. for `arrayMeasure`.**  This is the mark
layer's `SwarmMarks.bddAbove_range_Gtrunc_ae` transported along
`SwarmLogRatio.measurePreserving_siteMarks` for each walker.

It is a genuine extra input of `(locgroup)`: the measured `(locmax)` bound controls the *supremum*
`Gsup`, and `Gsup ≤ C` alone does not give `BddAbove` for the truncation series. -/
theorem ae_bddAbove_Gtrunc_arrayMeasure {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n => Gtrunc p (siteMarks p m U j) n (u + 1)) := by
  have hp0' : 0 < p := by linarith
  set q : ℝ := (1 - p) ^ (m - 1) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq]
    have h := pow_one_sub_le_half hp0 hp1 hm
    linarith
  obtain ⟨θ, hθ, hθlt⟩ := SwarmMarks.exists_theta_paper hp0 hp1 hm
  set γ : ℝ := ((1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) + 1) / 2 with hγ
  have hγpos : 0 < γ := by
    rw [hγ]
    have h1 : 0 ≤ (1 - q) * Real.exp (2 * θ) := by
      have : (0:ℝ) ≤ 1 - q := by linarith
      exact mul_nonneg this (Real.exp_pos _).le
    have h2 : 0 ≤ q * ((1 - p) / p) * Real.exp (θ / p) := by
      have hp1' : (0:ℝ) < p := by linarith
      have h3 : 0 ≤ (1 - p) / p := div_nonneg (by linarith) hp1'.le
      exact mul_nonneg (mul_nonneg hq0.le h3) (Real.exp_pos _).le
    linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  have hγineq : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ := by
    rw [hγ]; linarith
  have hrow : ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n => Gtrunc p (siteMarks p m U j) n (u + 1)) := by
    refine ae_all_iff.mpr (fun j => ?_)
    have hmp := SwarmLogRatio.measurePreserving_siteMarks (N := N) hp0' hp1 m j
    have hae := SwarmMarks.bddAbove_range_Gtrunc_ae (p := p) (q := q) hp0 hp1 hq0.le hq1 hθ hγpos hγ1 hγineq
    exact hmp.quasiMeasurePreserving.ae hae
  exact hrow

/-! ## 3. The bridge: `(locmax)` + record geometry give the windowed truncation event -/

/-- The ℤ-value of the level-window left edge `A = r - ((T+2)L+1)`. -/
theorem cast_A {r T L : ℕ} (h : (T + 2) * L + 1 ≤ r) :
    (((r - ((T + 2) * L + 1) : ℕ)) : ℤ) = (r : ℤ) - (((T + 2) * L + 1 : ℕ) : ℤ) :=
  Nat.cast_sub h

/-- **The windowed truncation event at a time of the record window.**  On the record hypothesis,
off the `(locmax)` event, with the forward potential convergent, at a time `n ∈ [n0, n0+TL]` at
which `(sep)` holds, the windowed good event holds at level `B = 2 L^{1/16} + 6`, together with the
predictable position condition at `A = r-(T+2)L-1` that makes the windowed one-step envelope
valid. -/
theorem winTrunc_of_record {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {r T L n0 n : ℕ} (hT : 1 ≤ T) (hL : 2 ≤ L) (hr : (T + 3) * L ≤ r)
    (hn0 : n0 ≤ n) (hnT : n ≤ n0 + T * L)
    {U : Array N} (hrec : RecHyp p m r n0 L U)
    (hlm : U ∉ LocMaxBad (N := N) p m r T L)
    (hbd : ∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))
    (hsep : SepSet p m n I J U) :
    winTrunc (N := N) p m n I J hI (max (2 * xOf L + 6) (2 * (xOf L + 1)))
      (r - ((T + 2) * L + 1)) U := by
  set A : ℕ := r - ((T + 2) * L + 1) with hAdef
  set H : ℝ := xOf L with hHdef
  have hL1 : 1 ≤ L := by omega
  have hH1 : 1 ≤ H := by rw [hHdef]; exact LocSumAct.one_le_xOf hL1
  -- elementary arithmetic of the record window
  have hA1 : ((T + 1) * L : ℕ) ≤ ((T + 2) * L : ℕ) := Nat.mul_le_mul_right L (by omega)
  have hA2 : ((T + 2) * L : ℕ) + 1 ≤ r := by
    have h1 : (T + 2) * L + 1 ≤ (T + 3) * L := by
      have h2 : (T + 2) * L + 1 ≤ (T + 2) * L + L := by omega
      have h3 : (T + 2) * L + L = (T + 3) * L := by ring
      omega
    omega
  have hA3 : ((T + 1) * L : ℕ) ≤ r := by omega
  have hAc : (A : ℤ) = (r : ℤ) - (((T + 2) * L + 1 : ℕ) : ℤ) := by
    rw [hAdef]; exact cast_A hA2
  have hTLc : (((T + 2) * L + 1 : ℕ) : ℤ) = ((T + 2) * L : ℕ) + 1 := by push_cast; ring
  have hAeq : (A : ℤ) + 1 = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) := by
    rw [hAc, hTLc]; ring
  have hA0 : (0 : ℤ) ≤ (A : ℤ) := by
    rw [hAc]; have : (((T + 2) * L + 1 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hA2
    linarith
  -- the (locmax) information on the record window
  have hloc : ∀ j : Fin N, ∀ y ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)),
      hof p (siteMarks p m U j) y ≤ H ∧ Gsup p (siteMarks p m U j) y ≤ H := by
    intro j y hy
    constructor
    · have hnot : ¬ (xOf L ≤ hof p (siteMarks p m U j) y) := fun hc => hlm ⟨j, y, hy, Or.inl hc⟩
      rw [hHdef]; exact le_of_lt (lt_of_not_ge hnot)
    · have hnot : ¬ (xOf L ≤ Gsup p (siteMarks p m U j) y) := fun hc => hlm ⟨j, y, hy, Or.inr hc⟩
      rw [hHdef]; exact le_of_lt (lt_of_not_ge hnot)
  -- containment
  have hbounds := RecHyp_runMax_bounds (p := p) (m := m) (T := T) hrec hn0 hnT
  have hpos := RecHyp_pos_ge (p := p) (m := m) (T := T) hrec hn0 hnT
  have hposA : ∀ k : Fin N, (A : ℤ) + 1 ≤ (trajectory p m U n).pos k := by
    intro k
    have h1 := hpos k
    have h2 : (((T + 1) * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by exact_mod_cast hA1
    rw [hAeq]; linarith
  have hposn1 : ∀ k : Fin N, A + 1 ≤ (X p m U n k).toNat := by
    intro k
    have h1 := hposA k
    have h2 : (0 : ℤ) ≤ (trajectory p m U n).pos k := by linarith
    have h3 : ((trajectory p m U n).pos k).toNat = ((X p m U n k).toNat) := rfl
    have h4 : ((A : ℤ) + 1) ≤ (((trajectory p m U n).pos k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h2]; exact h1
    rw [h3] at h4
    exact_mod_cast h4
  have hApos : ∀ i ∈ I, A ≤ (runMax p m U i n).toNat := by
    intro i hi
    have h1 : (trajectory p m U n).pos i ≤ runMax p m U i n :=
      Swarming.Trajectory.le_runMax p m U i n
    have h2 : (0 : ℤ) ≤ runMax p m U i n := by linarith [hposA i]
    have h3 : ((runMax p m U i n).toNat : ℤ) = runMax p m U i n := Int.toNat_of_nonneg h2
    have h4 : (A : ℤ) ≤ ((runMax p m U i n).toNat : ℤ) := by rw [h3]; linarith [hposA i]
    exact_mod_cast h4
  have hcover : ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n (I ∪ J) (Finset.Nonempty.mono (Finset.subset_union_left) hI) U →
      v ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)) := by
    intro v hv1 hv2
    have hK : (I ∪ J).Nonempty := Finset.Nonempty.mono (Finset.subset_union_left) hI
    have h2 : ((T + 2) * L : ℕ) + 2 ≤ r := by
      have h1 : (T + 2) * L + 2 ≤ (T + 3) * L := by
        have h2' : (T + 2) * L + 2 ≤ (T + 2) * L + L := by omega
        have h3' : (T + 2) * L + L = (T + 3) * L := by ring
        omega
      omega
    have h3 : A - 1 = r - ((T + 2) * L + 2) := by rw [hAdef]; omega
    have hlow : r - ((T + 2) * L + 2) ≤ v := by omega
    have hxTop : xTop p m n (I ∪ J) hK U ≤ r + T * L + 1 := by
      have h1 : xTop p m n (I ∪ J) hK U ≤ Rmax p m n (I ∪ J) hK U + 1 := by
        rw [xTop]; exact min_le_right _ _
      have hRmaxZ : RmaxZ p m n (I ∪ J) hK U ≤ ((r + T * L : ℕ) : ℤ) := by
        refine Finset.sup'_le _ _ fun k hk => ?_
        exact (hbounds k).2
      have hRmax : Rmax p m n (I ∪ J) hK U ≤ r + T * L := by
        rw [Rmax]
        exact Int.toNat_le.mpr hRmaxZ
      omega
    have hhigh : v ≤ r + T * L + 1 := le_trans hv2 hxTop
    rw [Finset.mem_Ico]
    constructor
    · exact hlow
    · calc v ≤ r + T * L + 1 := hhigh
        _ < r + T * L + 1 + 1 := Nat.lt_succ_self _
        _ = r + (T * L + 2) := by ring

  -- the `hfix` and `Gtail` bounds on the level window
  have hK : (I ∪ J).Nonempty := Finset.Nonempty.mono (Finset.subset_union_left) hI
  have hcover' : ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n (I ∪ J) hK U →
      v ∈ Finset.Ico (r - ((T + 2) * L + 2)) (r + (T * L + 2)) := hcover
  have hHbound : ∀ i ∈ I, ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n (I ∪ J) hK U →
      hfix (omegaN p m U i) v ≤ H := by
    intro i hi v hv1 hv2
    exact SiteWindow.hfix_of_locmax_window (p := p) (m := m) (n := n) (K := I ∪ J)
      (by linarith : p ≠ 0) hK (U := U) (a := r - ((T + 2) * L + 2)) (b := r + (T * L + 2))
      (x := H) (fun j y hy => (hloc j y hy).1) hcover' i v hv1 hv2
  have hGbound : ∀ i ∈ I, ∀ u : ℕ, A ≤ u → u ≤ xTop p m n (I ∪ J) hK U →
      Gtail p m U i u (n + 2) ≤ 1 + H := by
    intro i hi u hu1 hu2
    have hpne : p ≠ 0 := by linarith
    have h1 : Gtail p m U i u (n + 2) ≤ 1 + Gsup p (siteMarks p m U i) u :=
      SiteWindow.Gtail_le_one_add_Gsup hpne U i u (n + 2) (hbd i u)
    have hmem := hcover' u (by omega) hu2
    have h2 : Gsup p (siteMarks p m U i) u ≤ H := (hloc i u hmem).2
    linarith
  have hgood := SiteWindow.goodWWin_of_locmax (N := N) hp0 hp1 I J hI hJ hid hsep hH1
    (by linarith : (0:ℝ) ≤ 1 + H) hApos hHbound hGbound
  refine ⟨?_, hposn1⟩
  rw [hHdef] at hgood
  rw [hAdef] at hgood
  rw [add_comm (1:ℝ) (xOf L)] at hgood
  exact hgood

/-! ## 4. The absorption lemma -/

theorem exp_one_mul_le_exp (s : ℝ) : Real.exp 1 * s ≤ Real.exp s := by
  have h := Real.add_one_le_exp (s - 1)
  have h1 : Real.exp 1 * Real.exp (s - 1) = Real.exp s := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp 1 * s ≤ Real.exp 1 * Real.exp (s - 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        linarith
    _ = Real.exp s := h1

/-- `u e^{-cu} ≤ 1/(e c)`. -/
theorem mul_exp_neg_le (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : 0 ≤ u) :
    u * Real.exp (-(c * u)) ≤ 1 / (Real.exp 1 * c) := by
  have hden : (0 : ℝ) < Real.exp 1 * c := by positivity
  rw [le_div_iff₀ hden]
  have h1 : Real.exp 1 * (c * u) ≤ Real.exp (c * u) := exp_one_mul_le_exp _
  have h2 : Real.exp 1 * (c * u) * Real.exp (-(c * u)) ≤
      Real.exp (c * u) * Real.exp (-(c * u)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp (c * u) * Real.exp (-(c * u)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have h4 : u * Real.exp (-(c * u)) * (Real.exp 1 * c) =
      Real.exp 1 * (c * u) * Real.exp (-(c * u)) := by ring
  rw [h4]
  linarith [h2, h3.le, h3.ge]

/-- `u⁴ e^{-bu} ≤ (4/(e b))⁴`. -/
theorem pow_four_mul_exp_neg_le (b : ℝ) (hb : 0 < b) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 4 * Real.exp (-(b * u)) ≤ (4 / (Real.exp 1 * b)) ^ 4 := by
  have hb4 : (0 : ℝ) < b / 4 := by linarith
  have hbase : u * Real.exp (-(b / 4 * u)) ≤ 1 / (Real.exp 1 * (b / 4)) :=
    mul_exp_neg_le (b / 4) hb4 u hu
  have hnn : (0 : ℝ) ≤ u * Real.exp (-(b / 4 * u)) :=
    mul_nonneg hu (Real.exp_pos _).le
  have h4 := pow_le_pow_left₀ hnn hbase 4
  have hexp : Real.exp (-(b / 4 * u)) ^ 4 = Real.exp (-(b * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hleft : (u * Real.exp (-(b / 4 * u))) ^ 4 = u ^ 4 * Real.exp (-(b * u)) := by
    rw [mul_pow, hexp]
  have hright : (1 / (Real.exp 1 * (b / 4))) ^ 4 = (4 / (Real.exp 1 * b)) ^ 4 := by
    congr 1
    field_simp
  rwa [hleft, hright] at h4

/-- `L^{1/4}` as a real number. -/
noncomputable def Lq (L : ℕ) : ℝ := (L : ℝ) ^ ((1 : ℝ) / 4)

theorem Lq_nonneg (L : ℕ) : 0 ≤ Lq L := Real.rpow_nonneg (Nat.cast_nonneg L) _

theorem one_le_Lq {L : ℕ} (hL : 1 ≤ L) : 1 ≤ Lq L :=
  Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)

theorem Lq_pow_four {L : ℕ} (hL : 1 ≤ L) : Lq L ^ 4 = (L : ℝ) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h1 : Lq L ^ 4 = Lq L ^ (4 : ℕ) := rfl
  rw [h1, Lq, ← Real.rpow_natCast ((L : ℝ) ^ ((1 : ℝ) / 4)) 4,
    ← Real.rpow_mul hL0.le]
  norm_num

/-- **The absorption**: the Azuma term with a positive `L^{1/4}` exponent and a linear prefactor is
at most a `T`-dependent constant times `exp(-(a/2) L^{1/16})`, i.e. the paper's `C_T e^{-c_T L^{1/16}}`. -/
theorem absorb_le (a : ℝ) (ha : 0 < a) (T : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-a * Lq L)
      ≤ (2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1))
          * Real.exp (-(a / 2) * xOf L) := by
  set u : ℝ := Lq L with hudef
  have hu1 : 1 ≤ u := one_le_Lq hL
  have hu0 : 0 ≤ u := Lq_nonneg L
  have hLq : u ^ 4 = (L : ℝ) := Lq_pow_four hL
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hcpos : (0 : ℝ) < 2 * ((T : ℝ) + 1) := by positivity
  have hexppos : ∀ x : ℝ, (0 : ℝ) < Real.exp x := fun x => Real.exp_pos x
  -- the prefactor
  have hP : 2 * ((T : ℝ) * (L : ℝ) + 1) ≤ 2 * ((T : ℝ) + 1) * (u ^ 4 + 1) := by
    rw [← hLq]
    nlinarith [hu0, hu1, hT0, hL0]
  -- the quartic absorption
  have hQ : (u ^ 4 + 1) * Real.exp (-(a / 2) * u)
      ≤ (4 / (Real.exp 1 * (a / 2))) ^ 4 + 1 := by
    have hquartic : u ^ 4 * Real.exp (-(a / 2) * u) ≤ (4 / (Real.exp 1 * (a / 2))) ^ 4 := by
      have h := pow_four_mul_exp_neg_le (a / 2) (by linarith) u hu0
      rwa [show -(a / 2 * u) = -(a / 2) * u from by ring] at h
    have hexp1 : Real.exp (-(a / 2) * u) ≤ 1 := by
      have h1 : (0 : ℝ) ≤ (a / 2) * u := by
        have : (0:ℝ) ≤ a / 2 := by linarith
        exact mul_nonneg this hu0
      calc Real.exp (-(a / 2) * u) = Real.exp (-((a / 2) * u)) := by
            congr 1; ring
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    have hsplit : (u ^ 4 + 1) * Real.exp (-(a / 2) * u)
        = u ^ 4 * Real.exp (-(a / 2) * u) + Real.exp (-(a / 2) * u) := by ring
    rw [hsplit]; linarith
  -- the exponent comparison `L^{1/4} ≥ L^{1/16}`
  have hR : Real.exp (-(a / 2) * u) ≤ Real.exp (-(a / 2) * xOf L) := by
    apply Real.exp_le_exp.mpr
    have hrpow : xOf L ≤ u := by
      rw [hudef, Lq, LocSumAct.xOf]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL : (1:ℝ) ≤ (L:ℝ)) (by norm_num)
    have ha2 : (0 : ℝ) ≤ a / 2 := by linarith
    nlinarith
  -- assemble
  have hsplit2 : Real.exp (-a * u)
      = Real.exp (-(a / 2) * u) * Real.exp (-(a / 2) * u) := by
    rw [← Real.exp_add]
    have hsum : -(a / 2) * u + -(a / 2) * u = -a * u := by ring
    rw [hsum]
  calc 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-a * u)
      = (2 * ((T : ℝ) * (L : ℝ) + 1)) * (Real.exp (-(a / 2) * u) * Real.exp (-(a / 2) * u)) := by
        rw [hsplit2]
    _ ≤ (2 * ((T : ℝ) + 1) * (u ^ 4 + 1)) * (Real.exp (-(a / 2) * u) * Real.exp (-(a / 2) * u)) := by
        apply mul_le_mul_of_nonneg_right hP
        exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    _ = (2 * ((T : ℝ) + 1)) * ((u ^ 4 + 1) * Real.exp (-(a / 2) * u)) * Real.exp (-(a / 2) * u) := by
        ring
    _ ≤ (2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1))
          * Real.exp (-(a / 2) * xOf L) := by
        have h1 : (2 * ((T : ℝ) + 1)) * ((u ^ 4 + 1) * Real.exp (-(a / 2) * u)) * Real.exp (-(a / 2) * u)
            ≤ (2 * ((T : ℝ) + 1)) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1)
              * Real.exp (-(a / 2) * u) := by
          have h2 := mul_le_mul_of_nonneg_left hQ hcpos.le
          calc (2 * ((T : ℝ) + 1)) * ((u ^ 4 + 1) * Real.exp (-(a / 2) * u)) * Real.exp (-(a / 2) * u)
              = ((2 * ((T : ℝ) + 1)) * ((u ^ 4 + 1) * Real.exp (-(a / 2) * u)))
                  * Real.exp (-(a / 2) * u) := by ring
            _ ≤ ((2 * ((T : ℝ) + 1)) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1))
                  * Real.exp (-(a / 2) * u) :=
                mul_le_mul_of_nonneg_right h2 (hexppos _).le
        have h2 : (0 : ℝ) ≤ 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1) := by positivity
        calc (2 * ((T : ℝ) + 1)) * ((u ^ 4 + 1) * Real.exp (-(a / 2) * u)) * Real.exp (-(a / 2) * u)
            ≤ (2 * ((T : ℝ) + 1)) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1)
              * Real.exp (-(a / 2) * u) := h1
          _ ≤ (2 * ((T : ℝ) + 1)) * ((4 / (Real.exp 1 * (a / 2))) ^ 4 + 1)
              * Real.exp (-(a / 2) * xOf L) :=
              mul_le_mul_of_nonneg_left hR h2


/-! ## 5. The simultaneous `(locgroup)` bound at the paper's record window -/

/-- The coefficient of the `L^{1/4}` exponent of the Azuma term at the record scale. -/
noncomputable def locRate (N T : ℕ) : ℝ := 1 / (16 * (T : ℝ) * (321 * (N : ℝ)) ^ 2)

/-- The `T`-dependent constant `C_T` of the simultaneous `(locgroup)` bound. -/
noncomputable def locConst (N T : ℕ) : ℝ :=
  2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1) + 1

theorem locRate_pos {N T : ℕ} (hN : 1 ≤ N) (hT : 1 ≤ T) : 0 < locRate N T := by
  rw [locRate]
  have h1 : (0:ℝ) < (T:ℝ) := by exact_mod_cast (by omega : 0 < T)
  have h2 : (0:ℝ) < (321 * (N:ℝ)) ^ 2 := by
    have : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    positivity
  positivity

theorem locConst_pos {N T : ℕ} (hN : 1 ≤ N) (hT : 1 ≤ T) : 0 < locConst N T := by
  have ha := locRate_pos hN hT
  have hden : (0:ℝ) < Real.exp 1 * (locRate N T / 2) := by
    have := Real.exp_pos 1
    positivity
  have h1 : (0:ℝ) < (4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1 := by
    have h2 : (0:ℝ) < 4 / (Real.exp 1 * (locRate N T / 2)) := by positivity
    positivity
  have h3 : (0:ℝ) < 2 * ((T:ℝ) + 1) := by
    have : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
    linarith
  rw [locConst]
  nlinarith [mul_pos h3 h1]

/-- **Simultaneous `(locgroup)` at the paper's record window.**

For `1/2 < p < 1`, `2 ≤ m`, disjoint nonempty `I, J` and `T ≥ 1` there are `c_T > 0` and `L₀`
such that for every `L ≥ L₀` and every `r ≥ (T+3)L`, on the actual array measure, the set of
trajectories on which

* the record hypothesis `RecHyp` holds at `n0` (the paper's `{d_r ≤ L}` at the record time),
* the `(locmax)` window event `LocMaxBad` *fails*,
* the forward potential converges at every site (an a.e. condition),
* and yet some window `n0 ≤ s ≤ t ≤ n0+TL` with `(sep)` on `[s,t)` has
  `W_t^{I,J} - W_s^{I,J} > L^{3/4}`,

has measure at most `C_T exp(-c_T L^{1/16})` — i.e. for every such window at once,
`W_t^{I,J} - W_s^{I,J} ≤ L^{3/4}` off that set.  In particular the display `(locgroup)` holds with
the constant `1` (`C_T` in the paper) and every `T`-dependence sits in `c_T`. -/
theorem exists_locgroup_record_window {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hid : Disjoint I J) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (r n0 : ℕ), (T + 3) * L ≤ r →
      (arrayMeasure N).real
        {U : Array N |
          RecHyp p m r n0 L U ∧
          U ∉ LocMaxBad (N := N) p m r T L ∧
          (∀ j : Fin N, ∀ u : ℕ,
            BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
          (∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
            (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
            (L : ℝ) ^ ((3 : ℝ) / 4) < WA p m U t I J hI hJ - WA p m U s I J hI hJ)}
        ≤ locConst N T * Real.exp (-c_T * xOf L) := by
  have hN : 1 ≤ N := by
    obtain ⟨i, hi⟩ := hI
    have := i.isLt
    omega
  obtain ⟨c_lm, hc_lm, L₀_lm, hlm⟩ := exists_locMaxBad_le (N := N) hp0 hp1 hm T hT
  have hapos : 0 < locRate N T := locRate_pos hN hT
  refine ⟨min (locRate N T / 2) c_lm, lt_min (by linarith) hc_lm, max (max L₀_lm 2) 1, ?_⟩
  intro L hLbig r n0 hr
  have hL0 : L₀_lm ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hLbig)
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hLbig)
  have hL1 : 1 ≤ L := by omega
  set Kloc : ℕ := T * L with hKdef
  set ε : ℝ := (L : ℝ) ^ ((3 : ℝ) / 4) with hεdef
  set B : ℝ := max (2 * xOf L + 6) (2 * (xOf L + 1)) with hBdef
  set A : ℕ := r - ((T + 2) * L + 1) with hAdef
  have hxOf : xOf L = (L : ℝ) ^ ((1 : ℝ) / 16) := rfl
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hBtrunc : B = LocScaleArithmetic.truncLevel (L : ℝ) := by
    rw [hBdef, LocScaleArithmetic.truncLevel, hxOf]
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ ((1 : ℝ) / 16) := Real.one_le_rpow hLr (by norm_num)
    have h1 : 2 * (L : ℝ) ^ ((1 : ℝ) / 16) ≤ 2 * (L : ℝ) ^ ((1 : ℝ) / 16) + 6 := by linarith
    have h1' : 2 * ((L : ℝ) ^ ((1 : ℝ) / 16) + 1) ≤ 2 * (L : ℝ) ^ ((1 : ℝ) / 16) + 6 := by linarith
    rw [max_eq_left h1, max_eq_left h1']
  have hBpos : 0 < B := by
    rw [hBtrunc]
    rw [LocScaleArithmetic.truncLevel_eq hLr]
    have h2 : (0 : ℝ) < (L : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hεpos : 0 < ε := by rw [hεdef]; exact Real.rpow_pos_of_pos (by linarith) _
  have hKpos : 1 ≤ Kloc := by
    rw [hKdef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- the maximal-Azuma side condition
  have hside : ε ≤ 4 * (Kloc : ℝ) * LocGroupWindow.stepEnv (N := N) p B := by
    rw [hεdef, hKdef, hBtrunc]
    have hE4 : 4 * (L : ℝ) ^ ((1 : ℝ) / 16)
        ≤ LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L : ℝ)) :=
      LocGroupWindow.truncLevel_le_stepEnv (N := N) hp0 hp1.le hLr
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hr1 : (0 : ℝ) < (L : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : (L : ℝ) ^ ((3 : ℝ) / 4) ≤ (L : ℝ) ^ ((17 : ℝ) / 16) :=
      Real.rpow_le_rpow_of_exponent_le hLr (by norm_num)
    have h3 : (L : ℝ) ^ ((17 : ℝ) / 16) = (L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 16) := by
      rw [show ((17 : ℝ) / 16) = (1 : ℝ) + (1 : ℝ) / 16 by norm_num, Real.rpow_add (by linarith),
        Real.rpow_one]
    have h4 : 16 * ((T : ℝ) * (L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 16))
        ≤ 4 * ((T : ℝ) * (L : ℝ)) * LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L : ℝ)) := by
      have h5 := mul_le_mul_of_nonneg_left hE4 (by positivity : (0:ℝ) ≤ 4 * ((T : ℝ) * (L : ℝ)))
      nlinarith [h5]
    have h6 : (L : ℝ) ^ ((17 : ℝ) / 16) ≤ 16 * ((T : ℝ) * (L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
      rw [h3]
      nlinarith [hT1, hr1, mul_pos (by linarith : (0:ℝ) < (L:ℝ)) hr1]
    have hcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [h2, h6, h4]
  -- the measured deviation bound on the windowed martingale
  have hdev := measure_all_windows_le (N := N) (m := m) hp0 hp1 I J hI hJ hid
    (B := B) (hB := hBpos) (A := A) (n0 := n0) (K := Kloc) (ε := ε) hKpos hεpos hside
  -- the exponent comparison: the Azuma exponent is at most `-locRate * L^{1/4}`
  have hexp : -((ε / 2) ^ 2) / (4 * ((Kloc : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2))
      ≤ -locRate N T * Lq L := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
    have hu : 0 < Lq L := Real.rpow_pos_of_pos hLpos _
    have hu4 : Lq L ^ 4 = (L : ℝ) := Lq_pow_four hL1
    have hu3 : (L : ℝ) ^ ((3 : ℝ) / 4) = Lq L ^ 3 := by
      rw [Lq, ← Real.rpow_natCast ((L : ℝ) ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hLpos.le]
      norm_num
    have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hcast : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
    have hCE : (2 * LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ))) ^ 2
        ≤ (321 * (N : ℝ)) ^ 2 * Lq L := by
      have hC := LocScaleArithmetic.two_envB_truncLevel_le (N := N) hp0 hp1.le hN hLr
      have hE0 : (0 : ℝ) ≤ LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ)) := by
        rw [show LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ))
            = LocScaleArithmetic.envB p N (LocScaleArithmetic.truncLevel (L:ℝ)) from rfl]
        exact LocScaleArithmetic.envB_nonneg hp0 hp1.le (by
          rw [LocScaleArithmetic.truncLevel_eq hLr]
          have h4 : (0:ℝ) < (L:ℝ) ^ ((1:ℝ)/16) := Real.rpow_pos_of_pos hLpos _
          linarith)
      have h1 : 2 * LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ))
          ≤ 321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8) := by
        simp only [LocGroupWindow.stepEnv] at hC ⊢
        linarith
      have hsq : (321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8)) ^ 2
          = (321 * (N : ℝ)) ^ 2 * Lq L := by
        rw [mul_pow, mul_pow, Lq]
        congr 1
        rw [show ((1:ℝ)/4) = (1:ℝ)/8 + (1:ℝ)/8 by norm_num, Real.rpow_add hLpos]
        ring
      calc (2 * LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ))) ^ 2
          ≤ (321 * (N : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := by
            apply pow_le_pow_left₀ (by linarith) h1
        _ = (321 * (N : ℝ)) ^ 2 * Lq L := hsq
    have hgoal : locRate N T * Lq L
        ≤ ((ε / 2) ^ 2) / (4 * ((Kloc : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2)) := by
      rw [hεdef, hKdef, hBtrunc, hcast, hu3, locRate]
      have hE0 : (0:ℝ) < 2 * LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ)) := by
        have h3 : (0:ℝ) < (L:ℝ) ^ ((1:ℝ)/16) := Real.rpow_pos_of_pos hLpos _
        have := LocGroupWindow.stepEnv_pos (N := N) hp0 hp1.le (B := 2 * (L:ℝ)^((1:ℝ)/16) + 6) (by linarith)
        have heq : LocScaleArithmetic.truncLevel (L:ℝ) = 2 * (L:ℝ)^((1:ℝ)/16) + 6 :=
          LocScaleArithmetic.truncLevel_eq hLr
        rw [heq]
        linarith
      field_simp
      have hEsq : (0:ℝ) < LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ)) ^ 2 := by
        have h2 : (0:ℝ) < 2 * LocGroupWindow.stepEnv (N := N) p (LocScaleArithmetic.truncLevel (L:ℝ)) := hE0
        nlinarith
      rw [le_div_iff₀ hEsq]
      nlinarith [hCE, hu, hu4, hLpos, hT0, hN0, hE0]
    rw [neg_div, neg_mul]
    exact neg_le_neg_iff.mpr hgoal

  -- the subset relation
  have hsubset : {U : Array N |
        RecHyp p m r n0 L U ∧
        U ∉ LocMaxBad (N := N) p m r T L ∧
        (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
        (∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
          (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
          ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ)}
      ⊆ {U : Array N |
          ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
            (∀ k, s ≤ k → k < t → winTrunc (N := N) p m k I J hI B A U) ∧
            ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ}
        ∪ LocMaxBad (N := N) p m r T L
        ∪ {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
            BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))} := by
    rintro U ⟨hrec, hlmU, hbdU, s, t, hn0, hst, htK, hsep, hadv⟩
    refine Or.inl (Or.inl ⟨s, t, hn0, hst, htK, ?_, hadv⟩)
    intro k hk hkt
    exact winTrunc_of_record (N := N) hp0 hp1.le I J hI hJ hid hT hL2 hr
      (n := k) (le_trans hn0 hk) (le_trans hkt.le htK) hrec hlmU hbdU (hsep k (Finset.mem_Ico.mpr ⟨hk, hkt⟩))
  -- measures
  have hlm' : (arrayMeasure N).real (LocMaxBad (N := N) p m r T L) ≤ Real.exp (-c_lm * xOf L) := by
    have h := hlm L hL0 r hr
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h) ?_
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hbddz : (arrayMeasure N).real {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))} = 0 := by
    have hae := ae_bddAbove_Gtrunc_arrayMeasure (N := N) hp0 hp1 hm
    have h0 : (arrayMeasure N) {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
        BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))} = 0 :=
      (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae
    rw [measureReal_def, h0]; simp
  have hdev' : (arrayMeasure N).real {U : Array N |
        ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
          (∀ k, s ≤ k → k < t → winTrunc (N := N) p m k I J hI B A U) ∧
          ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ}
      ≤ 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-locRate N T * Lq L) := by
    have hTL : ((Kloc : ℝ) + 1) = (T : ℝ) * (L : ℝ) + 1 := by rw [hKdef]; push_cast; ring
    have h2 : Real.exp (-((ε / 2) ^ 2) / (4 * ((Kloc : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2)))
        ≤ Real.exp (-locRate N T * Lq L) := Real.exp_le_exp.mpr hexp
    have h3 : (0 : ℝ) ≤ 2 * ((Kloc : ℝ) + 1) := by positivity
    have h4 : 2 * ((Kloc : ℝ) + 1)
          * Real.exp (-((ε / 2) ^ 2) / (4 * ((Kloc : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2)))
        ≤ 2 * ((Kloc : ℝ) + 1) * Real.exp (-locRate N T * Lq L) :=
      mul_le_mul_of_nonneg_left h2 h3
    have h5 := le_trans hdev h4
    rw [hTL] at h5
    exact h5

  have hbad_meas : (arrayMeasure N).real {U : Array N |
        RecHyp p m r n0 L U ∧
        U ∉ LocMaxBad (N := N) p m r T L ∧
        (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
        (∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
          (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
          (L : ℝ) ^ ((3 : ℝ) / 4) < WA p m U t I J hI hJ - WA p m U s I J hI hJ)}
      ≤ Real.exp (-c_lm * xOf L) + 0
        + 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-locRate N T * Lq L) := by
    refine le_trans (measureReal_mono hsubset (measure_ne_top _ _)) ?_
    refine le_trans (MeasureTheory.measureReal_union_le (μ := arrayMeasure N) _ _) ?_
    have h2 := MeasureTheory.measureReal_union_le (μ := arrayMeasure N)
      ({U : Array N | ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
          (∀ k, s ≤ k → k < t → winTrunc (N := N) p m k I J hI B A U) ∧
          ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ})
      (LocMaxBad (N := N) p m r T L)
    have h3 : (arrayMeasure N).real
        ({U : Array N | ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + T * L ∧
            (∀ k, s ≤ k → k < t → winTrunc (N := N) p m k I J hI B A U) ∧
            ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ}
          ∪ LocMaxBad (N := N) p m r T L) ≤
        2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-locRate N T * Lq L) + Real.exp (-c_lm * xOf L) := by
      linarith [h2, hdev', hlm']
    linarith [h3, hbddz]
  -- the final constant
  refine le_trans hbad_meas ?_
  have hx0 : (0 : ℝ) ≤ xOf L := le_trans zero_le_one (LocSumAct.one_le_xOf hL1)
  have hmin1 : min (locRate N T / 2) c_lm ≤ c_lm := min_le_right _ _
  have hmin2 : min (locRate N T / 2) c_lm ≤ locRate N T / 2 := min_le_left _ _
  have hA1 : Real.exp (-c_lm * xOf L) ≤ Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hA3 : Real.exp (-(locRate N T / 2) * xOf L) ≤ Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hK0 : (0 : ℝ) ≤ 2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1) := by
    have hd : (0 : ℝ) < Real.exp 1 * (locRate N T / 2) := by
      have h1 := Real.exp_pos 1
      have h2 := locRate_pos hN hT
      positivity
    have h1 : (0 : ℝ) ≤ 4 / (Real.exp 1 * (locRate N T / 2)) := by positivity
    have h2 : (0 : ℝ) ≤ (4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1 := by
      have := pow_nonneg h1 4
      linarith
    have h3 : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
    nlinarith [h2, mul_nonneg h3 h2]
  have hAbs := absorb_le (locRate N T) (locRate_pos hN hT) T hL1
  have hstepA : 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-locRate N T * Lq L)
      ≤ (2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1))
        * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
    refine le_trans hAbs ?_
    exact mul_le_mul_of_nonneg_left hA3 hK0
  calc Real.exp (-c_lm * xOf L) + 0
        + 2 * ((T : ℝ) * (L : ℝ) + 1) * Real.exp (-locRate N T * Lq L)
      ≤ Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) + 0
        + (2 * ((T : ℝ) + 1) * ((4 / (Real.exp 1 * (locRate N T / 2))) ^ 4 + 1))
          * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
        linarith [hA1, hstepA]
    _ = locConst N T * Real.exp (-(min (locRate N T / 2) c_lm) * xOf L) := by
        rw [locConst]; ring

end LocGroupSimul
