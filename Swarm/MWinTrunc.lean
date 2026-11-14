/-
# The windowed `(locmove)` defect: `dQTW = dQ` on `winTrunc` windows

`LocMoveCompose.gamma_half_pointwise` is the `Γ`-drift half of display `(locmove)`.  Its only use
of the *prefix* envelope `LocGroupQ.GoodW` is `LocGroupWindow.ae_psum_dQT_eq_Q_sub`: on a window
where `GoodW` holds at every time, the `GoodW`-truncated martingale sum equals the paper's defect
`Q_t - Q_s`.  `PrefixObstruction` shows `GoodW` is not a function of the `(locmax)` window, so that
step cannot be used on the record window.

`WinTrunc` supplies the repair on the martingale side: the *windowed* truncation event

  `winTrunc p m n I J hI B A  =  SiteWindow.GoodWWin … B A  ∧  (∀ k, A+1 ≤ X_n^k)`

(a `posFilt n`-measurable event contained in `(sep)`), its truncated increment `incTW`, the
centred `dQTW`, the drift `(Wdrift)` (`condExp_incTW_nonpos`), the envelope `2·stepEnv p B`
(`ae_abs_dQTW_le`), the telescope (`ae_telescope_winTrunc`) and the maximal deviation bound
(`measure_deviation_dQTW_le`).

What `WinTrunc` does **not** contain — and what this file supplies — is the identification

  `Q_t - Q_s = Σ_{k ∈ [s,t)} dQTW_k`  on `winTrunc` windows,

i.e. the windowed counterpart of `ae_psum_dQT_eq_Q_sub`.  The mechanism is exactly the same one
`ae_dQT_eq_dQ_of_goodW` uses: `winTrunc ⊆ (sep)`, so `incTW` and the paper's `Qraw` agree on
`winTrunc`; the two `posFilt`-indicators then have equal conditional expectations on `winTrunc`,
so the compensators agree there and the centred increments coincide.

This is the missing input for `locmove_ae_win` (`MWinMove.lean`): with it, the `Γ`-drift half of
`(locmove)` — whose mean-`(loccoord)` term is `ae_window_gamma_drift_le`, a statement that never
uses `GoodW` — can be closed against the *windowed* martingale deviation instead of the prefix one.

No proof holes, no new axiom, no stochastic hypothesis: the only inputs are the public windowed
truncation and the public `(Wdrift)`.
-/
import Swarm.WinTrunc
import Swarm.LocMoveCompose
import Swarm.LocMoveLocalProfile

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow LocGroupSimul
open LocMoveMart LocMoveLocal LocMoveCompose

namespace MWin

variable {N : ℕ}

/-! ## 1. `incTW` is the paper's `Qraw` on the truncation event -/

/-- On the windowed truncation event the truncated increment *is* the paper's raw `(sep)`-increment
`Qraw` (they differ only by the indicator event, and `winTrunc ⊆ (sep)`). -/
theorem incTW_eq_Qraw_of_winTrunc {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty}
    {hJ : J.Nonempty} {B : ℝ} {A : ℕ} {U : Array N}
    (hU : LocGroupSimul.winTrunc p m n I J hI B A U) :
    LocGroupSimul.incTW p m n I J hI hJ B A U = Qraw p m I J hI hJ n U := by
  rw [LocGroupSimul.incTW_of_mem (hJ := hJ) (U := U) (n := n)
      (show U ∈ {U : Array N | LocGroupSimul.winTrunc p m n I J hI B A U} from hU),
    Qraw, Set.indicator_of_mem (show U ∈ {U : Array N | SepSet p m n I J U} from
      LocGroupSimul.winTrunc_sep hU)]

/-! ## 2. The centred windowed increment is the paper's `dQ` on the truncation event -/

/-- **`dQTW = dQ` on the windowed truncation event**, almost surely in the path.  This is
`LocGroupWindow.ae_dQT_eq_dQ_of_goodW` with `winTrunc` in place of `GoodW`: the truncation event is
`posFilt n`-measurable and contained in `(sep)`, which is all that proof uses. -/
theorem ae_dQTW_eq_dQ_of_winTrunc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m k : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) (A : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), LocGroupSimul.winTrunc p m k I J hI B A U →
      LocGroupSimul.dQTW p m k I J hI hJ B A U = dQ p m I J hI hJ k U := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp : (1 : ℝ) / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  set G : Set (Array N) := {U : Array N | LocGroupSimul.winTrunc p m k I J hI B A U} with hGdef
  have hGm : MeasurableSet[posFilt N p m k] G := LocGroupSimul.measurableSet_winTrunc p m k I J hI B A
  have hQint : Integrable (Qraw p m I J hI hJ k) (arrayMeasure N) :=
    integrable_Qraw hp hp1' m k I J hI hJ
  have hTint : Integrable (LocGroupSimul.incTW p m k I J hI hJ B A) (arrayMeasure N) :=
    LocGroupSimul.integrable_incTW (N := N) hp hp1' m k I J hI hJ B A
  have hindQ : Integrable (G.indicator (Qraw p m I J hI hJ k)) (arrayMeasure N) :=
    hQint.indicator (((posFilt N p m).le k) _ hGm)
  have hindT : Integrable (G.indicator (LocGroupSimul.incTW p m k I J hI hJ B A))
      (arrayMeasure N) :=
    hTint.indicator (((posFilt N p m).le k) _ hGm)
  have hmulQ : (G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k
      = G.indicator (Qraw p m I J hI hJ k) := by
    funext U
    by_cases hU : U ∈ G <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hU]
  have hmulT : (G.indicator (fun _ : Array N => (1 : ℝ)))
        * LocGroupSimul.incTW p m k I J hI hJ B A
      = G.indicator (LocGroupSimul.incTW p m k I J hI hJ B A) := by
    funext U
    by_cases hU : U ∈ G <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hU]
  have hfmeas : StronglyMeasurable[posFilt N p m k]
      (G.indicator (fun _ : Array N => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hGm
  have hpullQ := condExp_mul_of_stronglyMeasurable_left (μ := arrayMeasure N)
    (m := posFilt N p m k) (f := G.indicator (fun _ : Array N => (1 : ℝ)))
    (g := Qraw p m I J hI hJ k) hfmeas (by rw [hmulQ]; exact hindQ) hQint
  have hpullT := condExp_mul_of_stronglyMeasurable_left (μ := arrayMeasure N)
    (m := posFilt N p m k) (f := G.indicator (fun _ : Array N => (1 : ℝ)))
    (g := LocGroupSimul.incTW p m k I J hI hJ B A) hfmeas (by rw [hmulT]; exact hindT) hTint
  have hprod : (G.indicator (fun _ : Array N => (1 : ℝ)))
        * LocGroupSimul.incTW p m k I J hI hJ B A
      =ᵐ[arrayMeasure N]
        (G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k := by
    filter_upwards with U
    by_cases hU : U ∈ G
    · have hinc : LocGroupSimul.incTW p m k I J hI hJ B A U = Qraw p m I J hI hJ k U :=
        incTW_eq_Qraw_of_winTrunc hU
      simp only [Pi.mul_apply, Set.indicator_of_mem hU, one_mul, hinc]
    · simp only [Pi.mul_apply, Set.indicator_of_notMem hU, zero_mul]
  have hce : (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ)))
        * LocGroupSimul.incTW p m k I J hI hJ B A | ↑(posFilt N p m k)]
      =ᵐ[arrayMeasure N]
        (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ))) * Qraw p m I J hI hJ k
          | ↑(posFilt N p m k)] :=
    condExp_congr_ae (μ := arrayMeasure N) (m := posFilt N p m k) hprod
  have hcomb : ∀ᵐ U ∂(arrayMeasure N), U ∈ G →
      (arrayMeasure N)[LocGroupSimul.incTW p m k I J hI hJ B A | ↑(posFilt N p m k)] U
        = (arrayMeasure N)[Qraw p m I J hI hJ k | ↑(posFilt N p m k)] U := by
    filter_upwards [hpullT, hpullQ, hce] with U h1 h2 h3 hGU
    have hf1 : (G.indicator (fun _ : Array N => (1 : ℝ))) U = 1 := by
      simp only [Set.indicator_of_mem hGU]
    calc (arrayMeasure N)[LocGroupSimul.incTW p m k I J hI hJ B A | ↑(posFilt N p m k)] U
        = ((G.indicator (fun _ : Array N => (1 : ℝ))) *
            (arrayMeasure N)[LocGroupSimul.incTW p m k I J hI hJ B A | ↑(posFilt N p m k)]) U := by
          simp only [Pi.mul_apply, hf1, one_mul]
      _ = (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ)))
            * LocGroupSimul.incTW p m k I J hI hJ B A | ↑(posFilt N p m k)] U := h1.symm
      _ = (arrayMeasure N)[(G.indicator (fun _ : Array N => (1 : ℝ)))
            * Qraw p m I J hI hJ k | ↑(posFilt N p m k)] U := h3
      _ = ((G.indicator (fun _ : Array N => (1 : ℝ))) *
            (arrayMeasure N)[Qraw p m I J hI hJ k | ↑(posFilt N p m k)]) U := h2
      _ = (arrayMeasure N)[Qraw p m I J hI hJ k | ↑(posFilt N p m k)] U := by
          simp only [Pi.mul_apply, hf1, one_mul]
  filter_upwards [hcomb] with U hU hGU
  have hinc : LocGroupSimul.incTW p m k I J hI hJ B A U = Qraw p m I J hI hJ k U :=
    incTW_eq_Qraw_of_winTrunc hGU
  have hcoeq := hU hGU
  simp only [LocGroupSimul.dQTW, dQ, hinc, hcoeq]

/-! ## 3. The telescoped identity: the paper's defect is the windowed martingale sum -/

/-- **On a `winTrunc` window the windowed truncated sum is the paper's defect `Q_t - Q_s`.**
Almost surely, for all `s ≤ t` and every window on which `winTrunc` holds at every time.  This is
`LocGroupWindow.ae_psum_dQT_eq_Q_sub` with the windowed truncation. -/
theorem ae_psum_dQTW_eq_Q_sub {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) (A : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s t : ℕ, s ≤ t →
      (∀ k, s ≤ k → k < t → LocGroupSimul.winTrunc p m k I J hI B A U) →
      LocMart.psum (fun j => LocGroupSimul.dQTW p m (s + j) I J hI hJ B A) (t - s) U
        = Q p m I J hI hJ t U - Q p m I J hI hJ s U := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ,
      (LocGroupSimul.winTrunc p m k I J hI B A U →
        LocGroupSimul.dQTW p m k I J hI hJ B A U = dQ p m I J hI hJ k U) :=
    ae_all_iff.mpr (fun k => ae_dQTW_eq_dQ_of_winTrunc hp0 hp1 m k I J hI hJ hid B A)
  filter_upwards [hall] with U hU s t hst hwin
  have hcongr : LocMart.psum (fun j => LocGroupSimul.dQTW p m (s + j) I J hI hJ B A) (t - s) U
      = LocMart.psum (fun j => dQ p m I J hI hJ (s + j)) (t - s) U := by
    simp only [LocMart.psum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < t - s := Finset.mem_range.mp hj
    have hjt : s + j < t := by omega
    exact hU (s + j) (hwin (s + j) (Nat.le_add_right s j) hjt)
  rw [hcongr]
  have hQ : Q p m I J hI hJ t U - Q p m I J hI hJ s U
      = ∑ j ∈ Finset.range (t - s), dQ p m I J hI hJ (s + j) U := by
    have hts : s + (t - s) = t := Nat.add_sub_cancel' hst
    have hsplit := Finset.sum_range_add (fun k => dQ p m I J hI hJ k U) s (t - s)
    simp only [Q, hts] at hsplit ⊢
    linarith
  rw [hQ]
  simp only [LocMart.psum]

/-! ## 4. Axiom audit -/


end MWin
