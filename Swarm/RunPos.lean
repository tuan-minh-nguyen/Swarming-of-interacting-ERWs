/-
# The windowed `GoodWWin` at the *position* level: no record clock in the finite-run term

## What is changed, and why

`SiteWindow.goodWWin_of_locmax` (and hence `AstarPos.moveCarrierWin_of_carrier_hybrid`)
needs the mark row bounded on the **time** window `n + 2`:
`Gtail p m U i u (n+2) ≤ G` for `u ≤ xTop`.  Read through the finite-run carrier
(`SwarmCarrier.Gtail_le_of_runs`) this produces the run hypothesis
`RunsOK (siteMarks p m U i) (n+3) K` at every *time* of the record window, and the only known
way to measure that event is the record-clock tail `RecordClockTail.recTimeA_tail`, whose drift
constant is `(2p-1)(N-2m)` — positive **only** for `2m < N`.

The observation here is that `n+2` is not needed.  `EsumWin_le_of_window` compares
`hSum (wA …) u xTop` with `Gtail … u (n+2)` only through
`hSum_le_two_Gtail`, whose hypothesis on the truncation site is `R + 1 ≤ K`, where
`R = (runMax p m U i₀ n).toNat` is the *leader's running maximum*.  Since
`xTop ≤ R + 1` (`xTop_le_succ_of_max`) and `Gtrunc_le_of_runs` needs exactly `x + N ≤ b`,
the tight choice is `K = R + 1`, a **position**.  On the record carrier the leader's running
maximum is at most `r + T·L` (`LocCoordGeomCarrier.Rmax_le_nat_step`), so the finite-run event is
needed only at the deterministic level `r + T·L + 1` — no clock, no drift constant, every `N`.

* `Gtail_le_of_runs_target` — `Gtail … u (R+1) ≤ 2 + K/(1-(1-p)/p)` from `RunsOK … (R+1) K`.
* `EsumWin_le_of_window_pos` — `EsumWin ≤ 2G` from the position-level `Gtail` bound.
* `goodWWin_of_locmax_pos` — the windowed good event with the position-level `Gtail` bound.

The constants `2H+6`, `2G`, `max (2H+6) (2G)` are exactly those of `goodWWin_of_locmax`; only the
level of the `Gtail` hypothesis changes.
-/
import Swarm.WindowEnvelope
import Swarm.CarrierModel

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio

namespace WindowPos

variable {N : ℕ}

/-! ## 1. The truncated forward potential at the leader's own running maximum -/

/-- **`Gtail` at the leader's running maximum, from the run event at that same level.**  If the
mark row has no run of `K` unmarked sites below `R + 1`, then `Gtail` truncated at `R + 1` is at
most `2 + K/(1-(1-p)/p)`, for every `u ≤ R + 1`.

This is `SwarmCarrier.Gtail_le_of_runs` with the *time* level `n+3` replaced by the *position*
level `R+1`: `Gtrunc_le_of_runs` only asks `x + N ≤ b`, and here `x = u+1`, `N = R+1-u-1`. -/
theorem Gtail_le_of_runs_target {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (U : Array N) (i : Fin N) {R Lrun K : ℕ} (hK : 1 ≤ K) (hR : R + 1 ≤ Lrun)
    (hrun : SwarmRun.RunsOK (siteMarks p m U i) Lrun K) (u : ℕ) :
    Gtail p m U i u (R + 1) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
  have hden : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hnn : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := by positivity
  rcases lt_or_ge u (R + 1) with hlt | hge
  · have h1 : Gtail p m U i u (R + 1) = 1 + Gsum p m U i u (R + 1) := rfl
    rw [h1, SiteWindow.Gsum_eq_Gtrunc (by linarith : p ≠ 0) U i hlt]
    have h2 : Gtrunc p (siteMarks p m U i) (R + 1 - u - 1) (u + 1)
        ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by
      refine SwarmRun.Gtrunc_le_of_runs hp1 hp2 hK hrun ?_
      omega
    linarith
  · have hempty : Finset.Ico u (R + 1) = ∅ := Finset.Ico_eq_empty_iff.mpr (by omega)
    have h1 : Gtail p m U i u (R + 1) = 1 + Gsum p m U i u (R + 1) := rfl
    rw [h1, Gsum, hempty, Finset.sum_empty]
    linarith

/-- `Gtail` is monotone in the truncation site: the summands are nonnegative. -/
theorem Gtail_mono_target {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (U : Array N) (i : Fin N)
    {u K K' : ℕ} (hK : K ≤ K') : Gtail p m U i u K ≤ Gtail p m U i u K' := by
  have hnn : ∀ z : ℕ, 0 ≤ ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (omegaN p m U i) v :=
    fun z => Finset.prod_nonneg fun v _ =>
      rq_nonneg (omegaAt_pos p m U hp i (v : ℤ))
        (omegaAt_le_one p m U hp1 i (v : ℤ))
  have hmono : Gsum p m U i u K ≤ Gsum p m U i u K' := by
    unfold Gsum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hK)
      (fun z _ _ => hnn z)
  unfold Gtail
  linarith

/-! ## 2. `EsumWin` from the position-level `Gtail` bound -/

/-- **`Esum` on the level window, with the potential truncated at the leader's running maximum.**
This is `SiteWindow.EsumWin_le_of_window` with the `Gtail` hypothesis at `R + 1` instead of
`n + 2`.  The proof is the same, with `hSum_le_two_Gtail` used at `K = R + 1`. -/
theorem EsumWin_le_of_window_pos {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {i₀ : Fin N} (hi₀K : i₀ ∈ K)
    (hi₀J : i₀ ∈ Jᶜ) (hmax : Rmax p m n K hK U ≤ (runMax p m U i₀ n).toNat) {A : ℕ}
    {G : ℝ} (hGnn : 0 ≤ G)
    (hG : ∀ u : ℕ, A ≤ u → u ≤ xTop p m n K hK U →
      Gtail p m U i₀ u ((runMax p m U i₀ n).toNat + 1) ≤ G) :
    SiteWindow.EsumWin p m n J K hK A U ≤ 2 * G := by
  set R : ℕ := (runMax p m U i₀ n).toNat with hR
  have htopR : xTop p m n K hK U ≤ R + 1 := xTop_le_succ_of_max p m n K hK U hmax
  have hRz : ((R : ℕ) : ℤ) = runMax p m U i₀ n :=
    Int.toNat_of_nonneg (runMax_nonneg_pos p m n i₀ U)
  have hcomp : ∀ v : ℕ, v < R → omegaN p m U i₀ v ≤ wA p m U n Jᶜ v := by
    intro v hv
    refine omegaAt_le_wA p m U hp.le hi₀J (x := v) ?_
    rw [← hRz]
    exact_mod_cast hv
  refine Finset.sup'_le _ _ fun u hu => ?_
  rw [Finset.mem_range] at hu
  by_cases hwin : A ≤ u ∧ u ≤ xTop p m n K hK U
  · rw [if_pos hwin]
    rcases le_or_gt u R with huR | huR
    · have h1 : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)
          ≤ 2 * Gtail p m U i₀ u (R + 1) :=
        hSum_le_two_Gtail (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i₀) (u := u)
          (x := xTop p m n K hK U) (R := R) (K := R + 1) huR htopR hcomp (le_refl _)
      have h2 : Gtail p m U i₀ u (R + 1) ≤ G := hG u hwin.1 hwin.2
      linarith
    · have huEq : u = R + 1 := by omega
      have htopEq : xTop p m n K hK U = R + 1 := by omega
      have hempty : Finset.Ico u (xTop p m n K hK U) = ∅ := by
        rw [Finset.Ico_eq_empty_iff]
        omega
      have hzero : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) = 0 := by
        rw [hSum, hempty, Finset.sum_empty]
      have hG1 : 1 ≤ Gtail p m U i₀ u (R + 1) := by
        rw [Gtail]
        linarith [Gsum_nonneg hp.le hp1 m U i₀ u (R + 1)]
      have hGpos : 0 ≤ 2 * G := by linarith [hG u hwin.1 hwin.2]
      rw [hzero]
      exact hGpos
  · rw [if_neg hwin]
    linarith

/-! ## 3. The windowed good event with the position-level potential bound -/

/-- **The windowed `GoodWWin` from the window `(locmax)` hypotheses, at the leader's position.**
Same statement as `SiteWindow.goodWWin_of_locmax`, except that the `Gtail` hypothesis is at
`(runMax p m U i n).toNat + 1` instead of `n + 2`.  Since `Gtail` is monotone in its truncation
site, this is a *weaker* hypothesis and gives the same conclusion. -/
theorem goodWWin_of_locmax_pos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {A : ℕ} {H G : ℝ} (hH1 : 1 ≤ H) (hGnn : 0 ≤ G)
    (hA : ∀ i ∈ I, A ≤ (runMax p m U i n).toNat)
    (hH : ∀ i ∈ I, ∀ v : ℕ, A ≤ v + 1 →
      v ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U →
      hfix (omegaN p m U i) v ≤ H)
    (hG : ∀ i ∈ I, ∀ u : ℕ, A ≤ u →
      u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U →
      Gtail p m U i u ((runMax p m U i n).toNat + 1) ≤ G) :
    SiteWindow.GoodWWin p m n I J hI (max (2 * H + 6) (2 * G)) A U := by
  have hK : (I ∪ J).Nonempty := hJ.mono Finset.subset_union_right
  obtain ⟨i₀, hi₀, hlead⟩ := exists_leader_in_I I J hI hJ hsep
  have hi₀J : i₀ ∈ Jᶜ := Finset.mem_compl.mpr (Finset.disjoint_left.mp hid hi₀)
  have hmax := Rmax_le_leader I J hI hi₀ hlead
  refine ⟨hsep, ?_, ?_⟩
  · refine le_trans (SiteWindow.EfixWin_le_of_window (N := N) hp0.le hp1 (hK := hK) (U := U)
      (A := A) (Finset.mem_union_left _ hi₀) hi₀J hmax (hA i₀ hi₀) hH1 ?_)
      (le_max_left _ _)
    · intro v hv1 hv2
      exact hH i₀ hi₀ v hv1 hv2
  · refine le_trans (EsumWin_le_of_window_pos (N := N) hp0 hp1 (hK := hK) (U := U)
      (A := A) (Finset.mem_union_left _ hi₀) hi₀J hmax hGnn ?_) (le_max_right _ _)
    · intro u hu1 hu2
      exact hG i₀ hi₀ u hu1 hu2

end WindowPos
