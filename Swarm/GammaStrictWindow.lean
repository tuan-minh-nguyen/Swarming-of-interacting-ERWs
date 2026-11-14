/-
  **Direction (A): the actual strict-drift / Gamma-count window composition.**

  Three accepted packages are joined here, on the actual trajectory of the i.i.d. uniform array:

  * `GammaFin.lean` — the *finished* trial `GammaFinPiece p m A hA y j n iy` at its finishing time
    `n = j + (2m-1)`: the paper's trial pieces **plus** `(sep)` at `n`, with the pathwise content
    (`GammaFin_rightProbability` `α = 1/2`, `GammaFin_wA` `w = p`) and the strict conditional bound
    in the `∃`-form `condExp_indicator_WA_strict_le_exists` that a path-dependent leader needs;
  * `WindowBounds.lean` — the passage-time geometry: a level `y` in the record window
    `R_s^A < y ≤ R_t^A - 2m` finishes at a *finite* time `σ_y^A + 2m - 1` strictly inside `(s,t)`,
    and distinct levels finish at distinct times;
  * `GammaAmbient.lean` — the Gamma **count**: on `ambGood`, and for `n₀ ≤ s ≤ t ≤ n₀ + (T+3)L`
    with the group record inside `[r-L, r]` at `n₀`,
    `(1-p)^{(2m-1)|A|}(R_t^A - R_s^A) - C L^{3/4} ≤ #{R_s^A < y ≤ R_t^A - 2m : Γ_y^A}`.

  What is proved here (all for the paper's `I = A`, `J = Aᶜ`, `W_n = W_n^{A,Aᶜ}`):

  1. `StrictAt` — the event "some finished trial of the group finishes at time `n`", as the finite
     union of the accepted `GammaFinAt` over the levels `y ∈ [0,n]`.  It is `posFilt n`-measurable,
     it is contained in `(sep)` at `n`, and at every path in it some leader `iy ∈ A` has
     `α_n^{iy} = 1/2` and `w_n^{A}(X_n^{iy}) = p`.  Consequently
     **`condExp_indicator_StrictAt_le`**:
     `E[1_{StrictAt n}(W_{n+1}-W_n) | F_n] ≤ -(2p-1)/|A| · 1_{StrictAt n}`
     — the strict step applied to the *actual* path-dependent finishing event, not to a fixed
     level's container.  Membership in `GammaSet` alone is not enough: `(sep)` at the finishing
     time is carried by `GammaFinAt`.
  2. `winLevels` / `winFinishes` — the paper's random record window `(R_s^A, R_t^A - 2m]` as a
     finite set of levels, and its *strict-time Finset* `{σ_y^A + 2m - 1}`.  The finishing-time map
     is injective on the window (`finishTime_injOn`, from `WindowBounds.sigmaA_finish_inj`), so
     `#winFinishes = #winLevels = recWindowCount` — an **equality**, not just a bound.
  3. `mem_GammaFinAt_finishTime` — **identification**: every counted trial, at its finishing time,
     lies in `GammaFinAt`, i.e. in the accepted finished-trial container (separation at the finish
     included).  Hence the strict times are times at which `StrictAt` holds.
  4. `condMean` — the paper's conditional-mean sequence `a_n(U) = E[1_{(sep)}(W_{n+1}-W_n) | F_n](U)`
     (the conditional mean of `WdriftJoint.Qraw`), and `ae_condMean_le_indicator`:
     `a_n ≤ -(2p-1)/|A| · 1_{StrictAt n}` a.e., obtained by combining the strict bound on the
     `F_n`-measurable subevent `StrictAt n` with `(Wdrift)` `a_n ≤ 0` on the rest.  Both are
     conditional expectations *evaluated at the path*, which is what the window sum needs.
  5. `ae_window_gamma_drift_le` — **the composition**: on `ambGood` and on a fully separated window
     `{∀ n ∈ [s,t), (sep) at n}`, almost surely
     `W_t - W_s ≤ -γ (R_t^A - R_s^A) + κ C L^{3/4} + (Q_t - Q_s)`,
     with the paper's rate `γ = (2p-1)(1-p)^{(2m-1)|A|}/|A|`, defect coefficient
     `κ = (2p-1)/|A|`, `C = 2m(1-p)^{(2m-1)|A|} + 4m`, and `Q^{A,Aᶜ}` the accepted martingale
     correction (`WdriftJoint.Q`, a `Martingale` by `WdriftJoint.martingale_Q`).

  Scope.  This is the `-(R_t^A - R_s^A)` half of `(locmove)` composed with the Gamma count, at the
  paper's constants, with the martingale defect left explicit (`Q_t - Q_s`).  The defect is *not*
  estimated here: that is the `(locsum)`/`(locmax)` second-moment input.  Not proved here either:
  the `H^A`-growth half, `(locgroup)`, tightness, regeneration, `Ballistic`, `MainClaim`, and any
  probability estimate beyond `ambGood`'s own `1 - C_T e^{-c_T √L}`.
-/
import Swarm.GammaFin
import Swarm.GammaAmbient
import Swarm.WindowBounds
import Swarm.LocMoveH

set_option maxHeartbeats 2000000
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Swarming.GammaStrict

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift Swarming.Enl LocMove

variable {N : ℕ}

/-! ## 1. The strict-time event at a single time -/

/-- Some finished trial of the group `A` finishes at time `n`. -/
noncomputable def StrictAt (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (n : ℕ) : Set (Array N) :=
  ⋃ y ∈ Finset.Icc (0 : ℤ) (n : ℤ), GammaFin.GammaFinAt p m A hA y n

lemma measurableSet_StrictAt (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (n : ℕ) :
    MeasurableSet[posFilt N p m n] (StrictAt p m A hA n) :=
  Finset.measurableSet_biUnion _ (fun y _ => GammaFin.measurableSet_GammaFinAt p m A hA y n)

/-- Every path in `StrictAt n` is separated at time `n`: the conjunction is carried by the
finished-trial container `GammaFinAt` (it is *not* implied by the raw trial `Γ_y^A`). -/
lemma StrictAt_subset_sepSet {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {n : ℕ} :
    StrictAt p m A hA n ⊆ {U : Array N | SepSet p m n A Aᶜ U} := by
  intro U hU
  simp only [StrictAt, Set.mem_iUnion] at hU
  obtain ⟨y, -, hy⟩ := hU
  unfold GammaFin.GammaFinAt at hy
  split_ifs at hy with h
  · exact GammaFin.GammaFin_subset_SepSet p m A hA y (n - (2 * m - 1)) n hy
  · exact absurd hy (Set.notMem_empty U)

/-- **The finished trial supplies the strict-step hypotheses on `StrictAt`**: at a path in
`StrictAt n` there is a leader `iy ∈ A` sitting at a site excited for the group (`w = p`) but not
for itself (`α = 1/2`). -/
lemma exists_leader_of_mem_StrictAt {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin N)}
    {hA : A.Nonempty} {n : ℕ} {U : Array N} (hU : U ∈ StrictAt p m A hA n) :
    ∃ iy ∈ A,
      rightProbability p m (trajectory p m U n).ell iy (X p m U n iy) = 1 / 2 ∧
        wA p m U n A (X p m U n iy).toNat = p := by
  simp only [StrictAt, Set.mem_iUnion] at hU
  obtain ⟨y, hy, hfin⟩ := hU
  rw [Finset.mem_Icc] at hy
  have hy0 : 0 ≤ y := hy.1
  unfold GammaFin.GammaFinAt at hfin
  split_ifs at hfin with hle
  swap
  · exact absurd hfin (Set.notMem_empty U)
  simp only [GammaFin.GammaFin, Set.mem_iUnion] at hfin
  obtain ⟨iy, hiy, hpiece⟩ := hfin
  have hsub : n - (2 * m - 1) + (2 * m - 1) = n := Nat.sub_add_cancel hle
  have hpiece' : U ∈ GammaFin.GammaFinPiece p m A hA y (n - (2 * m - 1))
      (n - (2 * m - 1) + (2 * m - 1)) iy := by
    rwa [hsub]
  refine ⟨iy, hiy, ?_, ?_⟩
  · simpa only [hsub] using
      GammaFin.GammaFin_rightProbability (p := p) (m := m) hm hy0 hpiece' hiy
  · simpa only [hsub] using GammaFin.GammaFin_wA (p := p) (m := m) hm hy0 hpiece' hiy

/-- **The strict conditional mean at the actual path-dependent finishing event**:
`E[1_{StrictAt n}(W^{A,Aᶜ}_{n+1} - W^{A,Aᶜ}_n) | F_n] ≤ᵐ -(2p-1)/|A| · 1_{StrictAt n}`. -/
theorem condExp_indicator_StrictAt_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (n : ℕ) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => (StrictAt p m A hA n).indicator
        (fun U => WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc) U)
    ≤ᵐ[arrayMeasure N] fun U =>
      (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
        (StrictAt p m A hA n).indicator (fun _ => (1 : ℝ)) U :=
  GammaFin.condExp_indicator_WA_strict_le_exists hp0 hp1 m n A Aᶜ hA hAc
    disjoint_compl_right (measurableSet_StrictAt p m A hA n)
    (fun U hU => StrictAt_subset_sepSet hU)
    (fun U hU => by
      obtain ⟨iy, hiy, h1, h2⟩ := exists_leader_of_mem_StrictAt hm hU
      exact ⟨iy, hiy, h1, by simpa using h2⟩)

/-! ## 2. The record window as a finite set of levels, and its finishing times -/

/-- The paper's random record window `(R_s^A, R_t^A - 2m]`, as the finite set of levels at which
the trial `Γ_y^A` succeeded.  Its cardinality is exactly the accepted `recWindowCount`. -/
noncomputable def winLevels (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (s t : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (runMaxA p m U hA s + 1) (runMaxA p m U hA t - ((2 * m : ℕ) : ℤ))).filter
    (fun y => U ∈ GammaSet p m hA y)

lemma winLevels_card (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (s t : ℕ) :
    (winLevels p m hA U s t).card = recWindowCount p m hA U s t := rfl

lemma mem_winLevels_iff {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {U : Array N}
    {s t : ℕ} {y : ℤ} :
    y ∈ winLevels p m hA U s t ↔
      runMaxA p m U hA s + 1 ≤ y ∧ y ≤ runMaxA p m U hA t - ((2 * m : ℕ) : ℤ) ∧
        U ∈ GammaSet p m hA y := by
  classical
  rw [winLevels, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Window levels are nonnegative: the group record never goes below its initial value `0`. -/
lemma window_level_nonneg {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {U : Array N}
    {s t : ℕ} {y : ℤ} (hy : y ∈ winLevels p m hA U s t) : 0 ≤ y := by
  obtain ⟨h1, -, -⟩ := mem_winLevels_iff.mp hy
  have h0 := runMaxA_nonneg (p := p) (m := m) (U := U) (hA := hA) s
  omega

/-- The first passage of a window level is finite. -/
lemma window_level_sigma_ne_top {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {U : Array N} {s t : ℕ} {y : ℤ} (hy : y ∈ winLevels p m hA U s t) :
    sigmaA p m U hA y ≠ ⊤ := by
  obtain ⟨-, h2, -⟩ := mem_winLevels_iff.mp hy
  refine sigmaA_ne_top_of_runMaxA_le (y := y) (t := t) ?_
  have h3 : ((2 * m : ℕ) : ℤ) ≥ 0 := by positivity
  omega

/-- The first-passage level of a window level, as a natural number. -/
noncomputable def finishIdx (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (y : ℤ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, sigmaA p m U hA y = (j : WithTop ℕ) then h.choose else 0

lemma finishIdx_spec {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {U : Array N}
    {y : ℤ} (h : ∃ j : ℕ, sigmaA p m U hA y = (j : WithTop ℕ)) :
    sigmaA p m U hA y = (finishIdx p m hA U y : WithTop ℕ) := by
  classical
  rw [finishIdx, dif_pos h]
  exact h.choose_spec

/-- **The finishing time** `σ_y^A + 2m - 1` of the trial at level `y`. -/
noncomputable def finishTime (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (y : ℤ) : ℕ :=
  finishIdx p m hA U y + (2 * m - 1)

/-- **The strict-time Finset of the record window**: the finishing times of the counted trials. -/
noncomputable def winFinishes (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (s t : ℕ) : Finset ℕ :=
  (winLevels p m hA U s t).image (fun y => finishTime p m hA U y)

/-- For a window level, `finishIdx` is the first-passage level of `WindowBounds`. -/
lemma finishIdx_eq_of_window {p : ℝ} {m : ℕ} {A : Finset (Fin N)}
    {hA : A.Nonempty} {U : Array N} {s t : ℕ} {y : ℤ} {j : ℕ}
    (hy : y ∈ winLevels p m hA U s t)
    (hsig : sigmaA p m U hA y = (j : WithTop ℕ)) :
    finishIdx p m hA U y = j := by
  have hex : ∃ j' : ℕ, sigmaA p m U hA y = (j' : WithTop ℕ) := ⟨j, hsig⟩
  have h1 := finishIdx_spec (p := p) (m := m) (hA := hA) (U := U) (y := y) hex
  rw [hsig] at h1
  exact (WithTop.coe_inj.mp h1).symm

/-- A window level lies below its own finishing time:
`y = R^A_{σ_y^A} ≤ σ_y^A ≤ σ_y^A + 2m - 1`. -/
lemma window_level_le_finishTime {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {U : Array N} {s t : ℕ} {y : ℤ} (hy : y ∈ winLevels p m hA U s t) :
    y ≤ (finishTime p m hA U y : ℤ) := by
  have hy0 : 0 ≤ y := window_level_nonneg hy
  obtain ⟨hs, ht, -⟩ := mem_winLevels_iff.mp hy
  obtain ⟨j, np, hsig, -, hslt, hjsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) (s := s) (t := t) hy0
      (by omega) (by omega)
  have hfi : finishIdx p m hA U y = j := finishIdx_eq_of_window hy hsig
  have har : ARMax p m U hA y j := sigmaA_eq_coe_iff.mp hsig
  have hreq : runMaxA p m U hA j = y := ARMax.eq hy0 har
  have hle : y ≤ (j : ℤ) := by
    rw [← hreq]
    exact runMaxA_le_time j
  have hcast : (finishTime p m hA U y : ℤ) = (j : ℤ) + ((2 * m - 1 : ℕ) : ℤ) := by
    simp only [finishTime, hfi]
    push_cast
    ring
  have h2 : (0 : ℤ) ≤ ((2 * m - 1 : ℕ) : ℤ) := by positivity
  omega

/-- **The finishing times of distinct window levels are distinct**
(`WindowBounds.sigmaA_finish_inj`). -/
lemma finishTime_injOn {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    (U : Array N) (s t : ℕ) :
    Set.InjOn (fun y => finishTime p m hA U y) ↑(winLevels p m hA U s t) := by
  intro y hy y' hy' heq
  have hy0 : 0 ≤ y := window_level_nonneg hy
  have hy0' : 0 ≤ y' := window_level_nonneg hy'
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp (window_level_sigma_ne_top hy)
  obtain ⟨j', hj'⟩ := WithTop.ne_top_iff_exists.mp (window_level_sigma_ne_top hy')
  have hne : ∃ j : ℕ, sigmaA p m U hA y = (j : WithTop ℕ) := ⟨j, hj.symm⟩
  have hne' : ∃ j : ℕ, sigmaA p m U hA y' = (j : WithTop ℕ) := ⟨j', hj'.symm⟩
  have h1 := finishIdx_spec (p := p) (m := m) (hA := hA) (U := U) (y := y) hne
  have h2 := finishIdx_spec (p := p) (m := m) (hA := hA) (U := U) (y := y') hne'
  have heq' : finishIdx p m hA U y + (2 * m - 1) = finishIdx p m hA U y' + (2 * m - 1) := heq
  exact sigmaA_finish_inj hy0 hy0' h1 h2 heq'

/-- **The count of strict times equals the count of counted trials.** -/
theorem winFinishes_card_eq_recWindowCount (p : ℝ) (m : ℕ)
    {A : Finset (Fin N)} (hA : A.Nonempty) (U : Array N) (s t : ℕ) :
    (winFinishes p m hA U s t).card = recWindowCount p m hA U s t := by
  rw [winFinishes]
  rw [Finset.card_image_of_injOn (finishTime_injOn U s t)]
  exact winLevels_card p m hA U s t

/-! ## 3. Identification of the counted trials inside `GammaFinAt` -/

/-- Membership in `GammaFinAt` in terms of the underlying finished-trial event (the only case in
which `GammaFinAt` is nonempty is `2m-1 ≤ n`). -/
lemma mem_GammaFinAt_iff {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {U : Array N}
    {y : ℤ} {n : ℕ} (h : 2 * m - 1 ≤ n) :
    U ∈ GammaFin.GammaFinAt p m A hA y n ↔
      U ∈ GammaFin.GammaFin p m A hA y (n - (2 * m - 1)) n := by
  simp only [GammaFin.GammaFinAt, if_pos h]

/-- **Every counted trial lies in the finished-trial container at its finishing time.**  For a
window level `y` (so `R_s^A < y ≤ R_t^A - 2m`) on a fully separated window, the path lies in
`GammaFinAt p m A hA y (σ_y^A + 2m - 1)`: the paper's trial pieces `Γ_y^A` *and* `(sep)` at the
finishing time. -/
lemma mem_GammaFinAt_finishTime {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin N)}
    {hA : A.Nonempty} {U : Array N} {s t : ℕ}
    (hsep : ∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U)
    {y : ℤ} (hy : y ∈ winLevels p m hA U s t) :
    U ∈ GammaFin.GammaFinAt p m A hA y (finishTime p m hA U y) := by
  classical
  have hy0 : 0 ≤ y := window_level_nonneg hy
  obtain ⟨hs, ht, hyG⟩ := mem_winLevels_iff.mp hy
  obtain ⟨j, np, hsig, -, hslt, hjsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) (s := s) (t := t) hy0
      (by omega) (by omega)
  have hfi : finishIdx p m hA U y = j := finishIdx_eq_of_window hy hsig
  simp only [GammaSet, Set.mem_iUnion] at hyG
  obtain ⟨j0, iy, hiy, hpiece, hword⟩ := hyG
  have hARj0 : ARMax p m U hA y j0 := hpiece.1
  have hlead : IsLeader p m U A y j0 iy := hpiece.2
  have hj0 : j0 = j := ARMax_unique hARj0 (sigmaA_eq_coe_iff.mp hsig)
  have hfi' : finishIdx p m hA U y = j0 := by rw [hfi, hj0]
  have htime : finishTime p m hA U y = j0 + (2 * m - 1) := by
    simp only [finishTime, hfi']
  have hlast : j0 + (2 * m - 1) < t := by
    have h2m : j0 + 2 * m ≤ np := by omega
    exact (window_arith (m := m) hm h2m hnle).2
  have hle2 : 2 * m - 1 ≤ finishTime p m hA U y := by omega
  have hsub : finishTime p m hA U y - (2 * m - 1) = j0 := by omega
  refine (mem_GammaFinAt_iff (p := p) (m := m) (A := A) (hA := hA) (U := U) (y := y)
    (n := finishTime p m hA U y) hle2).mpr ?_
  rw [hsub]
  refine Set.mem_iUnion.mpr ⟨iy, Set.mem_iUnion.mpr ⟨hiy, ?_⟩⟩
  exact ⟨⟨⟨hARj0, hlead⟩, hword⟩,
    hsep (finishTime p m hA U y) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)⟩

/-- **The strict-time Finset sits inside the record window** `(s,t)`. -/
theorem winFinishes_subset_Ico {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin N)}
    {hA : A.Nonempty} (U : Array N) (s t : ℕ) :
    winFinishes p m hA U s t ⊆ Finset.Ico s t := by
  intro n hn
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hn
  have hy0 : 0 ≤ y := window_level_nonneg hy
  obtain ⟨hs, ht, -⟩ := mem_winLevels_iff.mp hy
  obtain ⟨j, np, hsig, -, hslt, hjsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) (s := s) (t := t) hy0
      (by omega) (by omega)
  have hfi : finishIdx p m hA U y = j := finishIdx_eq_of_window hy hsig
  have hlt : j + (2 * m - 1) < t := (window_arith (m := m) hm hjsep hnle).2
  rw [Finset.mem_Ico]
  constructor
  · simp only [finishTime, hfi]; omega
  · simp only [finishTime, hfi]; omega

/-- **The strict-time Finset of a window**: the times in `[s,t)` at which some finished trial of
the group finishes.  This is the Finset `T` a drift summation over strict times refers to. -/
noncomputable def strictTimes (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (s t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico s t).filter (fun n => U ∈ StrictAt p m A hA n)

lemma mem_strictTimes_iff {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {U : Array N}
    {s t n : ℕ} :
    n ∈ strictTimes p m hA U s t ↔ n ∈ Finset.Ico s t ∧ U ∈ StrictAt p m A hA n := by
  classical
  rw [strictTimes, Finset.mem_filter]

lemma strictTimes_subset {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    (U : Array N) (s t : ℕ) : strictTimes p m hA U s t ⊆ Finset.Ico s t := by
  classical
  exact Finset.filter_subset _ _

/-- **The strict times are times at which `StrictAt` holds**, hence subject to the strict
conditional bound. -/
theorem winFinishes_subset_strictTimes {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin N)}
    {hA : A.Nonempty} {U : Array N} {s t : ℕ}
    (hsep : ∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) :
    winFinishes p m hA U s t ⊆ strictTimes p m hA U s t := by
  classical
  intro n hn
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hn
  refine mem_strictTimes_iff.mpr ⟨winFinishes_subset_Ico hm U s t hn, ?_⟩
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
    ⟨Finset.mem_Icc.mpr ⟨window_level_nonneg hy, window_level_le_finishTime hy⟩,
      mem_GammaFinAt_finishTime hm hsep hy⟩⟩

/-! ## 4. The paper's conditional-mean sequence, and the strict bound on it -/

/-- The paper's conditional mean `a_n(U) = E[1_{(sep)}(W^{A,Aᶜ}_{n+1} - W^{A,Aᶜ}_n) | F_n]`,
evaluated at the path `U`.  This is the conditional mean of `WdriftJoint.Qraw`; the drift sum is
over these *evaluated* conditional means, so the pathwise identity of §5 is term by term. -/
noncomputable def condMean (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (n : ℕ) (U : Array N) : ℝ :=
  condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m A Aᶜ hA hAc n) U

/-- On the separation event, the paper's raw `Q`-increment `Qraw` is the genuine increment. -/
lemma Qraw_of_sep {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {hAc : Aᶜ.Nonempty}
    {n : ℕ} {U : Array N} (hsep : SepSet p m n A Aᶜ U) :
    Qraw p m A Aᶜ hA hAc n U = WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc := by
  simp only [Qraw]
  exact Set.indicator_of_mem (s := {U : Array N | SepSet p m n A Aᶜ U}) hsep _

/-- **(Wdrift) for the paper's `Qraw`**: the conditional mean of the separated increment is
nonpositive. -/
lemma condMean_le_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    {A : Finset (Fin N)} {hA : A.Nonempty} {hAc : Aᶜ.Nonempty} (n : ℕ) :
    condMean p m hA hAc n ≤ᵐ[arrayMeasure N] 0 :=
  Wdrift_sep hp0 hp1 m n A Aᶜ hA hAc disjoint_compl_right

/-- **The strict guard**: `1_{StrictAt n}` times the paper's conditional mean is at most
`-(2p-1)/|A|`.  The `F_n`-measurable indicator `1_{StrictAt n}` is pulled out of the conditional
expectation (on `StrictAt n` the separated increment `Qraw` agrees with `W_{n+1}-W_n` itself), and
the strict bound of §1 applies. -/
theorem ae_indicator_condMean_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (n : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      (StrictAt p m A hA n).indicator (fun U => condMean p m hA hAc n U) U
        ≤ (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
            (StrictAt p m A hA n).indicator (fun _ => (1 : ℝ)) U := by
  classical
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hsmeas : MeasurableSet[posFilt N p m n] (StrictAt p m A hA n) :=
    measurableSet_StrictAt p m A hA n
  have hstrict := condExp_indicator_StrictAt_le hp0 hp1 hm A hA hAc n
  -- on `StrictAt n` the separated increment is the genuine increment
  have hfun : (fun U => (StrictAt p m A hA n).indicator
        (fun U => WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc) U)
      = fun U => (StrictAt p m A hA n).indicator (Qraw p m A Aᶜ hA hAc n) U := by
    funext U
    by_cases hU : U ∈ StrictAt p m A hA n
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
      have hsep : SepSet p m n A Aᶜ U := StrictAt_subset_sepSet hU
      rw [Qraw_of_sep hsep]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
  -- pull the `F_n`-measurable indicator out of the conditional expectation
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => (StrictAt p m A hA n).indicator (Qraw p m A Aᶜ hA hAc n) U)
      =ᵐ[arrayMeasure N]
        fun U => (StrictAt p m A hA n).indicator (condMean p m hA hAc n) U :=
    condExp_indicator (integrable_Qraw hp hp1' m n A Aᶜ hA hAc) hsmeas
  filter_upwards [hstrict, hpull] with U h1 h2
  rw [hfun] at h1
  rw [← h2]
  exact h1

/-- **The pointwise drift bound of the window summation**: `a_n ≤ -(2p-1)/|A| · 1_{StrictAt n}`.
At a strict time the strict guard applies; at every other time `(Wdrift)` gives `a_n ≤ 0`. -/
theorem ae_condMean_le_indicator
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (n : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      condMean p m hA hAc n U
        ≤ (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
            (StrictAt p m A hA n).indicator (fun _ => (1 : ℝ)) U := by
  filter_upwards [ae_indicator_condMean_le hp0 hp1 hm A hA hAc n,
    condMean_le_zero (p := p) (m := m) (hA := hA) (hAc := hAc) hp0 hp1 n]
    with U h1 h0
  by_cases hU : U ∈ StrictAt p m A hA n
  · simpa only [Set.indicator_of_mem hU, mul_one] using h1
  · simpa only [Set.indicator_of_notMem hU, mul_zero, Pi.zero_apply] using h0

/-! ## 5. Telescoping, and the window sum of conditional means -/

/-- `∑_{n∈[s,t)} (f(n+1) - f n) = f t - f s`. -/
lemma sum_Ico_telescope {f : ℕ → ℝ} {s t : ℕ} (h : s ≤ t) :
    ∑ n ∈ Finset.Ico s t, (f (n + 1) - f n) = f t - f s := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk, ih]
      ring

/-- The martingale-defect sum telescopes: `∑_{n∈[s,t)} dQ_n = Q_t - Q_s`. -/
lemma sum_Ico_dQ {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {hAc : Aᶜ.Nonempty}
    {s t : ℕ} (hst : s ≤ t) (U : Array N) :
    ∑ n ∈ Finset.Ico s t, dQ p m A Aᶜ hA hAc n U
      = Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U := by
  rw [Finset.sum_Ico_eq_sub _ hst]
  simp only [Q]

/-- At a separated time the paper's conditional mean is the increment minus the `Q`-increment. -/
lemma condMean_eq_sub_dQ {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {hAc : Aᶜ.Nonempty} {n : ℕ} {U : Array N} (hsep : SepSet p m n A Aᶜ U) :
    condMean p m hA hAc n U
      = (WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc)
        - dQ p m A Aᶜ hA hAc n U := by
  have hq : Qraw p m A Aᶜ hA hAc n U
      = WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc := Qraw_of_sep hsep
  simp only [dQ, condMean, hq]
  ring

/-- **The window sum of the paper's conditional means equals the genuine increment minus the
martingale defect**, on a fully separated window:
`∑_{n∈[s,t)} a_n = (W_t - W_s) - (Q_t - Q_s)`. -/
theorem sum_condMean_eq {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {hAc : Aᶜ.Nonempty} {s t : ℕ} (hst : s ≤ t) {U : Array N}
    (hsepwin : ∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) :
    ∑ n ∈ Finset.Ico s t, condMean p m hA hAc n U
      = (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc)
        - (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U) := by
  have hstep : ∀ n ∈ Finset.Ico s t, condMean p m hA hAc n U
      = ((WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc)
        - dQ p m A Aᶜ hA hAc n U) :=
    fun n hn => condMean_eq_sub_dQ (p := p) (m := m) (hA := hA) (hAc := hAc) (hsepwin n hn)
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  rw [sum_Ico_telescope (f := fun k => WA p m U k A Aᶜ hA hAc) hst, sum_Ico_dQ hst]

/-! ## 6. The composition: the Gamma-driven drift term with explicit martingale defect -/

/-- A finite family of almost-sure statements holds simultaneously almost surely. -/
lemma eventually_forall_mem_finset {ι : Type*} (s : Finset ι) {P : ι → Array N → Prop}
    (h : ∀ i ∈ s, ∀ᵐ U ∂(arrayMeasure N), P i U) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i ∈ s, P i U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : ∀ᵐ U ∂(arrayMeasure N), P a U := h a (Finset.mem_insert_self a s)
      have h2 : ∀ᵐ U ∂(arrayMeasure N), ∀ i ∈ s, P i U :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      filter_upwards [h1, h2] with U hU1 hU2 i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hU1
      · exact hU2 i hi

/-- **The count of actual strict times carries the Gamma count.**  On `ambGood`, for a fully
separated window and `n₀ ≤ s ≤ t ≤ n₀ + (T+3)L` with `r - L ≤ R^A_{n₀} ≤ r`:

`(1-p)^{(2m-1)|A|} (R_t^A - R_s^A) - C L^{3/4} ≤ #(strict times)`,  `C = 2m(1-p)^{(2m-1)|A|} + 4m`.

The strict times are the *distinct* finishing times `σ_y^A + 2m - 1` of the counted trials
`Γ_y^A`, `R_s^A < y ≤ R_t^A - 2m`; they equal the count of trials exactly
(`winFinishes_card_eq_recWindowCount`) and each of them is a time at which `StrictAt` holds, i.e.
a finished trial with `(sep)` at its finish (`winFinishes_subset_strictTimes`). -/
theorem card_strictTimes_ge
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ}
    (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r) {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t)
    (hhor : t ≤ n0 + (Th + 3) * Lh) {U : Array N} (hgood : U ∈ ambGood p m hA r Th Lh)
    (hsepwin : ∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U)
    (hlo0 : r - (Lh : ℤ) ≤ runMaxA p m U hA n0) (hhi : runMaxA p m U hA n0 ≤ r) :
    (1 - p) ^ ((2 * m - 1) * A.card) *
        ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
        - ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
            Real.sqrt (Lh * Real.sqrt Lh)) ≤ (strictTimes p m hA U s t).card := by
  classical
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hr' : ((Th : ℤ) + 3) * (Lh : ℤ) ≤ r := by
    have hcast : (((Th + 3) * Lh : ℕ) : ℤ) = ((Th : ℤ) + 3) * (Lh : ℤ) := by
      push_cast
      ring
    rwa [hcast] at hr
  have hcount := gamma_actual_window_count_paper p hp hp1 m (by omega) hA hL hr' hgood
    hn0 hst hhor hlo0 hhi
  have h1 : (recWindowCount p m hA U s t : ℝ) ≤ (strictTimes p m hA U s t).card := by
    rw [← winFinishes_card_eq_recWindowCount p m hA U s t]
    exact_mod_cast Finset.card_le_card (winFinishes_subset_strictTimes hm hsepwin)
  linarith

/-- **The `-(R_t^A - R_s^A)` half of `(locmove)`, driven by the Gamma count, on a fully separated
window.**

For `1/2 < p < 1`, `1 ≤ m`, `L ≥ 1`, `(T+3)L ≤ r`, times `n₀ ≤ s ≤ t ≤ n₀ + (T+3)L` and the
group-record conditions `r - L ≤ R^A_{n₀} ≤ r`, almost surely, on the ambient-Gamma-good event and
on the event that *every* time of the window is separated for `A, Aᶜ`:

`W_t^{A,Aᶜ} - W_s^{A,Aᶜ} ≤ -γ (R_t^A - R_s^A) + κ C L^{3/4} + (Q_t^{A,Aᶜ} - Q_s^{A,Aᶜ})`,

with `γ = (2p-1)(1-p)^{(2m-1)|A|}/|A|`, `κ = (2p-1)/|A|`,
`C = 2m(1-p)^{(2m-1)|A|} + 4m`, and `Q^{A,Aᶜ}` the accepted martingale correction
(`WdriftJoint.Q`, a `Martingale` by `WdriftJoint.martingale_Q`).  The defect is left explicit: it
is *not* estimated here. -/
theorem ae_window_gamma_drift_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ambGood p m hA r Th Lh →
      (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
      r - (Lh : ℤ) ≤ runMaxA p m U hA n0 → runMaxA p m U hA n0 ≤ r →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          + (2 * p - 1) / ((A.card : ℕ) : ℝ) *
              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                Real.sqrt (Lh * Real.sqrt Lh))
          + (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U) := by
  classical
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hr' : ((Th : ℤ) + 3) * (Lh : ℤ) ≤ r := by
    have hcast : (((Th + 3) * Lh : ℕ) : ℤ) = ((Th : ℤ) + 3) * (Lh : ℤ) := by
      push_cast
      ring
    rwa [hcast] at hr
  filter_upwards [eventually_forall_mem_finset (Finset.Ico s t)
      (fun n _ => ae_condMean_le_indicator hp0 hp1 hm A hA hAc n)]
    with U hbnd hgood hsepwin hlo0 hhi
  set T : Finset ℕ := strictTimes p m hA U s t with hT
  have hTsub : T ⊆ Finset.Ico s t := hT ▸ strictTimes_subset U s t
  have hstrict : ∀ n ∈ T, condMean p m hA hAc n U ≤ -(2 * p - 1) / ((A.card : ℕ) : ℝ) := by
    intro n hn
    rw [hT] at hn
    obtain ⟨hnI, hnS⟩ := mem_strictTimes_iff.mp hn
    have h1 := hbnd n hnI
    rw [Set.indicator_of_mem hnS, mul_one] at h1
    exact h1
  have hother : ∀ n ∈ Finset.Ico s t, n ∉ T → condMean p m hA hAc n U ≤ 0 := by
    intro n hnI hnT
    have hnT' : n ∉ strictTimes p m hA U s t := hT ▸ hnT
    have h1 := hbnd n hnI
    rw [Set.indicator_of_notMem (fun hS => hnT' (mem_strictTimes_iff.mpr ⟨hnI, hS⟩))] at h1
    simpa using h1
  have hcard : (1 - p) ^ ((2 * m - 1) * A.card) *
        ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
        - ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
            Real.sqrt (Lh * Real.sqrt Lh)) ≤ (T.card : ℝ) := by
    have hcount := card_strictTimes_ge (p := p) hp0 hp1 hm A hA hL hr hn0 hst hhor hgood
      hsepwin hlo0 hhi
    rw [hT]
    exact hcount
  have hrate := sum_Ico_le_gamma_rate (p := p) hp0 hp1 m A hA (s := s) (t := t)
    (a := fun n => condMean p m hA hAc n U) (T := T) hTsub hstrict hother hcard
  have hsplit := sum_condMean_eq (p := p) (m := m) (A := A) (hA := hA) (hAc := hAc) hst
    (U := U) (fun n hn => hsepwin n hn)
  have hkey : WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
      = (∑ n ∈ Finset.Ico s t, condMean p m hA hAc n U)
        + (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U) := by
    rw [hsplit]
    ring
  rw [hkey]
  linarith

end Swarming.GammaStrict
