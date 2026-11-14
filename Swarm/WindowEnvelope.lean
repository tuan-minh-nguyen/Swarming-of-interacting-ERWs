/-
# The windowed `GoodW` envelope: the smallest honest repair of the site-locality bridge

`PrefixObstruction.lean` shows that `LocGroupQ.GoodW`'s *prefix* envelope
(`Efix`/`Esum` are suprema over all levels `u ≤ xTop`) is not a function of the `(locmax)` window
data: a long unmarked block below the window forces `hfix (omegaN) (M-1) = 2M+1` while every site
of a window above it is small.

This file proves the repair.  `EfixWin A` and `EsumWin A` are the same suprema restricted to the
*level window* `[A-1, xTop]` (encoded as `A ≤ u + 1`), `EsumWin A` to `[A, xTop]`:

* `EfixWin_le_of_window` — separation, the leader `i₀ ∈ I`, `A ≤ M_n^{i₀}`, and
  `hfix (omegaN p m U i₀) v ≤ H` for `v ∈ [A-1, xTop]` give `EfixWin A ≤ 2H + 6`;
* `EsumWin_le_of_window` — `Gtail p m U i₀ u (n+2) ≤ G` for `u ∈ [A, xTop]` gives
  `EsumWin A ≤ 2G`;
* `goodWWin_of_locmax` — the two together with `(sep)` give the windowed good event.

The window `[A-1, xTop]` is exactly the range of levels the paper ever queries: the current
positions and running maxima of the walkers during the record window, plus one level below for
`hprev`.  It is therefore the range that `(locmax)` on the record window `[r-(T+3)L, r+(T+3)L]`
controls.  `WindowStep.lean` composes this with the `hBound` step estimate.

No `sorry`, no extra axiom.  The constants `2H+6` and `2G` are the same as in
`LocGroupQ.Efix_le_of_locmax` / `Esum_le_of_locmax`; only the range of the hypothesis shrinks.
-/
import Swarm.GroupQ2
import Swarm.SiteDiffStatic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ

variable {N : ℕ}

/-! ### 1. The windowed envelopes -/

/-- `Efix` restricted to the level window `[A-1, xTop]`: the supremum of `hfix (wA n Jᶜ)` over
levels `u` with `A ≤ u + 1` and `u ≤ xTop` (the `-1` is the level `hprev` needs at site `A`). -/
noncomputable def EfixWin (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (A : ℕ) (U : Array N) : ℝ :=
  (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => if A ≤ u + 1 ∧ u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)

/-- `Esum` restricted to the level window `[A, xTop]`. -/
noncomputable def EsumWin (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (A : ℕ) (U : Array N) : ℝ :=
  (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => if A ≤ u ∧ u ≤ xTop p m n K hK U then
      hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0)

theorem hfix_le_EfixWin {p : ℝ} {m n : ℕ} {J K : Finset (Fin N)} (hK : K.Nonempty)
    (U : Array N) {A u : ℕ} (hu1 : A ≤ u + 1) (hu2 : u ≤ xTop p m n K hK U) :
    hfix (wA p m U n Jᶜ) u ≤ EfixWin p m n J K hK A U := by
  have hmem : u ∈ Finset.range (n + 3) :=
    Finset.mem_range.mpr (lt_of_le_of_lt hu2 (xTop_lt_range p m n K hK U))
  have h1 := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if A ≤ u + 1 ∧ u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) hmem
  have h2 : (if A ≤ u + 1 ∧ u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)
      = hfix (wA p m U n Jᶜ) u := by rw [if_pos ⟨hu1, hu2⟩]
  rwa [h2] at h1

theorem hSum_le_EsumWin {p : ℝ} {m n : ℕ} {J K : Finset (Fin N)} (hK : K.Nonempty)
    (U : Array N) {A u : ℕ} (hu1 : A ≤ u) (hu2 : u ≤ xTop p m n K hK U) :
    hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) ≤ EsumWin p m n J K hK A U := by
  have hmem : u ∈ Finset.range (n + 3) :=
    Finset.mem_range.mpr (lt_of_le_of_lt hu2 (xTop_lt_range p m n K hK U))
  have h1 := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if A ≤ u ∧ u ≤ xTop p m n K hK U then
      hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0) hmem
  have h2 : (if A ≤ u ∧ u ≤ xTop p m n K hK U then
      hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0)
      = hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) := by rw [if_pos ⟨hu1, hu2⟩]
  rwa [h2] at h1

/-! ### 2. `EfixWin` from the window potential bound -/

/-- **`Efix` on the level window.**  If the leader's static potential is at most `H` on
`[A-1, xTop]`, the windowed predictable step envelope is at most `2H + 6`.  This is
`LocGroupQ.Efix_le_of_locmax` with the hypothesis restricted to the window; the only extra input
is `A ≤ M_n^{i₀}` (the leader's running maximum lies above the window's left edge, which holds in
the record-window geometry because all positions are `≥ A`). -/
theorem EfixWin_le_of_window {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {i₀ : Fin N} (hi₀K : i₀ ∈ K)
    (hi₀J : i₀ ∈ Jᶜ) (hmax : Rmax p m n K hK U ≤ (runMax p m U i₀ n).toNat)
    {A : ℕ} (hA : A ≤ (runMax p m U i₀ n).toNat) {H : ℝ} (hH1 : 1 ≤ H)
    (hH : ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n K hK U → hfix (omegaN p m U i₀) v ≤ H) :
    EfixWin p m n J K hK A U ≤ 2 * H + 6 := by
  refine Finset.sup'_le _ _ fun u hu => ?_
  rw [Finset.mem_range] at hu
  by_cases hwin : A ≤ u + 1 ∧ u ≤ xTop p m n K hK U
  · rw [if_pos hwin]
    have hutop : u ≤ xTop p m n K hK U := hwin.2
    have huA : A ≤ u + 1 := hwin.1
    set R : ℕ := (runMax p m U i₀ n).toNat with hR
    have hRtop : R ≤ xTop p m n K hK U := toNat_runMax_le_xTop p m n K hK hi₀K U
    have htopR : xTop p m n K hK U ≤ R + 1 := xTop_le_succ_of_max p m n K hK U hmax
    have hRz : ((R : ℕ) : ℤ) = runMax p m U i₀ n :=
      Int.toNat_of_nonneg (runMax_nonneg_pos p m n i₀ U)
    have hR1 : hfix (wA p m U n Jᶜ) R ≤ H + 2 := by
      have h1 : hfix (wA p m U n Jᶜ) R ≤ hprev (omegaN p m U i₀) R + 2 :=
        hcomp_h_runMax (p := p) (m := m) (U := U) hp hp1 hi₀J
      have h2 : hprev (omegaN p m U i₀) R ≤ H := by
        rcases Nat.eq_zero_or_pos R with hR0 | hRpos
        · rw [hR0, hprev_zero]; exact hH1
        · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hRpos.ne'
          rw [hk, hprev_succ]
          exact hH k (by omega) (by omega)
      linarith
    rcases lt_or_eq_of_le (show u ≤ R + 1 by omega) with hlt | heq
    · rcases lt_or_eq_of_le (show u ≤ R by omega) with hltR | heqR
      · have hz : (u : ℤ) < runMax p m U i₀ n := by
          rw [← hRz]
          exact_mod_cast hltR
        exact le_trans (hcomp_h (p := p) (m := m) (U := U) hp hp1 hi₀J hz)
          (le_trans (hH u huA hutop) (by linarith))
      · subst heqR
        linarith
    · subst heq
      have hw := wA_pos p m U hp n Jᶜ (R + 1)
      have hw1 := one_half_le_wA p m U hp n Jᶜ (R + 1)
      have hstep : hfix (wA p m U n Jᶜ) (R + 1)
          = (1 + (1 - wA p m U n Jᶜ (R + 1)) * hfix (wA p m U n Jᶜ) R)
            / wA p m U n Jᶜ (R + 1) := by
        rw [hfix_eq, hprev_succ]
      have hRnn : 0 ≤ hfix (wA p m U n Jᶜ) R :=
        le_trans zero_le_one (one_le_hfix _ (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) R)
      have hnum : 1 + (1 - wA p m U n Jᶜ (R + 1)) * hfix (wA p m U n Jᶜ) R
          ≤ 1 + hfix (wA p m U n Jᶜ) R := by
        have hle1 : wA p m U n Jᶜ (R + 1) ≤ 1 := wA_le_one p m U hp1 n Jᶜ (R + 1)
        have hle0 : 0 ≤ wA p m U n Jᶜ (R + 1) := le_of_lt hw
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - wA p m U n Jᶜ (R + 1)) hRnn]
      have hfin : (1 + (1 - wA p m U n Jᶜ (R + 1)) * hfix (wA p m U n Jᶜ) R)
            / wA p m U n Jᶜ (R + 1) ≤ 2 * (1 + hfix (wA p m U n Jᶜ) R) := by
        rw [div_le_iff₀ hw]
        nlinarith [hnum, hw, hw1, hRnn]
      rw [hstep]
      linarith
  · rw [if_neg hwin]
    linarith

/-! ### 3. `EsumWin` from the window tail bound -/

/-- **`Esum` on the level window.**  If the leader's static tail sum is at most `G` on
`[A, xTop]`, the windowed predictable product sum is at most `2G`. -/
theorem EsumWin_le_of_window {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {i₀ : Fin N} (hi₀K : i₀ ∈ K)
    (hi₀J : i₀ ∈ Jᶜ) (hmax : Rmax p m n K hK U ≤ (runMax p m U i₀ n).toNat) {A : ℕ}
    {G : ℝ} (hGnn : 0 ≤ G)
    (hG : ∀ u : ℕ, A ≤ u → u ≤ xTop p m n K hK U → Gtail p m U i₀ u (n + 2) ≤ G) :
    EsumWin p m n J K hK A U ≤ 2 * G := by
  set R : ℕ := (runMax p m U i₀ n).toNat with hR
  have hRz : ((R : ℕ) : ℤ) = runMax p m U i₀ n :=
    Int.toNat_of_nonneg (runMax_nonneg_pos p m n i₀ U)
  have hR1 : R + 1 ≤ n + 2 := by
    have h1 : runMax p m U i₀ n ≤ (n : ℤ) := runMax_le_time p m n i₀ U
    have h2 : R ≤ n := by
      have h3 : ((R : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hRz]; exact h1
      exact_mod_cast h3
    omega
  have htopR : xTop p m n K hK U ≤ R + 1 := xTop_le_succ_of_max p m n K hK U hmax
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
          ≤ 2 * Gtail p m U i₀ u (n + 2) :=
        hSum_le_two_Gtail (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i₀) (u := u)
          (x := xTop p m n K hK U) (R := R) (K := n + 2) huR htopR hcomp hR1
      have h2 : Gtail p m U i₀ u (n + 2) ≤ G := hG u hwin.1 hwin.2
      exact le_trans h1 (by linarith)
    · have huEq : u = R + 1 := by omega
      have hempty : Finset.Ico u (xTop p m n K hK U) = ∅ := by
        rw [Finset.Ico_eq_empty_iff]
        omega
      have hzero : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) = 0 := by
        rw [hSum, hempty, Finset.sum_empty]
      have hGpos : 0 ≤ 2 * G := by
        have h1 : (1 : ℝ) ≤ Gtail p m U i₀ u (n + 2) := by
          rw [Gtail]; linarith [Gsum_nonneg hp.le hp1 m U i₀ u (n + 2)]
        linarith [hG u hwin.1 hwin.2]
      rw [hzero]
      exact hGpos
  · rw [if_neg hwin]
    have hGpos : 0 ≤ 2 * G := by linarith
    exact hGpos

/-! ### 4. The windowed good event -/

/-- The windowed predictable good event: separation together with the two *windowed* envelope
bounds.  On the record window this is what `(locmax)` on `[r-(T+3)L, r+(T+3)L]` discharges. -/
def GoodWWin (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (B : ℝ) (A : ℕ)
    (U : Array N) : Prop :=
  SepSet p m n I J U ∧
    EfixWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B ∧
    EsumWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B

/-- **The windowed `GoodW` from the window `(locmax)` hypotheses.**  `hA` says that every walker
of `I` has running maximum at least `A` (true on the record window, where every position is `≥ A`);
`hH`, `hG` are the windowed potential and tail bounds that `(locmax)` provides. -/
theorem goodWWin_of_locmax {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {A : ℕ} {H G : ℝ} (hH1 : 1 ≤ H) (hGnn : 0 ≤ G)
    (hA : ∀ i ∈ I, A ≤ (runMax p m U i n).toNat)
    (hH : ∀ i ∈ I, ∀ v : ℕ, A ≤ v + 1 →
      v ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U →
      hfix (omegaN p m U i) v ≤ H)
    (hG : ∀ i ∈ I, ∀ u : ℕ, A ≤ u →
      u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U →
      Gtail p m U i u (n + 2) ≤ G) :
    GoodWWin p m n I J hI (max (2 * H + 6) (2 * G)) A U := by
  have hK : (I ∪ J).Nonempty := hJ.mono Finset.subset_union_right
  obtain ⟨i₀, hi₀, hlead⟩ := exists_leader_in_I I J hI hJ hsep
  have hi₀J : i₀ ∈ Jᶜ := Finset.mem_compl.mpr (Finset.disjoint_left.mp hid hi₀)
  have hmax := Rmax_le_leader I J hI hi₀ hlead
  refine ⟨hsep, ?_, ?_⟩
  · refine le_trans (EfixWin_le_of_window (N := N) hp0.le hp1 (hK := hK) (U := U)
      (A := A) (Finset.mem_union_left _ hi₀) hi₀J hmax (hA i₀ hi₀) hH1 ?_) (le_max_left _ _)
    · intro v hv1 hv2
      exact hH i₀ hi₀ v hv1 hv2
  · refine le_trans (EsumWin_le_of_window (N := N) hp0 hp1 (hK := hK) (U := U)
      (A := A) (Finset.mem_union_left _ hi₀) hi₀J hmax hGnn ?_) (le_max_right _ _)
    · intro u hu1 hu2
      exact hG i₀ hi₀ u hu1 hu2

end SiteWindow

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ

variable {N : ℕ}

/-! ### 5. Predictability of the windowed envelopes

The windowed good event must be a `posFilt n`-measurable truncation event, exactly like
`LocGroupQ.measurableSet_goodW_posFilt`.  The proofs are the same as `measurable_Efix`,
`measurable_Esum` with the extra condition `A ≤ u + 1`. -/

theorem measurable_EfixWin (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (A : ℕ) : Measurable[posFilt N p m n] (fun U : Array N => EfixWin p m n J K hK A U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have htop := measurable_xTop_posFilt (N := N) p m n K hK
  have heq : (fun U : Array N => EfixWin p m n J K hK A U)
      = (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun u (U : Array N) => if A ≤ u + 1 ∧ u ≤ xTop p m n K hK U then
          hfix (wA p m U n Jᶜ) u else 0) := by
    funext U
    exact (Finset.sup'_apply _ (fun u (U : Array N) => if A ≤ u + 1 ∧ u ≤ xTop p m n K hK U
      then hfix (wA p m U n Jᶜ) u else 0) U).symm
  rw [heq]
  refine Finset.measurable_sup' _ (fun u _ => ?_)
  refine Measurable.ite ?_ (SwarmM3.measurable_hfix_wA_posFilt p m n Jᶜ u) measurable_const
  by_cases h : A ≤ u + 1
  · simp only [h, true_and]
    exact measurableSet_le measurable_const htop
  · simp only [h, false_and]
    exact MeasurableSet.empty

theorem measurable_hSum_wA (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (u : ℕ) : Measurable[posFilt N p m n] (fun U : Array N =>
      hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have htop := measurable_xTop_posFilt (N := N) p m n K hK
  have heq : (fun U : Array N => hSum (wA p m U n Jᶜ) u (xTop p m n K hK U))
      = fun U => ∑ z ∈ Finset.Ico u (n + 2),
          (if z < xTop p m n K hK U then
            ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0) := by
    funext U
    exact hSum_eq_sum_indicator (u := u) (x := xTop p m n K hK U) (M := n + 2)
      (xTop_le p m n K hK U)
  rw [heq]
  refine Finset.measurable_sum _ (fun z _ => ?_)
  exact (Finset.measurable_prod _ (fun v _ => measurable_rq_wA p m n Jᶜ v)).ite
    (measurableSet_lt measurable_const htop) measurable_const

theorem measurable_EsumWin (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (A : ℕ) : Measurable[posFilt N p m n] (fun U : Array N => EsumWin p m n J K hK A U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have htop := measurable_xTop_posFilt (N := N) p m n K hK
  have hinner : ∀ u : ℕ, Measurable (fun U : Array N =>
      if A ≤ u ∧ u ≤ xTop p m n K hK U then
        hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0) := by
    intro u
    have hterm : Measurable (fun U : Array N => hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)) :=
      measurable_hSum_wA p m n J K hK u
    refine Measurable.ite ?_ hterm measurable_const
    by_cases h : A ≤ u
    · simp only [h, true_and]
      exact measurableSet_le measurable_const htop
    · simp only [h, false_and]
      exact MeasurableSet.empty
  have heq : (fun U : Array N => EsumWin p m n J K hK A U)
      = (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun u (U : Array N) => if A ≤ u ∧ u ≤ xTop p m n K hK U then
          hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0) := by
    funext U
    exact (Finset.sup'_apply _ (fun u (U : Array N) => if A ≤ u ∧ u ≤ xTop p m n K hK U then
      hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0) U).symm
  rw [heq]
  exact Finset.measurable_sup' _ (fun u _ => hinner u)

theorem measurableSet_goodWWin (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (B : ℝ) (A : ℕ) :
    MeasurableSet[posFilt N p m n] {U : Array N | GoodWWin p m n I J hI B A U} := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have h1 : MeasurableSet {U : Array N | SepSet p m n I J U} := measurableSet_sepSet p m n I J
  have h2 : MeasurableSet {U : Array N |
      EfixWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B} :=
    measurableSet_le (measurable_EfixWin p m n J (I ∪ J) _ A) measurable_const
  have h3 : MeasurableSet {U : Array N |
      EsumWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B} :=
    measurableSet_le (measurable_EsumWin p m n J (I ∪ J) _ A) measurable_const
  exact h1.inter (h2.inter h3)

end SiteWindow
