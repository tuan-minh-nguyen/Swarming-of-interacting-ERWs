/-
# The source's `(meet)` step: from the fluid `(meet)` deadline to `JoinRuleFrom`

The paper (`main_1d_revised.tex`, proof of Proposition `tight`, the paragraph
after `(coincide)`) derives the meeting rule from the fluid `(meet)` inequality

  `t - s <= b (max_i x_i(s) - min_i x_i(s))`

for a *strictly separated* leading group as follows:

> If `s + b (max x(s) - min x(s)) < T`, there exist `u ∈ (s, s + b(max x(s) - min x(s))]`
> and `j ∉ A` such that `x_j(u) = R(u)`.  Indeed, otherwise continuity would allow us to
> choose `t > s + b(max x(s) - min x(s))` with `t < T` such that strict separation holds
> on `[s,t]`, contrary to `(meet)`.  At the first such joining time, every index formerly
> in `A` still belongs to the leading set, so that set increases strictly.

This file formalises exactly that paragraph.

* `MeetBound x s₀ b T` is the *scalar* fluid `(meet)` statement: on any interval
  `[s,v] ⊂ [s₀,T]` on which the leading group `A = leaders(·,s)` stays strictly above its
  complement, `v - s ≤ b * fluidGap (x s)`.  It is a statement about the fluid positions
  only — no potential `W`, no `LeaderDecay`/`LeaderStart`/`GroupLower`, no records.
  `M2Meet.meet_of_grid_bounds` (`MeetPassage.lean`) produces it, with `b = 2 C^2`, from the
  finite-scale sharp lattice bounds at every scale.
* `leaderPersist_of_stickyOn` — `(coincide)` (`StickyOn`) plus continuity gives the
  paper's leader persistence.
* `reaches_of_meetBound` — **the first-contact time**: with `MeetBound`, `StickyOn` and
  continuity, from a proper leading set at `s` before the deadline there is
  `u ∈ [s, deadline]` and an outsider `k ∉ leaders(·,s)` whose fluid position equals the
  fluid maximum at `u`.  The contact time is the infimum of the failure set and the outsider
  is selected *at* that time, by finite maximisation — it is not prescribed in advance.
* `joinRuleFrom_of_meetBound` — the paper's `JoinRuleFrom` with the scalar `b`, obtained by
  the existing reduction `FluidJoin.joinRuleFrom_of_reaches`.

No probability, no stationarity, no assumed separation in the consumer: the separation
interval is an internal object of the proof.  Nothing here is a probability estimate;
`MeetBound` itself is a named remaining premise unless the finite-scale `MeetPassage` input
is supplied at every scale.
-/
import Swarm.MeetPassage

open Filter Topology Finset
open FluidMerge
open scoped BigOperators BoundedContinuousFunction

namespace M2Meet

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The scalar fluid `(meet)` bound -/

/-- The source's `(meet)` in scalar fluid form: while the leading group at time `s` stays
strictly above its complement, the elapsed fluid time is at most `b` diameters. -/
def MeetBound (x : ι → ℝ → ℝ) (s₀ b T : ℝ) : Prop :=
  ∀ (A : Finset ι) (hA : A.Nonempty) (s v : ℝ),
    s₀ ≤ s → s ≤ v → v ≤ T → A = leaders (fun i => x i s) → A ≠ univ →
    (∀ r ∈ Set.Icc s v, ∀ i ∈ A, ∀ j ∈ univ \ A, x j r < x i r) →
    v - s ≤ b * fluidGap (fun i => x i s)

/-! ## 2. Leader persistence from `(coincide)` -/

/-- `StickyOn` plus continuity give the paper's leader persistence: a coordinate maximal at
`s` stays maximal at every later time of the window.  (Same statement as the existing
`Coalesce.leaderPersist_of_sticky`.) -/
theorem leaderPersist_of_stickyOn {x : ι → ℝ → ℝ} {s₀ T : ℝ}
    (hsticky : StickyOn x s₀ T) (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T)) :
    ∀ s t, s₀ ≤ s → s ≤ t → t ≤ T → leaders (fun i => x i s) ⊆ leaders (fun i => x i t) := by
  intro s t hs₀ hst htT i hi
  have hi_s : x i s = fluidMax (fun k => x k s) := mem_leaders.mp hi
  refine mem_leaders.mpr (le_antisymm (Finset.le_sup' (fun k => x k t) (mem_univ i)) ?_)
  by_contra hnot
  have hlt : x i t < fluidMax (fun k => x k t) := lt_of_not_ge hnot
  have hlt' : x i t < univ.sup' univ_nonempty (fun k => x k t) := hlt
  obtain ⟨j, -, hj⟩ := Finset.lt_sup'_iff univ_nonempty |>.mp hlt'
  have hj_le_s : x j s ≤ x i s := by
    rw [hi_s]
    exact Finset.le_sup' (fun k => x k s) (mem_univ j)
  set w : ℝ → ℝ := fun u => x j u - x i u with hw
  have hcont_w : ContinuousOn w (Set.Icc s t) := by
    have hsub : Set.Icc s t ⊆ Set.Icc s₀ T := fun u hu =>
      ⟨le_trans hs₀ hu.1, by linarith [hu.2]⟩
    have hIj : ContinuousOn (x j) (Set.Icc s t) := (hcont j).mono hsub
    have hIi : ContinuousOn (x i) (Set.Icc s t) := (hcont i).mono hsub
    have h : ContinuousOn (fun u => x j u - x i u) (Set.Icc s t) := hIj.sub hIi
    simpa only [hw] using h
  have hws : w s ≤ 0 := by
    simp only [hw]
    linarith
  have hwt : 0 < w t := by
    simp only [hw]
    linarith
  have hmem := intermediate_value_Icc hst hcont_w
    (Set.mem_Icc.mpr ⟨hws, le_of_lt hwt⟩ : (0 : ℝ) ∈ Set.Icc (w s) (w t))
  obtain ⟨u, hu, hu0⟩ := hmem
  have heq : x j u = x i u := by
    have hzero : w u = 0 := hu0
    simp only [hw] at hzero
    linarith
  have hsticky' := hsticky j i u t (le_trans hs₀ hu.1) hu.2 htT heq
  linarith [hwt]

/-! ## 3. The first-contact time -/

/-- **The source's first-contact step.**  If the leading group `A` at `s` is proper, the
candidate deadline `s + b Δ(s)` is below `T`, and `(meet)` holds with constant `b ≥ 0`, then
some outsider reaches the fluid maximum no later than the deadline.  The contact time is the
infimum of the set where the complement catches up with the leader level; the outsider is
selected at that time, not prescribed. -/
theorem reaches_of_meetBound {x : ι → ℝ → ℝ} {s₀ b T : ℝ}
    (hsticky : StickyOn x s₀ T) (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T))
    (hmeet : MeetBound x s₀ b T) (hb : 0 ≤ b)
    {s : ℝ} (hs₀ : s₀ ≤ s) (hproper : leaders (fun i => x i s) ≠ univ)
    (hdeadline : s + b * fluidGap (fun i => x i s) < T) :
    ∃ u, s ≤ u ∧ u ≤ s + b * fluidGap (fun i => x i s) ∧
      ∃ k, k ∉ leaders (fun i => x i s) ∧ x k u = fluidMax (fun i => x i u) := by
  classical
  let A : Finset ι := leaders (fun i => x i s)
  let J : Finset ι := univ \ A
  have hAleaders : A = leaders (fun i => x i s) := rfl
  have hmemA : ∀ i, i ∈ A ↔ x i s = fluidMax (fun k => x k s) := by
    intro i
    rw [hAleaders]
    exact mem_leaders
  have hAne : A ≠ univ := hproper
  have hApos : A.Nonempty := leaders_nonempty _
  have hJ : J.Nonempty := by
    refine Finset.sdiff_nonempty.mpr ?_
    intro hsub
    exact hproper (Finset.eq_univ_iff_forall.mpr (fun i => hsub (mem_univ i)))
  have hA2 : A.Nonempty := hApos
  obtain ⟨i₀, hi₀⟩ := hA2
  have hLeq : ∀ (i : ι), i ∈ A → ∀ u, s ≤ u → u ≤ T → x i u = x i₀ u := by
    intro i hi u hsu huT
    refine hsticky i i₀ s u hs₀ hsu huT ?_
    rw [(hmemA i).mp hi, (hmemA i₀).mp hi₀]
  let L : ℝ → ℝ := fun u => x i₀ u
  let M : ℝ → ℝ := fun u => J.sup' hJ (fun j => x j u)
  have hsT : s ≤ T := by linarith [hdeadline, mul_nonneg hb (fluidGap_nonneg (fun i => x i s))]
  have hLcont : ContinuousOn L (Set.Icc s T) :=
    (hcont i₀).mono (Set.Icc_subset_Icc hs₀ le_rfl)
  have hMcont : ContinuousOn M (Set.Icc s T) := by
    have h := ContinuousOn.finset_sup' (s := J) (t := Set.Icc s T)
      (f := fun j (u : ℝ) => x j u) hJ
      (fun j _ => (hcont j).mono (Set.Icc_subset_Icc hs₀ le_rfl))
    have hh : (J.sup' hJ (fun j (u : ℝ) => x j u)) = M := by
      funext u
      exact Finset.sup'_apply hJ (fun j (v : ℝ) => x j v) u
    rwa [hh] at h
  have hLs : L s = fluidMax (fun i => x i s) := (hmemA i₀).mp hi₀
  have hMs : M s < L s := by
    rw [hLs, Finset.sup'_lt_iff hJ]
    intro j hj
    have hjA : j ∉ A := (Finset.mem_sdiff.mp hj).2
    have hle : x j s ≤ fluidMax (fun i => x i s) :=
      Finset.le_sup' (fun i => x i s) (mem_univ j)
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hjA ((hmemA j).mpr heq)
  -- the failure set: the complement has caught up with the leader level
  let P : ℝ → Prop := fun u => u ∈ Set.Icc s T ∧ L u ≤ M u
  let S : Set ℝ := {u | P u}
  have hSmem : ∀ u, u ∈ S ↔ P u := fun u => Iff.rfl
  have hSI : ∀ u, u ∈ S → u ∈ Set.Icc s T := by
    intro u hu
    exact ((hSmem u).mp hu).1
  have hSg : ∀ u, u ∈ S → L u ≤ M u := by
    intro u hu
    exact ((hSmem u).mp hu).2
  have hSep_of_notmem : ∀ r, r ∈ Set.Icc s T → r ∉ S → ∀ i ∈ A, ∀ j ∈ J, x j r < x i r := by
    intro r hr hnr i hi j hj
    have h1 : ¬ (L r ≤ M r) := fun hc => hnr ((hSmem r).mpr ⟨hr, hc⟩)
    have h1' : M r < L r := not_le.mp h1
    have h2 : x j r ≤ M r := Finset.le_sup' (fun j => x j r) hj
    have h3 : L r = x i r := (hLeq i hi r hr.1 hr.2).symm
    rw [h3] at h1'
    linarith
  have hSne : S.Nonempty := by
    by_contra hempty
    have hnotmem : ∀ r, r ∈ Set.Icc s T → r ∉ S := fun r hr hmem => hempty ⟨r, hmem⟩
    have hall : ∀ r ∈ Set.Icc s T, ∀ i ∈ A, ∀ j ∈ J, x j r < x i r := by
      intro r hr i hi j hj
      exact hSep_of_notmem r hr (hnotmem r hr) i hi j hj
    have hbound := hmeet A hApos s T hs₀ hsT le_rfl hAleaders hAne hall
    linarith [hdeadline, mul_nonneg hb (fluidGap_nonneg (fun i => x i s))]
  have hbdd : BddBelow S := ⟨s, fun u hu => (hSI u hu).1⟩
  set u₀ : ℝ := sInf S with hu₀def
  have hsu₀ : s ≤ u₀ := by
    rw [hu₀def]
    exact le_csInf hSne (fun u hu => (hSI u hu).1)
  have hu₀T : u₀ ≤ T := by
    obtain ⟨u, hu⟩ := hSne
    rw [hu₀def]
    exact le_trans (csInf_le hbdd hu) (hSI u hu).2
  -- continuity at the contact time, in a usable form
  have hball : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ Set.Icc s T, |u - u₀| < δ →
      |(M u - L u) - (M u₀ - L u₀)| < ε := by
    intro ε hε
    have hcontAt : ContinuousWithinAt (fun u => M u - L u) (Set.Icc s T) u₀ :=
      (hMcont.sub hLcont) u₀ ⟨hsu₀, hu₀T⟩
    rw [Metric.continuousWithinAt_iff'] at hcontAt
    have hev := hcontAt ε hε
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
    obtain ⟨δ, hδ, hsub⟩ := hev
    refine ⟨δ, hδ, fun u hu hd => ?_⟩
    have hmem : u ∈ Metric.ball u₀ δ := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hd
    have hthis := hsub ⟨hmem, hu⟩
    simpa only [Set.mem_setOf_eq, Real.dist_eq] using hthis
  -- members of the failure set are arbitrarily close to its infimum from above
  have hnear : ∀ ε > 0, ∃ u ∈ S, u₀ ≤ u ∧ u < u₀ + ε := by
    intro ε hε
    have hlt : sInf S < u₀ + ε := by rw [hu₀def]; linarith
    obtain ⟨u, huS, hltu⟩ := exists_lt_of_csInf_lt hSne hlt
    exact ⟨u, huS, csInf_le hbdd huS, hltu⟩
  -- `g u₀ ≥ 0`: the complement cannot be strictly behind at the contact time
  have hge : L u₀ ≤ M u₀ := by
    by_contra hcon
    have hneg : M u₀ - L u₀ < 0 := by
      have : M u₀ < L u₀ := not_le.mp hcon
      linarith
    obtain ⟨δ, hδ, hball'⟩ := hball _ (by linarith : 0 < -(M u₀ - L u₀))
    obtain ⟨u, huS, huu₀, hltu⟩ := hnear δ hδ
    have huI : u ∈ Set.Icc s T := hSI u huS
    have hd : |u - u₀| < δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hkey := hball' u huI hd
    rw [abs_lt] at hkey
    have hle : L u ≤ M u := hSg u huS
    linarith [hkey.2]
  -- hence `u₀ > s`, so there are points just below the contact time
  have hsu₀' : s < u₀ := by
    rcases lt_or_eq_of_le hsu₀ with h | h
    · exact h
    · exfalso
      have : L u₀ ≤ M u₀ := hge
      rw [← h] at this
      linarith [hMs]
  have hnearL : ∀ ε > 0, ∃ u, u ∈ Set.Icc s T ∧ u < u₀ ∧ u₀ - ε < u := by
    intro ε hε
    refine ⟨max s (u₀ - ε / 2), ⟨le_max_left _ _, ?_⟩, ?_, ?_⟩
    · exact max_le hsT (by linarith)
    · exact max_lt hsu₀' (by linarith)
    · have h1 : u₀ - ε < u₀ - ε / 2 := by linarith
      exact lt_of_lt_of_le h1 (le_max_right _ _)
  -- `g u₀ ≤ 0`: left-continuity of the separation condition
  have hle' : M u₀ ≤ L u₀ := by
    by_contra hcon
    have hpos : 0 < M u₀ - L u₀ := by
      have : L u₀ < M u₀ := not_le.mp hcon
      linarith
    obtain ⟨δ, hδ, hball'⟩ := hball _ hpos
    obtain ⟨u, huI, hltu₀, hgt⟩ := hnearL δ hδ
    have hnotmem : u ∉ S := by
      intro hmem
      have h1 : sInf S ≤ u := csInf_le hbdd hmem
      have h2 : u₀ ≤ u := hu₀def ▸ h1
      linarith
    have hsep := hSep_of_notmem u huI hnotmem
    have hgu : (fun v => M v - L v) u < 0 := by
      have h1 : ¬ (L u ≤ M u) := fun hc => hnotmem ((hSmem u).mpr ⟨huI, hc⟩)
      have h2 : M u < L u := not_le.mp h1
      linarith
    have hd : |u - u₀| < δ := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hkey := hball' u huI hd
    rw [abs_lt] at hkey
    linarith [hkey.1]
  -- the deadline bound on `u₀`
  have hu₀d : u₀ ≤ s + b * fluidGap (fun i => x i s) := by
    by_contra hcon
    have hlt : s + b * fluidGap (fun i => x i s) < u₀ := lt_of_not_ge hcon
    set d : ℝ := b * fluidGap (fun i => x i s) with hd
    have hdnn : 0 ≤ d := mul_nonneg hb (fluidGap_nonneg _)
    set v : ℝ := (max s (s + d) + u₀) / 2 with hvdef
    have hmlt : max s (s + d) < u₀ := max_lt (by linarith) hlt
    have hsv : s ≤ v := by
      rw [hvdef]
      have h1 : s ≤ max s (s + d) := le_max_left _ _
      linarith
    have hvu : v < u₀ := by rw [hvdef]; linarith
    have hdv : d < v - s := by
      rw [hvdef]
      have h1 : s + d ≤ max s (s + d) := le_max_right _ _
      linarith
    have hvT : v ≤ T := le_of_lt (lt_of_lt_of_le hvu hu₀T)
    have hall : ∀ r ∈ Set.Icc s v, ∀ i ∈ A, ∀ j ∈ J, x j r < x i r := by
      intro r hr i hi j hj
      have hrT : r ∈ Set.Icc s T := ⟨hr.1, le_trans hr.2 hvT⟩
      refine hSep_of_notmem r hrT ?_ i hi j hj
      intro hmem
      have h1 : u₀ ≤ r := csInf_le hbdd hmem
      have h2 : r ≤ v := hr.2
      linarith
    have hb2 := hmeet A hApos s v hs₀ hsv hvT hAleaders hAne hall
    linarith
  -- the outsider at the contact time
  have hcontact : M u₀ = L u₀ := le_antisymm hle' hge
  obtain ⟨k, hkJ, hkval⟩ := Finset.exists_mem_eq_sup' hJ (fun j => x j u₀)
  have hkL : x k u₀ = L u₀ := by
    rw [← hkval]
    exact hcontact
  have hkA : k ∉ A := (Finset.mem_sdiff.mp hkJ).2
  have hmax : x k u₀ = fluidMax (fun i => x i u₀) := by
    refine le_antisymm (Finset.le_sup' (fun i => x i u₀) (mem_univ k)) ?_
    refine Finset.sup'_le univ_nonempty _ (fun i _ => ?_)
    by_cases hiA : i ∈ A
    · rw [hLeq i hiA u₀ hsu₀ hu₀T]
      exact le_of_eq hkL.symm
    · have hiJ : i ∈ J := Finset.mem_sdiff.mpr ⟨mem_univ i, hiA⟩
      calc x i u₀ ≤ M u₀ := Finset.le_sup' (fun j => x j u₀) hiJ
        _ = L u₀ := hcontact
        _ = x k u₀ := hkL.symm
  exact ⟨u₀, hsu₀, hu₀d, k, hkA, hmax⟩

/-! ## 4. `JoinRuleFrom` from the scalar `(meet)` bound -/

/-- **The source's step 6.**  `(coincide)` (`StickyOn`), continuity, and the scalar fluid
`(meet)` bound at constant `b ≥ 0` give the meeting rule `JoinRuleFrom` at the same constant.
No separation is assumed by the consumer, no potential object appears, and the newcomer at
each step is produced by `reaches_of_meetBound`. -/
theorem joinRuleFrom_of_meetBound {x : ι → ℝ → ℝ} {s₀ b T : ℝ}
    (hsticky : StickyOn x s₀ T) (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T))
    (hmeet : MeetBound x s₀ b T) (hb : 0 ≤ b) :
    JoinRuleFrom x s₀ b T := by
  intro s hs₀ hproper hdeadline
  obtain ⟨u, hsu, hu, k, hknot, hkmax⟩ :=
    reaches_of_meetBound hsticky hcont hmeet hb hs₀ hproper hdeadline
  have huT : u ≤ T := le_of_lt (lt_of_le_of_lt hu hdeadline)
  have hsub : leaders (fun i => x i s) ⊆ leaders (fun i => x i u) :=
    leaderPersist_of_stickyOn hsticky hcont s u hs₀ hsu huT
  refine ⟨u, hsu, hu, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩⟩
  intro heq
  exact hknot (heq ▸ mem_leaders.mpr hkmax)

end M2Meet
