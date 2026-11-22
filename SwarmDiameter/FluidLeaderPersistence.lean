import Swarm.FluidJoinCoalesce
import Swarm.FluidGeometryLight
import Swarm.MeetJoin

open Finset Set
open FluidMerge FluidJoin

namespace Swarming.Diameter

set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- A group lies strictly above every path outside the group. -/
def StrictTop (x : ι → ℝ → ℝ) (A : Finset ι) (t : ℝ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ Aᶜ, x j t < x i t

/-- An upper bound on growth of the distance from a separated upper group
to an outside path, on each closed interval of strict separation. -/
def TopGroupComparison (x : ι → ℝ → ℝ) (s₀ C T : ℝ) : Prop :=
  ∀ (A : Finset ι) (hA : A.Nonempty) (s t : ℝ), s₀ ≤ s → s ≤ t → t ≤ T →
    (∀ u ∈ Set.Icc s t, StrictTop x A u) →
    ∀ j ∈ Aᶜ, A.sup' hA (fun i => x i t) - x j t ≤
      C * (A.sup' hA (fun i => x i s) - x j s)

omit [Nonempty ι] in
private theorem isOpen_strictTop {x : ι → ℝ → ℝ} (hc : ∀ i, Continuous (x i)) (A : Finset ι) :
    IsOpen {t | StrictTop x A t} := by
  have he : {t | StrictTop x A t} =
      ⋂ i ∈ A, ⋂ j ∈ Aᶜ, {t | x j t < x i t} := by ext t; simp [StrictTop]
  rw [he]
  exact isOpen_biInter_finset fun i _ => isOpen_biInter_finset fun j _ => isOpen_lt (hc j) (hc i)

omit [Nonempty ι] in
private theorem strictTop_subset_of_unequal {x : ι → ℝ → ℝ} {A : Finset ι} (hA : A.Nonempty)
    {t : ℝ} (hsep : StrictTop x A t) {i j : ι} (hi : i ∈ A) (hj : j ∈ A)
    (hne : x i t ≠ x j t) :
    ∃ B : Finset ι, B.Nonempty ∧ B ⊆ A ∧ B.card < A.card ∧ StrictTop x B t := by
  let M := A.sup' hA (fun i => x i t)
  let B := A.filter fun i => x i t = M
  obtain ⟨k, hk, hM⟩ := Finset.exists_mem_eq_sup' hA (fun i => x i t)
  have hB : B.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hM.symm⟩⟩
  have hsub : B ⊆ A := Finset.filter_subset _ _
  have hne' : B ≠ A := by
    intro he
    have h₁ := (Finset.mem_filter.mp (show i ∈ B from he.symm ▸ hi)).2
    have h₂ := (Finset.mem_filter.mp (show j ∈ B from he.symm ▸ hj)).2
    exact hne (h₁.trans h₂.symm)
  refine ⟨B, hB, hsub, Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩), ?_⟩
  intro l hl q hq
  have hltop := (Finset.mem_filter.mp hl).2
  by_cases hqA : q ∈ A
  · rw [hltop]
    refine lt_of_le_of_ne (Finset.le_sup' (fun i => x i t) hqA) ?_
    intro he
    exact (Finset.mem_compl.mp hq) (Finset.mem_filter.mpr ⟨hqA, he⟩)
  · exact hsep l (hsub hl) q (Finset.mem_compl.mpr hqA)

omit [Nonempty ι] in
private theorem equal_on_of_top_comparison {x : ι → ℝ → ℝ} {s₀ C T : ℝ}
    (hc : ∀ i, Continuous (x i)) (hC : 0 ≤ C) (hcomp : TopGroupComparison x s₀ C T)
    {A : Finset ι} (hA : A.Nonempty) {s t : ℝ} (hs₀ : s₀ ≤ s) (htT : t ≤ T)
    (hsame : ∀ i ∈ A, ∀ j ∈ A, x i s = x j s)
    (hsep : ∀ u ∈ Set.Icc s t, StrictTop x A u) :
    ∀ u ∈ Set.Icc s t, ∀ i ∈ A, ∀ j ∈ A, x i u = x j u := by
  classical
  intro u hu i hi j hj
  by_contra hne
  let P (k : ℕ) : Prop := ∃ B : Finset ι, B.Nonempty ∧ B ⊆ A ∧ B.card = k ∧
    B.card < A.card ∧ ∃ v ∈ Set.Icc s t, StrictTop x B v
  have hP : ∃ k, P k := by
    obtain ⟨B, hB, hsub, hlt, hBsep⟩ := strictTop_subset_of_unequal hA (hsep u hu) hi hj hne
    exact ⟨B.card, B, hB, hsub, rfl, hlt, u, hu, hBsep⟩
  obtain ⟨B, hB, hBA, hcard, hBcard, v, hv, hvsep⟩ := Nat.find_spec hP
  let F : Set ℝ := Set.Icc s v ∩ {u | StrictTop x B u}ᶜ
  have hF : IsCompact F := isCompact_Icc.inter_right (isOpen_strictTop hc B).isClosed_compl
  have hsF : s ∈ F := by
    refine ⟨⟨le_rfl, hv.1⟩, ?_⟩
    intro hsB
    obtain ⟨l, hl⟩ := hB
    obtain ⟨k, hk, hkB⟩ : ∃ k, k ∈ A ∧ k ∉ B := by
      by_contra! h
      exact (not_le_of_gt hBcard) (Finset.card_le_card h)
    exact (hsB l hl k (Finset.mem_compl.mpr hkB)).ne (hsame k hk l (hBA hl))
  obtain ⟨a, ha, hlast⟩ := hF.exists_isGreatest ⟨s, hsF⟩
  have hav : a < v := by
    refine lt_of_le_of_ne ha.1.2 ?_
    intro he
    exact ha.2 (he ▸ hvsep)
  have hsep' (r : ℝ) (hr : r ∈ Set.Ioc a v) : StrictTop x B r := by
    by_contra h
    exact (not_le_of_gt hr.1) (hlast ⟨⟨ha.1.1.trans hr.1.le, hr.2⟩, h⟩)
  have htie (r : ℝ) (hr : r ∈ Set.Ioc a v) (l : ι) (hl : l ∈ B) (k : ι) (hk : k ∈ B) :
      x l r = x k r := by
    by_contra h
    obtain ⟨D, hD, hDB, hlt, hDsep⟩ := strictTop_subset_of_unequal hB (hsep' r hr) hl hk h
    have hd : P D.card :=
      ⟨D, hD, hDB.trans hBA, rfl, hlt.trans hBcard, r,
        ⟨ha.1.1.trans hr.1.le, hr.2.trans hv.2⟩, hDsep⟩
    exact (not_le_of_gt (hlt.trans_eq hcard)) (Nat.find_min' hP hd)
  have ha_closure : a ∈ closure (Set.Ioc a v) := by
    rw [closure_Ioc hav.ne]
    exact ⟨le_rfl, hav.le⟩
  have htie₀ (l : ι) (hl : l ∈ B) (k : ι) (hk : k ∈ B) : x l a = x k a := by
    have hsub : Set.Ioc a v ⊆ {r | x l r = x k r} := fun r hr => htie r hr l hl k hk
    exact (closure_minimal hsub (isClosed_eq (hc l) (hc k))) ha_closure
  have hnot : ¬ StrictTop x B a := ha.2
  unfold StrictTop at hnot
  push Not at hnot
  obtain ⟨l, hl, k, hk, hkl⟩ := hnot
  let Z (r : ℝ) := B.sup' hB (fun i => x i r)
  have hZ : Continuous Z := Continuous.finset_sup'_apply hB (fun i _ => hc i)
  have hZa : Z a ≤ x k a := by
    apply Finset.sup'_le
    intro l' hl'
    exact (htie₀ l' hl' l hl).trans_le hkl
  have hZv : x k v < Z v :=
    (hvsep l hl k hk).trans_le (Finset.le_sup' (fun j => x j v) hl)
  have hsub : Set.Ioc a v ⊆ {r | Z v - x k v ≤ C * (Z r - x k r)} := by
    intro r hr
    exact hcomp B hB r v (hs₀.trans (ha.1.1.trans hr.1.le)) hr.2 (hv.2.trans htT)
      (fun r' hr' => hsep' r' ⟨hr.1.trans_le hr'.1, hr'.2⟩) k hk
  have hclosed : IsClosed {r | Z v - x k v ≤ C * (Z r - x k r)} :=
    isClosed_le continuous_const ((hZ.sub (hc k)).const_mul C)
  have hfinal : Z v - x k v ≤ C * (Z a - x k a) := (closure_minimal hsub hclosed) ha_closure
  linarith only [hZv, hfinal, mul_nonpos_of_nonneg_of_nonpos hC (sub_nonpos.mpr hZa)]

/-- The separated-group comparison prevents the paths at the top of
the limiting family from leaving the set of leaders. -/
theorem leaderPersist_of_topComparison {x : ι → ℝ → ℝ} {s₀ C T : ℝ}
    (hc : ∀ i, Continuous (x i)) (hC : 0 ≤ C) (hcomp : TopGroupComparison x s₀ C T) :
    LeaderPersist x s₀ T := by
  classical
  intro s t hs₀ hst htT i hi
  let F : Set ℝ := Set.Icc s t ∩ {r | x i r = fluidMax (fun j => x j r)}
  have hMax : Continuous (fun r => fluidMax (fun j => x j r)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun j _ => hc j)
  have hF : IsCompact F := isCompact_Icc.inter_right (isClosed_eq (hc i) hMax)
  obtain ⟨a, ha, hlast⟩ := hF.exists_isGreatest ⟨s, ⟨⟨le_rfl, hst⟩, mem_leaders.mp hi⟩⟩
  by_contra hn
  have hat : a < t := by
    refine lt_of_le_of_ne ha.1.2 ?_
    intro he
    exact hn (mem_leaders.mpr (he ▸ ha.2))
  let A := leaders (fun j => x j a)
  have hA : A.Nonempty := leaders_nonempty _
  have hiA : i ∈ A := mem_leaders.mpr ha.2
  have hsep : StrictTop x A a := by
    intro j hj k hk
    rw [mem_leaders.mp hj]
    exact lt_of_le_of_ne (Finset.le_sup' (fun j => x j a) (Finset.mem_univ k))
      (fun he => (Finset.mem_compl.mp hk) (mem_leaders.mpr he))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_strictTop hc A) a hsep
  let b := min t (a + ε / 2)
  have hab : a < b := lt_min hat (by linarith only [hε])
  have hbt : b ≤ t := min_le_left _ _
  have hsep' (r : ℝ) (hr : r ∈ Set.Icc a b) : StrictTop x A r := by
    refine hball (Metric.mem_ball.mpr ?_)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith only [hr.2.trans (min_le_right t (a + ε / 2)), hε]
  have he := equal_on_of_top_comparison hc hC hcomp hA (hs₀.trans ha.1.1) (hbt.trans htT)
    (fun j hj k hk => (mem_leaders.mp hj).trans (mem_leaders.mp hk).symm) hsep'
    b ⟨hab.le, le_rfl⟩ i hiA
  have hib : x i b = fluidMax (fun j => x j b) := by
    refine le_antisymm (Finset.le_sup' (fun j => x j b) (Finset.mem_univ i)) ?_
    apply Finset.sup'_le
    intro j _
    by_cases hj : j ∈ A
    · exact (he j hj).ge
    · exact (hsep' b ⟨hab.le, le_rfl⟩ i hiA j (Finset.mem_compl.mpr hj)).le
  exact (not_le_of_gt hab) (hlast ⟨⟨ha.1.1.trans hab.le, hbt⟩, hib⟩)

/-- Persistent leaders and the elapsed-time bound for strictly separated
groups force the leading set to increase by the next deadline. -/
theorem joinRuleFrom_of_leaderPersist {x : ι → ℝ → ℝ} {s₀ b T : ℝ}
    (hp : LeaderPersist x s₀ T) (hb : 0 ≤ b) (hmeet : M2Meet.MeetBound x s₀ b T) :
    JoinRuleFrom x s₀ (b + 1) T := by
  classical
  intro s hs hproper hdeadline
  let A := leaders (fun i => x i s)
  let D := fluidGap (fun i => x i s)
  let t := s + (b + 1) * D
  have ht : t < T := hdeadline
  have hA : A.Nonempty := leaders_nonempty _
  have hD : 0 < D := by
    obtain ⟨i, hi⟩ : ∃ i, i ∉ A := by
      by_contra! h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    have hlo : fluidMin (fun j => x j s) ≤ x i s := Finset.inf'_le _ (Finset.mem_univ i)
    have hhi : x i s < fluidMax (fun j => x j s) :=
      lt_of_le_of_ne (Finset.le_sup' (fun j => x j s) (Finset.mem_univ i))
        (fun he => hi (mem_leaders.mpr he))
    exact sub_pos.mpr (hlo.trans_lt hhi)
  have hst : s ≤ t := by dsimp only [t]; linarith only [mul_nonneg (by linarith : 0 ≤ b + 1) hD.le]
  by_contra! hno
  have he (u : ℝ) (hu : u ∈ Set.Icc s t) : A = leaders (fun i => x i u) := by
    have hsub := hp s u hs hu.1 (hu.2.trans ht.le)
    by_contra hne
    exact hno u hu.1 hu.2 (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hsep (u : ℝ) (hu : u ∈ Set.Icc s t) :
      ∀ i ∈ A, ∀ j ∈ Finset.univ \ A, x j u < x i u := by
    intro i hi j hj
    have hi' := mem_leaders.mp (he u hu ▸ hi)
    rw [hi']
    exact lt_of_le_of_ne (Finset.le_sup' (fun k => x k u) (Finset.mem_univ j)) (fun hej =>
      (Finset.mem_sdiff.mp hj).2 ((he u hu).symm ▸ mem_leaders.mpr hej))
  have h := hmeet A hA s t hs hst ht.le rfl hproper hsep
  change t - s ≤ b * D at h
  dsimp only [t] at h
  nlinarith only [h, hD]

omit [DecidableEq ι] in
/-- Coalescence persists once the increasing leading set reaches all paths. -/
theorem exists_coalescence_of_leaderPersist {x : ι → ℝ → ℝ} {s₀ b D T : ℝ}
    (hp : LeaderPersist x s₀ T) (hm : FluidMotionOn x s₀ T) (hj : JoinRuleFrom x s₀ b T)
    (hD : 0 ≤ D) (hb : 0 ≤ b) (hlim : D * (1 + b) ^ (Fintype.card ι - 1) - 1 < T)
    (hs : s₀ ≤ D - 1) (hgap : fluidGap (fun i => x i s₀) ≤ D) :
    ∃ u, s₀ ≤ u ∧ u ≤ D * (1 + b) ^ (Fintype.card ι - 1) - 1 ∧
      ∀ t, u ≤ t → t ≤ T → ∀ i j, x i t = x j t := by
  obtain ⟨u, hsu, hu, hfull⟩ := exists_coalescence_aux x s₀ b D T hm hj hD hb hlim
    (Fintype.card ι) 0 s₀ (Nat.sub_le _ _) (Finset.card_pos.mpr (leaders_nonempty _))
    le_rfl (by simpa using hs) (by simpa using hgap)
  refine ⟨u, hsu, hu, ?_⟩
  intro t ht htT i j
  have hsub := hp u t hsu ht htT
  rw [hfull] at hsub
  exact (mem_leaders.mp (hsub (Finset.mem_univ i))).trans
    (mem_leaders.mp (hsub (Finset.mem_univ j))).symm

end Swarming.Diameter
