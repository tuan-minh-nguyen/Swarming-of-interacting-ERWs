/-
# Fluid geometry from the local-good separated-group estimates

This module isolates the zero-error fluid-limit forms of `(Wpos)`,
`(loccoord)`, `(locgroup)` and `(locmove)` in the tightness proof.  It then
proves actual `FluidMerge.StickyOn` and `FluidMerge.JoinRuleFrom` conclusions.
The estimates themselves are not proved here: in particular, no finite-L good
event, limiting subsequence, fluid-maximum theorem or good-event probability is
constructed.  `AtRecordsOn` is precisely the needed fluid-maximum conclusion
`m_i(t) = x_i(t)` after `s₀`; the running maxima are otherwise kept explicit.

The reset estimate retains both terms from the paper: the internal spread of
the upper group and the maximum record lag of the lower group.  Group decay is
required on `(u,t]`, so it can be applied after a last contact without
falsely assuming separation at that contact.  Stickiness is proved for a whole
finite coincident group by induction on the number tied at its maximum.
Joining is obtained at the first contact, before applying leader decay; no
indefinite-separation hypothesis is hidden in the conclusion.
-/
import Swarm.FluidMergeLight
import Swarm.IntervalGeometry

open Classical Filter Topology
open scoped BigOperators

namespace FluidGeometry

open FluidMerge
open FluidInterval

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Maximum over a nonempty finite group. -/
noncomputable def groupMax (A : Finset ι) (hA : A.Nonempty) (z : ι → ℝ) : ℝ :=
  A.sup' hA z

/-- Minimum over a nonempty finite group. -/
noncomputable def groupMin (A : Finset ι) (hA : A.Nonempty) (z : ι → ℝ) : ℝ :=
  A.inf' hA z

/-- Internal spread of a nonempty finite group. -/
noncomputable def groupSpread (A : Finset ι) (hA : A.Nonempty) (z : ι → ℝ) : ℝ :=
  groupMax A hA z - groupMin A hA z

/-- `I` is an upper group in `D`: every member of `I` is above every
member of the complementary group `D \ I`. -/
def GroupUpper (D I : Finset ι) (z : ι → ℝ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ D \ I, z j ≤ z i

/-- Position separation of `I` above `J`, using paths `x` for `I` and paths
`m` for `J`.  Taking `m` to be the running maxima gives fluid `(sep)`. -/
noncomputable def groupGap (x m : ι → ℝ → ℝ)
    (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (t : ℝ) : ℝ :=
  groupMin I hI (fun i => x i t) - groupMax J hJ (fun j => m j t)

/-- After `s₀`, each supplied running maximum agrees with the current position
through `T`: the needed fluid form of `(fluidmax)`. -/
def AtRecordsOn (x m : ι → ℝ → ℝ) (s₀ T : ℝ) : Prop :=
  ∀ i t, s₀ ≤ t → t ≤ T → m i t = x i t

/-- Fluid-limit `(Wpos)`: under weak ordering, the separated-group potential
is bounded below by the actual position gap. -/
def GroupLower (x : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T : ℝ) : Prop :=
  ∀ (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (t : ℝ),
    s₀ ≤ t → t ≤ T → Disjoint I J →
    0 ≤ groupGap x x I J hI hJ t → groupGap x x I J hI hJ t ≤ W I J t

/-- Fluid-limit coordinate/reset bound from `(loccoord)`.  A failed separation
at `u` bounds `W` by internal upper-group spread plus lower-group record lag.
There is no discrete nearest-neighbour `+2` term in the zero-error limit. -/
def GroupReset (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T C : ℝ) : Prop :=
  ∀ (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (u : ℝ),
    s₀ ≤ u → u ≤ T → Disjoint I J →
    groupGap x m I J hI hJ u ≤ 0 →
    W I J u ≤ C * (groupSpread I hI (fun i => x i u) +
      groupMax J hJ (fun j => m j u - x j u))

/-- Fluid-limit `(locgroup)`, including the limiting passage to the left
endpoint.  Crucially, strict separation is demanded only on `(s,t]`. -/
def GroupDecay (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T : ℝ) : Prop :=
  ∀ (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (s t : ℝ),
    s₀ ≤ s → s ≤ t → t ≤ T → Disjoint I J →
    (∀ r ∈ Set.Ioc s t, 0 < groupGap x m I J hI hJ r) →
    W I J t ≤ W I J s

/-- Fluid-limit `(locmove)` for the current leader set `A` and its complement.
As in the paper, the coincident leader spread at `s` has already vanished, so
only the linear negative elapsed-time term remains. -/
def LeaderDecay (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T C : ℝ) : Prop :=
  ∀ (A J : Finset ι) (hA : A.Nonempty) (hJ : J.Nonempty) (s t : ℝ),
    s₀ ≤ s → s ≤ t → t ≤ T →
    A = leaders (fun i => x i s) → J = Finset.univ \ A → A ≠ Finset.univ →
    Disjoint A J →
    (∀ r ∈ Set.Icc s t, 0 < groupGap x m A J hA hJ r) →
    W A J t ≤ W A J s - (t - s) / C

/-- Initial upper-coordinate bound for the leader potential.  This is the
fluid form of the last `W_s ≤ C L (max x_s - min x_s)` estimate in `(meet)`. -/
def LeaderStart (x : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ C : ℝ) : Prop :=
  ∀ (A J : Finset ι) (hA : A.Nonempty) (hJ : J.Nonempty) (s : ℝ),
    s₀ ≤ s → A = leaders (fun i => x i s) → J = Finset.univ \ A →
    A ≠ Finset.univ → Disjoint A J →
    W A J s ≤ C * fluidGap (fun i => x i s)

/-- The five precise local-good estimates needed below.  No probability,
stationarity, independence, invariance or regeneration is included. -/
def FluidLocalGood (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T C : ℝ) : Prop :=
  GroupLower x W s₀ T ∧ GroupReset x m W s₀ T C ∧ GroupDecay x m W s₀ T ∧
    LeaderDecay x m W s₀ T C ∧ LeaderStart x W s₀ C

@[simp] theorem groupMax_eq_const {A : Finset ι} {hA : A.Nonempty}
    {z : ι → ℝ} {c : ℝ} (h : ∀ i ∈ A, z i = c) : groupMax A hA z = c := by
  apply le_antisymm
  · exact Finset.sup'_le hA z (fun i hi => (h i hi).le)
  · obtain ⟨i, hi⟩ := hA
    rw [← h i hi]
    exact Finset.le_sup' z hi

@[simp] theorem groupMin_eq_const {A : Finset ι} {hA : A.Nonempty}
    {z : ι → ℝ} {c : ℝ} (h : ∀ i ∈ A, z i = c) : groupMin A hA z = c := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hA
    rw [← h i hi]
    exact Finset.inf'_le z hi
  · exact Finset.le_inf' hA z (fun i hi => (h i hi).ge)

@[simp] theorem groupSpread_eq_zero {A : Finset ι} {hA : A.Nonempty}
    {z : ι → ℝ} {c : ℝ} (h : ∀ i ∈ A, z i = c) : groupSpread A hA z = 0 := by
  unfold groupSpread
  rw [groupMax_eq_const h, groupMin_eq_const h]
  ring

theorem groupMax_le_of_subset {A D : Finset ι} {hA : A.Nonempty} {hD : D.Nonempty}
    {z : ι → ℝ} (hAD : A ⊆ D) : groupMax A hA z ≤ groupMax D hD z := by
  unfold groupMax
  exact Finset.sup'_le hA z (fun i hi => Finset.le_sup' z (hAD hi))

theorem groupMin_le_of_subset {A D : Finset ι} {hA : A.Nonempty} {hD : D.Nonempty}
    {z : ι → ℝ} (hAD : A ⊆ D) : groupMin D hD z ≤ groupMin A hA z := by
  unfold groupMin
  exact Finset.le_inf' hA z (fun i hi => Finset.inf'_le z (hAD hi))

theorem groupMax_eq_of_upper {D I : Finset ι} {hD : D.Nonempty} {hI : I.Nonempty}
    {z : ι → ℝ} (hID : I ⊆ D) (hupper : GroupUpper D I z) :
    groupMax I hI z = groupMax D hD z := by
  apply le_antisymm (groupMax_le_of_subset hID)
  obtain ⟨i₀, hi₀⟩ := hI
  unfold groupMax
  refine Finset.sup'_le hD z (fun j hj => ?_)
  by_cases hjI : j ∈ I
  · exact Finset.le_sup' z hjI
  · exact (hupper i₀ hi₀ j (Finset.mem_sdiff.mpr ⟨hj, hjI⟩)).trans
      (Finset.le_sup' z hi₀)

theorem continuousOn_groupMax {x : ι → ℝ → ℝ} {s T : ℝ}
    (A : Finset ι) (hA : A.Nonempty)
    (hx : ∀ i, ContinuousOn (x i) (Set.Icc s T)) :
    ContinuousOn (fun t => groupMax A hA (fun i => x i t)) (Set.Icc s T) := by
  unfold groupMax
  exact ContinuousOn.finset_sup'_apply hA (fun i _ => hx i)

theorem continuousOn_groupMin {x : ι → ℝ → ℝ} {s T : ℝ}
    (A : Finset ι) (hA : A.Nonempty)
    (hx : ∀ i, ContinuousOn (x i) (Set.Icc s T)) :
    ContinuousOn (fun t => groupMin A hA (fun i => x i t)) (Set.Icc s T) := by
  unfold groupMin
  exact ContinuousOn.finset_inf'_apply hA (fun i _ => hx i)

theorem groupGap_eq_of_records {x m : ι → ℝ → ℝ}
    (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (t : ℝ)
    (hm : ∀ j ∈ J, m j t = x j t) :
    groupGap x m I J hI hJ t = groupGap x x I J hI hJ t := by
  have hmax : groupMax J hJ (fun j => m j t) = groupMax J hJ (fun j => x j t) := by
    unfold groupMax
    exact Finset.sup'_congr hJ rfl (fun j hj => hm j hj)
  unfold groupGap
  rw [hmax]

theorem continuousOn_groupGap {x : ι → ℝ → ℝ} {s T : ℝ}
    (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hx : ∀ i, ContinuousOn (x i) (Set.Icc s T)) :
    ContinuousOn (fun t => groupGap x x I J hI hJ t) (Set.Icc s T) := by
  exact (continuousOn_groupMin I hI hx).sub (continuousOn_groupMax J hJ hx)

/-- Persistence of every finite initially coincident group.  The induction
shows that each upper group of each permitted cardinality is tied at the global
maximum, uniformly at every later time. -/
theorem coincident_group_persistent
    (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (C s₀ s T : ℝ) (D : Finset ι) (hD : D.Nonempty) (c : ℝ)
    (hlower : GroupLower x W s₀ T) (hreset : GroupReset x m W s₀ T C)
    (hdecay : GroupDecay x m W s₀ T) (hrecords : AtRecordsOn x m s₀ T)
    (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T))
    (hs₀ : s₀ ≤ s) (hsT : s ≤ T) (hinit : ∀ i ∈ D, x i s = c) :
    ∀ t, s ≤ t → t ≤ T → ∀ i ∈ D, ∀ j ∈ D, x i t = x j t := by
  have hrank : ∀ k : ℕ, 1 ≤ k → k ≤ D.card →
      ∀ t, s ≤ t → t ≤ T → ∀ I : Finset ι, I ⊆ D → I.card = k →
      GroupUpper D I (fun i => x i t) →
      ∀ i ∈ I, x i t = groupMax D hD (fun j => x j t) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
        intro _ hkD t hst htT E hED hEcard hEtied
        by_cases hk0 : k = 0
        · subst k
          obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hEcard
          have hI : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
          have hmax := groupMax_eq_of_upper (hD := hD) (hI := hI) hED hEtied
          intro j hj
          rw [Finset.mem_singleton] at hj
          subst j
          calc
            x i t = groupMax {i} hI (fun j => x j t) :=
              (groupMax_eq_const (A := {i}) (hA := hI) (z := fun j => x j t)
                (c := x i t) (fun j hj => by
                  rw [Finset.mem_singleton] at hj
                  subst j
                  rfl)).symm
            _ = groupMax D hD (fun j => x j t) := hmax
        · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          have hE : E.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨e, heE, hemin⟩ := Finset.exists_mem_eq_inf' hE (fun i => x i t)
          change E.inf' hE (fun i => x i t) = x e t at hemin
          let I := E.erase e
          let J := D \ I
          have hIE : I ⊆ E := Finset.erase_subset e E
          have hID : I ⊆ D := hIE.trans hED
          have hIcard : I.card = k := by
            dsimp [I]
            rw [Finset.card_erase_of_mem heE, hEcard]
            omega
          have hI : I.Nonempty := Finset.card_pos.mp (by omega)
          have heD : e ∈ D := hED heE
          have heJ : e ∈ J := by
            apply Finset.mem_sdiff.mpr
            exact ⟨heD, by simp [I]⟩
          have hJ : J.Nonempty := ⟨e, heJ⟩
          have hdis : Disjoint I J := by
            refine Finset.disjoint_left.mpr (fun i hiI hiJ => ?_)
            exact (Finset.mem_sdiff.mp hiJ).2 hiI
          have hupperI_t : GroupUpper D I (fun i => x i t) := by
            intro i hiI j hj
            have hiE : i ∈ E := hIE hiI
            have hjD : j ∈ D := (Finset.mem_sdiff.mp hj).1
            have hjI : j ∉ I := (Finset.mem_sdiff.mp hj).2
            by_cases hje : j = e
            · subst j
              change x e t ≤ x i t
              rw [← hemin]
              exact Finset.inf'_le (fun i => x i t) hiE
            · have hjE : j ∉ E := by
                intro hjE
                exact hjI (Finset.mem_erase.mpr ⟨hje, hjE⟩)
              exact hEtied i hiE j (Finset.mem_sdiff.mpr ⟨hjD, hjE⟩)
          have hgap_nonneg : 0 ≤ groupGap x x I J hI hJ t := by
            unfold groupGap
            refine sub_nonneg.mpr ?_
            unfold groupMax groupMin
            exact Finset.sup'_le hJ _ (fun j hj =>
              Finset.le_inf' hI _ (fun i hi => hupperI_t i hi j hj))
          by_cases hp : 0 < groupGap x x I J hI hJ t
          · exfalso
            have hg_s : groupGap x x I J hI hJ s = 0 := by
              unfold groupGap
              have hmin : groupMin I hI (fun i => x i s) = c :=
                groupMin_eq_const (fun i hi => hinit i (hID hi))
              have hmax : groupMax J hJ (fun j => x j s) = c :=
                groupMax_eq_const (fun j hj => hinit j (Finset.mem_sdiff.mp hj).1)
              rw [hmin, hmax]
              ring
            have hcs : ∀ i, ContinuousOn (x i) (Set.Icc s t) := by
              intro i
              exact (hcont i).mono (Set.Icc_subset_Icc hs₀ htT)
            obtain ⟨u, hu, hgu, hafter⟩ := exists_last_eq_zero_of_continuousOn
              hst (continuousOn_groupGap I J hI hJ hcs) hg_s.le hp
            have hs₀u : s₀ ≤ u := hs₀.trans hu.1
            have huT : u ≤ T := hu.2.le.trans htT
            have hgu_xm : groupGap x m I J hI hJ u = 0 := by
              rw [groupGap_eq_of_records I J hI hJ u
                (fun j _ => hrecords j u hs₀u huT)]
              exact hgu
            have hupperI_u : GroupUpper D I (fun i => x i u) := by
              intro i hi j hj
              have hjle : x j u ≤ groupMax J hJ (fun j => x j u) :=
                Finset.le_sup' (fun j => x j u) hj
              have hile : groupMin I hI (fun i => x i u) ≤ x i u :=
                Finset.inf'_le (fun i => x i u) hi
              change groupMin I hI (fun i => x i u) -
                groupMax J hJ (fun j => x j u) = 0 at hgu
              linarith
            have hItied_u := ih hkpos (by omega) u hu.1 huT I hID hIcard hupperI_u
            have hspread : groupSpread I hI (fun i => x i u) = 0 :=
              groupSpread_eq_zero hItied_u
            have hlag : groupMax J hJ (fun j => m j u - x j u) = 0 :=
              groupMax_eq_const (fun j _ => sub_eq_zero.mpr (hrecords j u hs₀u huT))
            have hWu := hreset I J hI hJ u hs₀u huT hdis hgu_xm.le
            rw [hspread, hlag] at hWu
            have hWu0 : W I J u ≤ 0 := by simpa using hWu
            have hWt : W I J t ≤ 0 := by
              apply (hdecay I J hI hJ u t hs₀u hu.2.le htT hdis ?_).trans hWu0
              intro r hr
              rw [groupGap_eq_of_records I J hI hJ r
                (fun j _ => hrecords j r (hs₀u.trans hr.1.le) (hr.2.trans htT))]
              exact hafter r hr
            have hgapW := hlower I J hI hJ t (hs₀.trans hst) htT hdis hgap_nonneg
            linarith
          · have hzero : groupGap x x I J hI hJ t = 0 :=
              le_antisymm (le_of_not_gt hp) hgap_nonneg
            have hItied_t := ih hkpos (by omega) t hst htT I hID hIcard hupperI_t
            have hminI : groupMin I hI (fun i => x i t) =
                groupMax D hD (fun i => x i t) := groupMin_eq_const hItied_t
            have hmaxJ : groupMax J hJ (fun j => x j t) =
                groupMax D hD (fun j => x j t) := by
              unfold groupGap at hzero
              rw [hminI] at hzero
              linarith
            have he_le : x e t ≤ groupMax D hD (fun i => x i t) :=
              Finset.le_sup' (fun i => x i t) heD
            obtain ⟨j, hjJ, hjmax⟩ := Finset.exists_mem_eq_sup' hJ (fun j => x j t)
            change groupMax J hJ (fun j => x j t) = x j t at hjmax
            have hxj : x j t = groupMax D hD (fun i => x i t) := by
              rw [← hjmax]
              exact hmaxJ
            have hxe : x e t = groupMax D hD (fun i => x i t) := by
              by_cases hje : j = e
              · subst j
                exact hxj
              · have hjD : j ∈ D := (Finset.mem_sdiff.mp hjJ).1
                have hjI : j ∉ I := (Finset.mem_sdiff.mp hjJ).2
                have hjE : j ∉ E := by
                  intro hjE
                  exact hjI (Finset.mem_erase.mpr ⟨hje, hjE⟩)
                have hje_le := hEtied e heE j (Finset.mem_sdiff.mpr ⟨hjD, hjE⟩)
                change x j t ≤ x e t at hje_le
                rw [hxj] at hje_le
                exact le_antisymm he_le hje_le
            intro i hiE
            by_cases hie : i = e
            · subst i
              exact hxe
            · exact hItied_t i (Finset.mem_erase.mpr ⟨hie, hiE⟩)
  intro t hst htT i hi j hj
  have hcard : 1 ≤ D.card := Finset.card_pos.mpr hD
  have hupper : GroupUpper D D (fun i => x i t) := by
    simp [GroupUpper]
  have hall := hrank D.card hcard le_rfl t hst htT D (fun _ h => h) rfl hupper
  exact (hall i hi).trans (hall j hj).symm

/-- The fluid local-good estimates derive the accepted `StickyOn` input. -/
theorem stickyOn_of_localGood
    (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ) (s₀ T C : ℝ)
    (hlocal : FluidLocalGood x m W s₀ T C) (hrecords : AtRecordsOn x m s₀ T)
    (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T)) : StickyOn x s₀ T := by
  intro i j s t hs₀ hst htT hij
  let D : Finset ι := {i, j}
  have hD : D.Nonempty := ⟨i, by simp [D]⟩
  have hinit : ∀ k ∈ D, x k s = x i s := by
    intro k hk
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rfl
    · exact hij.symm
  have hpersist := coincident_group_persistent x m W C s₀ s T D hD (x i s)
    hlocal.1 hlocal.2.1 hlocal.2.2.1 hrecords hcont hs₀ (hst.trans htT) hinit
  exact hpersist t hst htT i (by simp [D]) j (by simp [D])

/-- A proper set has nonempty complement. -/
theorem univ_sdiff_nonempty_of_ne_univ (A : Finset ι) (hA : A ≠ Finset.univ) :
    (Finset.univ \ A).Nonempty := by
  apply Finset.sdiff_nonempty.mpr
  intro hsub
  apply hA
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  exact hsub (Finset.mem_univ i)

/-- A proper leader set forces a strictly positive configuration diameter. -/
theorem fluidGap_pos_of_leaders_ne_univ (z : ι → ℝ)
    (hproper : leaders z ≠ Finset.univ) : 0 < fluidGap z := by
  obtain ⟨j, hj⟩ := univ_sdiff_nonempty_of_ne_univ (leaders z) hproper
  have hjA : j ∉ leaders z := (Finset.mem_sdiff.mp hj).2
  have hle : z j ≤ fluidMax z := Finset.le_sup' z (Finset.mem_univ j)
  have hne : z j ≠ fluidMax z := by
    intro heq
    exact hjA (mem_leaders.mpr heq)
  have hlt : z j < fluidMax z := lt_of_le_of_ne hle hne
  have hmin : fluidMin z ≤ z j := Finset.inf'_le z (Finset.mem_univ j)
  unfold fluidGap
  linarith

/-- At a proper leader set, its strict position separation from the complement
is initially positive. -/
theorem leader_initial_gap_pos (x : ι → ℝ → ℝ)
    (A J : Finset ι) (hA : A.Nonempty) (hJ : J.Nonempty) (s : ℝ)
    (hAdef : A = leaders (fun i => x i s)) (hJdef : J = Finset.univ \ A)
    (hproper : A ≠ Finset.univ) : 0 < groupGap x x A J hA hJ s := by
  have hmin : groupMin A hA (fun i => x i s) = fluidMax (fun i => x i s) := by
    apply groupMin_eq_const
    intro i hi
    exact (mem_leaders (x := fun k => x k s) (i := i)).mp (by rwa [← hAdef])
  obtain ⟨j, hjJ, hjmax⟩ := Finset.exists_mem_eq_sup' hJ (fun j => x j s)
  change groupMax J hJ (fun j => x j s) = x j s at hjmax
  have hjA : j ∉ A := by
    have hjJ' : j ∈ Finset.univ \ A := by rwa [← hJdef]
    exact (Finset.mem_sdiff.mp hjJ').2
  have hle : x j s ≤ fluidMax (fun i => x i s) :=
    Finset.le_sup' (fun i => x i s) (Finset.mem_univ j)
  have hne : x j s ≠ fluidMax (fun i => x i s) := by
    intro heq
    apply hjA
    rw [hAdef]
    exact mem_leaders.mpr heq
  have hlt : x j s < fluidMax (fun i => x i s) := lt_of_le_of_ne hle hne
  unfold groupGap
  rw [hmin, hjmax]
  exact sub_pos.mpr hlt

/-- The zero-error fluid `(meet)` calculation.  On any interval on which the
leaders remain strictly above the complementary running maxima, elapsed time
is at most `C²` times the original diameter. -/
theorem leader_time_bound_of_separated
    (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (C s₀ T s v : ℝ) (hC : 0 < C)
    (hlower : GroupLower x W s₀ T) (hleader : LeaderDecay x m W s₀ T C)
    (hstart : LeaderStart x W s₀ C) (hrecords : AtRecordsOn x m s₀ T)
    (A J : Finset ι) (hA : A.Nonempty) (hJ : J.Nonempty)
    (hs₀ : s₀ ≤ s) (hsv : s ≤ v) (hvT : v ≤ T)
    (hAdef : A = leaders (fun i => x i s)) (hJdef : J = Finset.univ \ A)
    (hproper : A ≠ Finset.univ) (hdis : Disjoint A J)
    (hsep : ∀ r ∈ Set.Icc s v, 0 < groupGap x m A J hA hJ r) :
    v - s ≤ C * C * fluidGap (fun i => x i s) := by
  have hsep_x : 0 < groupGap x x A J hA hJ v := by
    rw [← groupGap_eq_of_records A J hA hJ v
      (fun j _ => hrecords j v (hs₀.trans hsv) hvT)]
    exact hsep v ⟨hsv, le_rfl⟩
  have hgapW := hlower A J hA hJ v (hs₀.trans hsv) hvT hdis hsep_x.le
  have hWnonneg : 0 ≤ W A J v := hsep_x.le.trans hgapW
  have hdec := hleader A J hA hJ s v hs₀ hsv hvT hAdef hJdef hproper hdis hsep
  have hini := hstart A J hA hJ s hs₀ hAdef hJdef hproper hdis
  have hmain : (v - s) / C ≤ C * fluidGap (fun i => x i s) := by
    linarith
  have hmul := (div_le_iff₀ hC).mp hmain
  calc
    v - s ≤ C * fluidGap (fun i => x i s) * C := hmul
    _ = C * C * fluidGap (fun i => x i s) := by ring

/-- A zero leader/complement gap after `s` creates a strict leader inclusion.
Former leaders are retained by `StickyOn`; the new maximiser comes from `J`. -/
theorem leaders_ssubset_of_contact
    (x : ι → ℝ → ℝ) (s₀ T s u : ℝ) (hsticky : StickyOn x s₀ T)
    (A J : Finset ι) (hA : A.Nonempty) (hJ : J.Nonempty)
    (hs₀ : s₀ ≤ s) (hsu : s ≤ u) (huT : u ≤ T)
    (hAdef : A = leaders (fun i => x i s)) (hJdef : J = Finset.univ \ A)
    (hcontact : groupGap x x A J hA hJ u = 0) :
    A ⊂ leaders (fun i => x i u) := by
  let i₀ := Classical.choose hA
  have hi₀ : i₀ ∈ A := Classical.choose_spec hA
  have hi₀leader : x i₀ s = fluidMax (fun i => x i s) := by
    exact (mem_leaders (x := fun k => x k s) (i := i₀)).mp (by rwa [← hAdef])
  have hpair : ∀ i ∈ A, x i u = x i₀ u := by
    intro i hi
    apply hsticky i i₀ s u hs₀ hsu huT
    have hileader : x i s = fluidMax (fun i => x i s) := by
      exact (mem_leaders (x := fun k => x k s) (i := i)).mp (by rwa [← hAdef])
    exact hileader.trans hi₀leader.symm
  have hmin : groupMin A hA (fun i => x i u) = x i₀ u := groupMin_eq_const hpair
  obtain ⟨j, hjJ, hjmax⟩ := Finset.exists_mem_eq_sup' hJ (fun j => x j u)
  change groupMax J hJ (fun j => x j u) = x j u at hjmax
  have hxj : x j u = x i₀ u := by
    unfold groupGap at hcontact
    rw [hmin, hjmax] at hcontact
    linarith
  have hall_le : ∀ k, x k u ≤ x i₀ u := by
    intro k
    by_cases hkA : k ∈ A
    · rw [hpair k hkA]
    · have hkJ : k ∈ J := by
        rw [hJdef]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkA⟩
      calc
        x k u ≤ groupMax J hJ (fun j => x j u) :=
          Finset.le_sup' (fun j => x j u) hkJ
        _ = x j u := hjmax
        _ = x i₀ u := hxj
  have hmax : fluidMax (fun i => x i u) = x i₀ u := by
    apply le_antisymm
    · unfold fluidMax
      exact Finset.sup'_le Finset.univ_nonempty _ (fun k _ => hall_le k)
    · exact Finset.le_sup' (fun i => x i u) (Finset.mem_univ i₀)
  have hsub : A ⊆ leaders (fun i => x i u) := by
    intro i hi
    exact mem_leaders.mpr ((hpair i hi).trans hmax.symm)
  have hjnew : j ∈ leaders (fun i => x i u) :=
    mem_leaders.mpr (hxj.trans hmax.symm)
  have hjA : j ∉ A := by
    have hjJ' : j ∈ Finset.univ \ A := by rwa [← hJdef]
    exact (Finset.mem_sdiff.mp hjJ').2
  exact (Finset.ssubset_iff_of_subset hsub).mpr ⟨j, hjnew, hjA⟩

/-- The separated leader estimates and `StickyOn` derive the accepted bounded
`JoinRuleFrom` input with the paper's scalar `b = C² > 0`. -/
theorem joinRuleFrom_of_leader_estimates
    (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T C : ℝ) (hC : 0 < C)
    (hlower : GroupLower x W s₀ T) (hleader : LeaderDecay x m W s₀ T C)
    (hstart : LeaderStart x W s₀ C) (hsticky : StickyOn x s₀ T)
    (hrecords : AtRecordsOn x m s₀ T)
    (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T)) :
    JoinRuleFrom x s₀ (C * C) T := by
  intro s hs₀ hproper hdeadline
  let A := leaders (fun i => x i s)
  let J := Finset.univ \ A
  let d := s + C * C * fluidGap (fun i => x i s)
  have hproperA : A ≠ Finset.univ := by simpa only [A] using hproper
  have hA : A.Nonempty := by
    dsimp only [A]
    exact leaders_nonempty _
  have hJ : J.Nonempty := by
    dsimp only [J]
    exact univ_sdiff_nonempty_of_ne_univ A hproperA
  have hdis : Disjoint A J := by
    refine Finset.disjoint_left.mpr (fun i hiA hiJ => ?_)
    exact (Finset.mem_sdiff.mp hiJ).2 hiA
  have hgap : 0 < fluidGap (fun i => x i s) := by
    dsimp only [A] at hproperA
    exact fluidGap_pos_of_leaders_ne_univ _ hproperA
  have hdT : d < T := by simpa only [d] using hdeadline
  have hprod : 0 < C * C * fluidGap (fun i => x i s) :=
    mul_pos (mul_pos hC hC) hgap
  have hsd : s < d := by dsimp only [d]; linarith
  have hsT : s ≤ T := by linarith
  have hinitial : 0 < groupGap x x A J hA hJ s :=
    leader_initial_gap_pos x A J hA hJ s rfl rfl hproperA
  have hcg : ContinuousOn (fun r => groupGap x x A J hA hJ r) (Set.Icc s T) := by
    apply continuousOn_groupGap A J hA hJ
    intro i
    exact (hcont i).mono (Set.Icc_subset_Icc hs₀ le_rfl)
  by_cases hex : ∃ v ∈ Set.Icc s T, groupGap x x A J hA hJ v ≤ 0
  · obtain ⟨u, hu, hgu, hbefore⟩ :=
      exists_first_eq_zero_of_continuousOn hsT hcg hinitial hex
    have hud : u ≤ d := by
      by_contra hnot
      have hdu : d < u := lt_of_not_ge hnot
      let v := (d + u) / 2
      have hdv : d < v := by dsimp only [v]; linarith
      have hvu : v < u := by dsimp only [v]; linarith
      have hsv : s ≤ v := by linarith
      have hvT : v ≤ T := hvu.le.trans hu.2
      have hsep : ∀ r ∈ Set.Icc s v, 0 < groupGap x m A J hA hJ r := by
        intro r hr
        rw [groupGap_eq_of_records A J hA hJ r
          (fun j _ => hrecords j r (hs₀.trans hr.1) (hr.2.trans hvT))]
        exact hbefore r ⟨hr.1, hr.2.trans_lt hvu⟩
      have hb := leader_time_bound_of_separated x m W C s₀ T s v hC
        hlower hleader hstart hrecords A J hA hJ hs₀ hsv hvT rfl rfl hproperA hdis hsep
      dsimp only [d] at hdv
      linarith
    have hss := leaders_ssubset_of_contact x s₀ T s u hsticky A J hA hJ
      hs₀ hu.1.le hu.2 rfl rfl hgu
    refine ⟨u, hu.1.le, hud, ?_⟩
    simpa only [A] using hss
  · exfalso
    let v := (d + T) / 2
    have hdv : d < v := by dsimp only [v]; linarith
    have hvT : v ≤ T := by dsimp only [v]; linarith
    have hsv : s ≤ v := by linarith
    have hpos : ∀ r ∈ Set.Icc s T, 0 < groupGap x x A J hA hJ r := by
      intro r hr
      apply lt_of_not_ge
      intro hrnon
      exact hex ⟨r, hr, hrnon⟩
    have hsep : ∀ r ∈ Set.Icc s v, 0 < groupGap x m A J hA hJ r := by
      intro r hr
      rw [groupGap_eq_of_records A J hA hJ r
        (fun j _ => hrecords j r (hs₀.trans hr.1) (hr.2.trans hvT))]
      exact hpos r ⟨hr.1, hr.2.trans hvT⟩
    have hb := leader_time_bound_of_separated x m W C s₀ T s v hC
      hlower hleader hstart hrecords A J hA hJ hs₀ hsv hvT rfl rfl hproperA hdis hsep
    dsimp only [d] at hdv
    linarith

/-- Nonvacuity: a lockstep fluid family, with zero group potential and zero
record lag, satisfies all five estimates.  Its proper-leader cases are empty. -/
theorem fluidLocalGood_lockstep (v : ℝ → ℝ) (s₀ T C : ℝ) :
    FluidLocalGood (fun _ : ι => v) (fun _ : ι => v)
      (fun _ _ _ => (0 : ℝ)) s₀ T C := by
  have hlead : ∀ w : ℝ, leaders (fun _ : ι => w) = Finset.univ := by
    intro w
    have hmax : fluidMax (fun _ : ι => w) = w := by
      unfold fluidMax
      exact groupMax_eq_const (A := Finset.univ) (hA := Finset.univ_nonempty)
        (z := fun _ : ι => w) (c := w) (fun _ _ => rfl)
    apply (leaders_eq_univ_iff (fun _ : ι => w)).mpr
    intro i
    rw [hmax]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro I J hI hJ t _ _ _ _
    have hz : groupGap (fun _ : ι => v) (fun _ : ι => v) I J hI hJ t = 0 := by
      unfold groupGap
      rw [groupMin_eq_const (fun _ _ => rfl), groupMax_eq_const (fun _ _ => rfl)]
      ring
    simp only [hz]
    exact le_rfl
  · intro I J hI hJ u _ _ _ _
    have hspread : groupSpread I hI (fun _ => v u) = 0 :=
      groupSpread_eq_zero (fun _ _ => rfl)
    have hlag : groupMax J hJ (fun j => v u - v u) = 0 :=
      groupMax_eq_const (fun _ _ => by ring)
    simp only [hspread, hlag, add_zero, mul_zero, le_refl]
  · intro I J hI hJ s t _ _ _ _ _
    exact le_rfl
  · intro A J hA hJ s t _ _ _ hAdef _ hproper _ _
    exfalso
    apply hproper
    rw [hAdef]
    simpa using hlead (v s)
  · intro A J hA hJ s _ hAdef _ hproper _
    exfalso
    apply hproper
    rw [hAdef]
    simpa using hlead (v s)

/-- All five local-good estimates supply both deterministic geometric inputs
needed by `FluidMergeLight.exists_persistent_coalescence`. -/
theorem sticky_and_join_of_localGood
    (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T C : ℝ) (hC : 0 < C) (hlocal : FluidLocalGood x m W s₀ T C)
    (hrecords : AtRecordsOn x m s₀ T)
    (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T)) :
    StickyOn x s₀ T ∧ JoinRuleFrom x s₀ (C * C) T := by
  have hsticky := stickyOn_of_localGood x m W s₀ T C hlocal hrecords hcont
  refine ⟨hsticky, ?_⟩
  exact joinRuleFrom_of_leader_estimates x m W s₀ T C hC hlocal.1
    hlocal.2.2.2.1 hlocal.2.2.2.2 hsticky hrecords hcont

/-- The joining half of the same derivation, for consumers that already have
`StickyOn` from another source. -/
theorem joinRuleFrom_of_localGood
    (x m : ι → ℝ → ℝ) (W : Finset ι → Finset ι → ℝ → ℝ)
    (s₀ T C : ℝ) (hC : 0 < C) (hlocal : FluidLocalGood x m W s₀ T C)
    (hrecords : AtRecordsOn x m s₀ T)
    (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T)) :
    JoinRuleFrom x s₀ (C * C) T :=
  (sticky_and_join_of_localGood x m W s₀ T C hC hlocal hrecords hcont).2

end FluidGeometry
