/-
Compact first/last contact lemmas for continuous real functions on a bounded
interval.  These are dependency-light topological inputs to the fluid group
arguments; they contain no probability or stochastic-model assumption.
-/
import Swarm.Imports

open Classical Filter Topology

namespace FluidInterval

/-- If a continuous function is nonpositive at the left endpoint and positive
at the right endpoint, there is a last nonpositive time.  At that time the
function is zero, and it is strictly positive afterwards. -/
theorem exists_last_eq_zero_of_continuousOn
    {g : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hg : ContinuousOn g (Set.Icc s t))
    (hs : g s ≤ 0) (ht : 0 < g t) :
    ∃ u ∈ Set.Ico s t, g u = 0 ∧ ∀ v ∈ Set.Ioc u t, 0 < g v := by
  let S := Set.Icc s t ∩ g ⁻¹' Set.Iic 0
  have hSclosed : IsClosed S :=
    hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed Set.inter_subset_left
  have hsS : s ∈ S := by
    exact ⟨⟨le_rfl, hst⟩, hs⟩
  obtain ⟨u, huS, humax⟩ :=
    hScompact.exists_isMaxOn ⟨s, hsS⟩ continuousOn_id
  have huI : u ∈ Set.Icc s t := huS.1
  have hgu_le : g u ≤ 0 := huS.2
  have hut : u < t := by
    apply lt_of_le_of_ne huI.2
    intro hut
    subst u
    linarith
  have hgu : g u = 0 := by
    apply le_antisymm hgu_le
    by_contra hnonneg
    have hguneg : g u < 0 := lt_of_not_ge hnonneg
    have hsub : Set.Icc u t ⊆ Set.Icc s t :=
      Set.Icc_subset_Icc huI.1 le_rfl
    have hmem : (0 : ℝ) ∈ Set.Icc (g u) (g t) :=
      ⟨hguneg.le, ht.le⟩
    obtain ⟨v, hv, hgv⟩ :=
      intermediate_value_Icc hut.le (hg.mono hsub) hmem
    have hvS : v ∈ S := by
      exact ⟨hsub hv, hgv.le⟩
    have hvu : v = u := le_antisymm (humax hvS) hv.1
    subst v
    exact (ne_of_lt hguneg) hgv
  refine ⟨u, ⟨huI.1, hut⟩, hgu, ?_⟩
  intro v hv
  apply lt_of_not_ge
  intro hvg
  have hvS : v ∈ S := by
    refine ⟨⟨?_, hv.2⟩, hvg⟩
    exact huI.1.trans hv.1.le
  exact (not_le_of_gt hv.1) (humax hvS)

/-- If a continuous function is initially positive and is nonpositive
somewhere on the interval, there is a first nonpositive time.  That time is a
zero, and the function is strictly positive before it. -/
theorem exists_first_eq_zero_of_continuousOn
    {g : ℝ → ℝ} {s t : ℝ} (_hst : s ≤ t)
    (hg : ContinuousOn g (Set.Icc s t))
    (hs : 0 < g s) (hex : ∃ v ∈ Set.Icc s t, g v ≤ 0) :
    ∃ u ∈ Set.Ioc s t, g u = 0 ∧ ∀ v ∈ Set.Ico s u, 0 < g v := by
  let S := Set.Icc s t ∩ g ⁻¹' Set.Iic 0
  have hSclosed : IsClosed S :=
    hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed Set.inter_subset_left
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hvg⟩ := hex
    exact ⟨v, hv, hvg⟩
  obtain ⟨u, huS, humin⟩ :=
    hScompact.exists_isMinOn hSne continuousOn_id
  have huI : u ∈ Set.Icc s t := huS.1
  have hgu_le : g u ≤ 0 := huS.2
  have hsu : s < u := by
    apply lt_of_le_of_ne huI.1
    intro hsu
    subst u
    linarith
  have hgu : g u = 0 := by
    apply le_antisymm hgu_le
    by_contra hnonneg
    have hguneg : g u < 0 := lt_of_not_ge hnonneg
    have hsub : Set.Icc s u ⊆ Set.Icc s t :=
      Set.Icc_subset_Icc le_rfl huI.2
    have hmem : (0 : ℝ) ∈ Set.Icc (g u) (g s) :=
      ⟨hguneg.le, hs.le⟩
    obtain ⟨v, hv, hgv⟩ :=
      intermediate_value_Icc' hsu.le (hg.mono hsub) hmem
    have hvS : v ∈ S := by
      exact ⟨hsub hv, hgv.le⟩
    have hvu : v = u := le_antisymm hv.2 (humin hvS)
    subst v
    exact (ne_of_lt hguneg) hgv
  refine ⟨u, ⟨hsu, huI.2⟩, hgu, ?_⟩
  intro v hv
  apply lt_of_not_ge
  intro hvg
  have hvS : v ∈ S := by
    refine ⟨⟨hv.1, hv.2.le.trans huI.2⟩, hvg⟩
  exact (not_le_of_gt hv.2) (humin hvS)

end FluidInterval
