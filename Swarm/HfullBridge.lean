/-
The one-stage selected-block fullness statement from a genuine invariant
record law.  The invariant law is an explicit premise throughout: this file
does not construct it, and does not infer it from transience.
-/
import Swarm.StationaryRecordKac
import Swarm.Induction
import Swarm.InvariantPositivity

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmChain
open scoped ENNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SwarmActualHfull

open SimJump SwarmChainRegen SwarmConcat SwarmFinFuture SwarmFreshCompose

variable {N : ℕ}

/-- The extended-natural raw first regeneration level is finite exactly when
there is a positive-level regeneration in the selector's path language. -/
theorem raw_D_ne_top_iff_exists_isRegen [Nonempty (Fin N)] (X : RegenPath.Path N)
    (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1) :
    RegenPath.D X ≠ ⊤ ↔
      ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ SwarmSel.isRegen t d X := by
  classical
  constructor
  · intro hD
    have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := by
      by_contra h
      apply hD
      simp [RegenPath.D, h]
    obtain ⟨r, hr, t, htau, hat, hstay⟩ := hex
    refine ⟨t, (r : ℤ), by exact_mod_cast hr, ?_, hstay⟩
    have ht := RegenPath.tau_eq_iff.mp htau
    refine ⟨?_, hat⟩
    intro s hs i
    by_contra hnot
    have hne := ht.2 s hs i
    have hgt : (r : ℤ) < X s i := by omega
    obtain ⟨n, hn, hhit⟩ := RegenPath.exists_lt_of_reaches
      (f := fun u => X u i) (hX0 i) (fun u => hNN u i)
      (s := s) (d := X s i) rfl
      (by exact_mod_cast (show 0 ≤ r by omega)) hgt
    exact ht.2 n (lt_trans hn hs) i hhit
  · rintro ⟨t, d, hd, hrec, hstay⟩
    have htau : RegenPath.tau X d = (t : ℕ∞) := by
      apply RegenPath.tau_eq_iff.mpr
      refine ⟨⟨Classical.choice inferInstance, hrec.2 _⟩, ?_⟩
      intro n hn i
      exact ne_of_lt (hrec.1 n hn i)
    have hreg : RegenPath.Reg X d := ⟨t, htau, hrec.2, hstay⟩
    have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := by
      refine ⟨d.toNat, by omega, ?_⟩
      have hdcast : (d.toNat : ℤ) = d := by omega
      rwa [hdcast]
    have hfind : RegenPath.D X = (Nat.find hex : ℕ∞) := by
      simp [RegenPath.D, hex]
    rw [hfind]
    simp

/-- The exact no-positive-regeneration event used by `full_iff_noRegen_null`
is the strict-path event `D = ⊤`. -/
theorem noRegen_seed_eq_D_top (X : RegenPath.Path N) [Nonempty (Fin N)]
    (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1) :
    (¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ SwarmSel.isRegen t d X) ↔
      RegenPath.D X = ⊤ := by
  have h := not_congr (raw_D_ne_top_iff_exists_isRegen X hX0 hNN)
  simpa only [not_not] using h.symm

/-- A genuine invariant stopped-record law proves the one-stage fullness
statement for the actual array.  Strict positivity of `π(srSet)` is derived
from invariance by the integrated force estimate.  The proof then transports
canonical Poincaré recurrence through the exact strict-path mass identity; it
does not identify the raw array measure with a stationary law. -/
theorem full_selection_of_invariant {m : ℕ} (hm : 1 ≤ m) {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hN : 0 < N)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmSelInd.seed} := by
  have hπ : 0 < π (SwarmRec.srSet N m) :=
    RecKernel.invariant_srSet_pos p hp0.le hp1.le hp1 hm hN π hinv
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp0.le hp1.le π
  let μ := SwarmChainAssemble.chainLaw
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ := by
    dsimp [μ]
    exact SwarmInfSeg.measurePreserving_chainLaw_shift p hm hp0.le hp1.le π hinv
  have hDmeas : MeasurableSet {X : RegenPath.Path N | RegenPath.D X = ⊤} :=
    SwarmChainRegen.measurable_raw_D (measurableSet_singleton ⊤)
  have hraw : (μ.restrict Chain.A)
      (chainPath ⁻¹' {X : RegenPath.Path N | RegenPath.D X = ⊤}) = 0 := by
    change (μ.restrict Chain.A) {c | RegenPath.D (chainPath c) = ⊤} = 0
    have h := SwarmChainRegen.ae_raw_D_ne_top_onA μ hmp
    rw [ae_iff] at h
    simpa only [Set.mem_ofPred_eq, not_not] using h
  have hprod : π (SwarmRec.srSet N m) * (arrayMeasure N)
      {U : Array N | SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩
        {X : RegenPath.Path N | RegenPath.D X = ⊤}} = 0 := by
    rw [← SwarmPositiveHorizon.chainLaw_hstruct p hm hp0 hp1 π _ hDmeas]
    change μ (Chain.A ∩ chainPath ⁻¹'
      {X : RegenPath.Path N | RegenPath.D X = ⊤}) = 0
    rw [Set.inter_comm, ← Measure.restrict_apply (measurable_chainPath hDmeas)]
    exact hraw
  have hstrict : (arrayMeasure N)
      {U : Array N | SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩
        {X : RegenPath.Path N | RegenPath.D X = ⊤}} = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hπ.ne'
  apply (SwarmSelInd.full_iff_noRegen_null (p := p) (m := m) hN).mpr
  have hset : {U : Array N | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed ∧
        ¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧
          SwarmSel.isRegen t d (SwarmRestart.posPath p m U)} =
      {U : Array N | SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩
        {X : RegenPath.Path N | RegenPath.D X = ⊤}} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hseed, hno⟩
      exact ⟨hseed, (noRegen_seed_eq_D_top _ (SwarmFresh.posPath_zero p m U)
        (fun n i => SwarmFresh.posPath_step p m U n i)).mp hno⟩
    · rintro ⟨hseed, htop⟩
      exact ⟨hseed, (noRegen_seed_eq_D_top _ (SwarmFresh.posPath_zero p m U)
        (fun n i => SwarmFresh.posPath_step p m U n i)).mpr htop⟩
  rw [hset]
  exact hstrict

/-- Paper-parameter form: a genuine invariant record law yields exactly the
`hfull` consumed by `SelectedBlockLaw.map_selectedBlocks_seedLaw_actual`. -/
theorem full_selection_actual_of_invariant {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed} :=
  full_selection_of_invariant (by omega) hp0 hp1 (by omega) π hinv

/-- The same one-stage fullness conclusion from tightness of the genuine
stopped-record iterates.  Tightness is used only to construct an invariant
law, not as an additional regeneration hypothesis. -/
theorem full_selection_of_tight {m : ℕ} (hm : 1 ≤ m) {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hN : 0 < N)
    (μ₀ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ₀]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (RecKernel.hitKKernel (N := N) (m := m) p hm))^[r]
        μ₀ (SwarmRec.exh N m K)ᶜ ≤ ε) :
    (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed} := by
  obtain ⟨π, hprob, hinv, -⟩ :=
    RecKernel.exists_invariant_measure_pos_hitKInf_feller
      (N := N) (m := m) p hp0.le hp1.le hp1 hm hN μ₀ htight
  letI : IsProbabilityMeasure π := hprob
  exact full_selection_of_invariant hm hp0 hp1 hN π hinv

end SwarmActualHfull
