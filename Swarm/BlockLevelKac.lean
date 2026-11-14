/-
The actual selected-block level is integrable from a genuine invariant record law.

The proof transports the normalized fresh-path Kac bound through the first
selected-block atoms.  It never identifies level with elapsed walk time.
-/
import Swarm.StationaryRecordKac
import Swarm.FBLaw
import Swarm.HfullBridge

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmChain
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BlockLevelKac

open SimJump SwarmChainRegen SwarmFreshCompose

variable {N : ℕ}

/-- A selector regeneration is a regeneration in the raw-path language. -/
theorem reg_of_isRegen [Nonempty (Fin N)] {X : RegenPath.Path N}
    {t : ℕ} {d : ℤ} (h : SwarmSel.isRegen t d X) : RegenPath.Reg X d := by
  refine ⟨t, RegenPath.tau_eq_iff.mpr ⟨?_, ?_⟩, h.1.2, h.2⟩
  · exact ⟨Classical.choice inferInstance, h.1.2 _⟩
  · intro n hn i
    exact ne_of_lt (h.1.1 n hn i)

/-- A raw regeneration at a positive natural level is a selector regeneration.
The nearest-neighbour hypothesis is used only to make the prefix strictly
below the first-hit level. -/
theorem exists_isRegen_of_reg [Nonempty (Fin N)] (X : RegenPath.Path N)
    (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1)
    {r : ℕ} (hr : 1 ≤ r) (h : RegenPath.Reg X (r : ℤ)) :
    ∃ t : ℕ, SwarmSel.isRegen t (r : ℤ) X := by
  obtain ⟨t, htau, hat, hstay⟩ := h
  refine ⟨t, ?_, hstay⟩
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

/-- On a genuine selected first-block event, the raw first regeneration level
is exactly that block's level.  This also excludes the no-return fallback. -/
theorem firstRegenLevel_eq_of_firstRegen [Nonempty (Fin N)] (X : RegenPath.Path N)
    (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1)
    {t d : ℕ} (hd : 1 ≤ d)
    (hfr : X ∈ SwarmSel.firstRegen t (d : ℤ)) :
    SwarmChainRegen.firstRegenLevel X = d := by
  classical
  rw [SwarmSel.mem_firstRegen_iff] at hfr
  obtain ⟨⟨hrec, hpos, hno⟩, hregD⟩ := hfr
  have hregDraw : RegenPath.Reg X (d : ℤ) := reg_of_isRegen hregD
  let hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := ⟨d, hd, hregDraw⟩
  have hle : Nat.find hex ≤ d := Nat.find_min' hex ⟨hd, hregDraw⟩
  have hge : d ≤ Nat.find hex := by
    by_contra hcon
    have hed : Nat.find hex < d := by omega
    have he1 : 1 ≤ Nat.find hex := (Nat.find_spec hex).1
    obtain ⟨u, hregE⟩ := exists_isRegen_of_reg X hX0 hNN he1 (Nat.find_spec hex).2
    have hut : u < t := by
      by_contra hnot
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin N))
      by_cases hut' : t = u
      · subst u
        have hDi := hregD.1.2 i
        have hEi := hregE.1.2 i
        omega
      · have htui : t < u := by omega
        have hDi := hregD.2 u htui i
        have hEi := hregE.1.2 i
        omega
    obtain ⟨n, hun, hnt, i, hi⟩ := hno (Nat.find hex : ℤ)
      (by exact_mod_cast he1) (by exact_mod_cast hed) u hut hregE.1
    have hafter := hregE.2 n hun i
    omega
  have hfind : Nat.find hex = d := le_antisymm hle hge
  rw [SwarmChainRegen.firstRegenLevel_eq_find X hex, hfind]

/-- The normalized strict-path law is the path pushforward of the actual
seed-conditioned array measure. -/
theorem map_posPath_seedCond (p : ℝ) (m : ℕ) :
    (SwarmFB.seedCond (p := p) (m := m) (N := N)).map (SwarmRestart.posPath p m) =
      ((SwarmFreshCompose.strictLaw p m N Set.univ)⁻¹ •
        SwarmFreshCompose.strictLaw p m N) := by
  have hfresh :
      ((arrayMeasure N).restrict (SwarmFB.seedSet (p := p) (m := m) (N := N))).map
          (SwarmRestart.posPath p m) = SwarmFreshCompose.strictLaw p m N := by
    rw [SwarmFreshCompose.strictLaw, Measure.restrict_map
      (SwarmRestart.measurable_posPath p m N) SwarmFresh.measurableSet_strictPos]
    rfl
  rw [SwarmFB.seedCond, ProbabilityTheory.cond, Measure.map_smul, hfresh,
    SwarmFreshCompose.strictLaw_univ]
  rfl

variable {p : ℝ} {m : ℕ}

/-- Exact level identity on a one-block atom. -/
theorem blkLevelR_Z_zero_of_mem_atom (hN : 0 < N)
    {L : Fin 1 → ℕ × ℕ} {U : Array N}
    (hU : U ∈ SwarmFB.Atom (p := p) (m := m) (N := N) L) :
    SwarmFB.blkLevelR (SwarmFB.Z (p := p) (m := m) (N := N) 0 U) =
      (SwarmChainRegen.firstRegenLevel (SwarmRestart.posPath p m U) : ℝ) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hZ : SwarmFB.Z (p := p) (m := m) (N := N) 0 U = L 0 := by
    simpa using SwarmFB.Z_eq_of_mem_atom (p := p) (m := m) (N := N) hN L hU 0
  have hlist : SwarmFB.idxList L = [((L 0).1, SwarmFB.blkLevel (L 0))] := by
    simp [SwarmFB.idxList, List.ofFn_succ]
  rw [SwarmFB.Atom, hlist, SwarmSelInd.AchainIdx] at hU
  have hfr := (SwarmSelInd.mem_Hidx_cons.mp hU).2.1
  have hfr' : SwarmRestart.posPath p m U ∈
      SwarmSel.firstRegen (L 0).1 (((L 0).2 + 1 : ℕ) : ℤ) := by
    simpa [SwarmFB.blkLevel, Nat.cast_add, Nat.cast_one] using hfr
  have hlevel := firstRegenLevel_eq_of_firstRegen
    (N := N) (SwarmRestart.posPath p m U)
    (SwarmFresh.posPath_zero p m U)
    (fun n i => SwarmFresh.posPath_step p m U n i)
    (t := (L 0).1) (d := (L 0).2 + 1) (by omega) hfr'
  rw [hZ]
  simp [SwarmFB.blkLevelR, hlevel]

/-- The default first-block value cannot affect the level identity: `hfull`
makes the one-chain event full measure under `seedCond`. -/
theorem ae_blkLevelR_Z_zero (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    (fun U => SwarmFB.blkLevelR (SwarmFB.Z (p := p) (m := m) (N := N) 0 U)) =ᵐ[
      SwarmFB.seedCond (p := p) (m := m) (N := N)]
      (fun U => (SwarmChainRegen.firstRegenLevel (SwarmRestart.posPath p m U) : ℝ)) := by
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  have hprob : SwarmFB.seedCond (p := p) (m := m) (N := N)
      (SwarmSelInd.Achain p m N 1 Set.univ) = 1 :=
    SwarmFB.seedCond_chain (p := p) (m := m) hN hfull h0 1
  have hchain : ∀ᵐ U ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)),
      U ∈ SwarmSelInd.Achain p m N 1 Set.univ :=
    (mem_ae_iff_prob_eq_one
      (SwarmSelInd.measurableSet_Achain 1 MeasurableSet.univ)).mpr hprob
  filter_upwards [hchain] with U hU
  have hU' : U ∈ ⋃ L : Fin 1 → ℕ × ℕ,
      SwarmFB.Atom (p := p) (m := m) (N := N) L := by
    rw [SwarmFB.iUnion_atom_eq (p := p) (m := m) (N := N)]
    exact hU
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  exact blkLevelR_Z_zero_of_mem_atom (p := p) (m := m) hN hL

/-- Genuine invariant `hitKKernel` record law implies the actual one-block
level integrability required by `NeutralRegenLaw`. -/
theorem integrable_blkLevelR_of_invariant
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    Integrable SwarmFB.blkLevelR (SwarmFB.Q (p := p) (m := m) (N := N)) := by
  have hπ : 0 < π (SwarmRec.srSet N m) :=
    RecKernel.invariant_srSet_pos p hp0.le hp1.le hp1 (by omega) (by omega) π hinv
  obtain ⟨hint, -, -⟩ :=
    SwarmChainRegen.chainLaw_firstRegenLevel_mean_bound_model
      (N := N) (m := m) hm hN hp0 hp1 π hinv hπ
  have hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) := by
    simpa only [SwarmFB.seedSet] using
      (SwarmActualHfull.full_selection_actual_of_invariant
        (N := N) (m := m) hp0 hp1 hm hN π hinv)
  have h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 := by
    unfold SwarmFB.seedSet
    exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  have hmap := map_posPath_seedCond (N := N) p m
  rw [← hmap] at hint
  have hraw : Integrable
      (fun U => (SwarmChainRegen.firstRegenLevel (SwarmRestart.posPath p m U) : ℝ))
      (SwarmFB.seedCond (p := p) (m := m) (N := N)) := by
    simpa only [Function.comp_def] using
      hint.comp_measurable (SwarmRestart.measurable_posPath p m N)
  have hblock : Integrable
      (fun U => SwarmFB.blkLevelR (SwarmFB.Z (p := p) (m := m) (N := N) 0 U))
      (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    hraw.congr (ae_blkLevelR_Z_zero (p := p) (m := m) (by omega) hfull h0).symm
  have hQ : Integrable SwarmFB.blkLevelR
      ((SwarmFB.seedCond (p := p) (m := m) (N := N)).map
        (SwarmFB.Z (p := p) (m := m) (N := N) 0)) := by
    apply (integrable_map_measure SwarmFB.measurable_blkLevelR.aestronglyMeasurable
      (SwarmFB.measurable_Z (p := p) (m := m) (by omega) 0).aemeasurable).2
    simpa only [Function.comp_def] using hblock
  rwa [SwarmFB.map_Z (p := p) (m := m) (by omega) hfull h0 0] at hQ

end BlockLevelKac
