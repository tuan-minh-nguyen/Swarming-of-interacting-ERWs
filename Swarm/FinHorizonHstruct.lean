/-`Swarm/DHStruct.lean` shows that the paper's structural display

  `hstruct : μ (A ∩ Φ ⁻¹' B) = ∫⁻ y in F, P_y (V ∩ B) ∂π`

(with `A = Φ ⁻¹' strictPos`, `strictPos = V`) is *one* path-mass identity, and
`Swarm/ChainAssemble.lean` (`chain_hstruct_iff_stateMass`) plus
`Swarm/FreshState.lean` (`fresh_mass_integral_srSet`) compute the right-hand side down to
`π(F) · P(V ∩ B)`.  What is left is the *chain side*: the mass of the concatenated path lying in
`V ∩ B`.  `V = strictPos` contains the infinite-time condition `X_n^i > 0` for every `n ≥ 1`, so
no finite-horizon statement is literally equivalent to it.  This file isolates the exact finite
substitute.

* **§1** `finStrict K` is `V` truncated at horizon `K`: `X 0 ≡ 0` (the paper's `Y_0 ∈ F`, read in
  path coordinates — this is what `strictPos` means at `n = 0`) together with `X_n^i > 0` for
  `1 ≤ n ≤ K`.  `finStrict` is antitone and `⋂ K, finStrict K = strictPos`; it is measurable.

* **§2** `finHorizon_to_strictPos`: if two finite measures agree on `finStrict K ∩ B` for every
  `K` and every measurable `B`, they agree on `strictPos ∩ B`.  The proof is continuity from above
  (`Antitone.measure_iInter`) on both sides; the two sequences are decreasing, both measures are
  finite, so nothing else is needed — in particular no "thin set" or compactness argument.

* **§3** `hstruct_of_finHorizon`: consequently the whole of `hstruct` (in the `∫⁻`-form consumed by
  `FreshCompose.record_ED_of_fresh`, and equivalently in the `π(F)·P(V∩B)` form of
  `ChainAssemble.chain_hstruct_iff_stateMass`) follows from the single family of *finite-horizon*
  identities

    `(★ K)  μ (Φ ⁻¹' (finStrict K ∩ B)) = π(F) · P(posPath ∈ finStrict K ∩ B)`.

  `(★ K)` is the exact residual: it is a statement about the first `K` raw steps only, it is not
  implied by stationarity or by compatibility, and it is *not* a trivial consequence of `hstruct`
  (the left-hand side of `hstruct` does not shrink with `K`; `(★ K)` restricts the path instead).

* **§4** `horizWeight_eq(_of_srSet)`: the finite-horizon fresh weight with an arbitrary pattern
  cylinder is state independent on the fresh starts (hence on `srSet`), at every `K`.  This is the
  finite-array input that makes `(★ K)` a *single* number identity rather than a state-dependent
  one: the right-hand side of `(★ K)` does not depend on which `y ∈ F` drives the record chain.

Scope.  No invariant record law, no tightness, no `RegenAvail`, no block tails and no speed are
claimed or used; `π` is an arbitrary probability measure on record states with `π(F) > 0`, exactly
as in `FreshCompose`.  `hstruct` itself is *not* proved: §3 proves that it follows from `(★ K)`
for all `K`, and §4 supplies the state-independence half of `(★ K)`.
-/
import Swarm.FreshCompose
import Swarm.FreshArrayBridge

open MeasureTheory Set
open scoped ENNReal
open SimJump
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRec SwarmFresh SwarmFreshPos

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFinHorizon

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-! ## 1. The horizon-`K` truncation of `V = strictPos` -/

/-- **The `K`-horizon strict positivity event.**  `X 0 ≡ 0` is the paper's `Y_0 ∈ F` read on the
path (this is the `n = 0` half of `strictPos`), and every walker is strictly above the record level
at every positive time up to `K`. -/
def finStrict (K : ℕ) : Set (ℕ → Fin N → ℤ) :=
  {X | (∀ i, X 0 i = 0) ∧ ∀ (n : ℕ), 0 < n → n ≤ K → ∀ i, 0 < X n i}

theorem mem_finStrict {K : ℕ} {X : ℕ → Fin N → ℤ} :
    X ∈ finStrict (N := N) K ↔
      (∀ i, X 0 i = 0) ∧ ∀ (n : ℕ), 0 < n → n ≤ K → ∀ i, 0 < X n i :=
  Iff.rfl

/-- `strictPos` implies `finStrict K`: `finStrict` is a truncation, not a different event. -/
theorem strictPos_subset_finStrict (K : ℕ) :
    strictPos (N := N) ⊆ finStrict (N := N) K := by
  rintro X hX
  rw [mem_strictPos] at hX
  exact mem_finStrict.mpr ⟨hX.1, fun n hn _ i => hX.2 n hn i⟩

theorem finStrict_antitone : Antitone (fun K => finStrict (N := N) K) := by
  intro K L hKL X hX
  refine mem_finStrict.mpr ⟨hX.1, fun n hn hnK i => hX.2 n hn (le_trans hnK hKL) i⟩

/-- The truncations recover `strictPos` exactly. -/
theorem iInter_finStrict : (⋂ K, finStrict (N := N) K) = strictPos (N := N) := by
  ext X
  simp only [mem_iInter, mem_finStrict, mem_strictPos]
  constructor
  · intro h
    refine ⟨(h 0).1, fun n hn i => ?_⟩
    exact (h n).2 n hn (Nat.le_refl n) i
  · rintro ⟨h0, hpos⟩ n
    refine ⟨h0, fun k hk _ i => ?_⟩
    exact hpos k hk i

theorem measurable_eval (n : ℕ) (i : Fin N) :
    Measurable fun X : ℕ → Fin N → ℤ => X n i :=
  (measurable_pi_apply i).comp (measurable_pi_apply n)

theorem measurableSet_finStrict (K : ℕ) : MeasurableSet (finStrict (N := N) K) := by
  have heq : finStrict (N := N) K =
      {X : ℕ → Fin N → ℤ | ∀ i, X 0 i = 0} ∩
        ⋂ (n : {n : Fin (K + 1) // 0 < (n : ℕ)}), ⋂ i : Fin N, {X | 0 < X (n.1 : ℕ) i} := by
    ext X
    simp only [mem_finStrict, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro ⟨h0, hpos⟩
      exact ⟨h0, fun n i => hpos (n.1 : ℕ) n.2 (by have := n.1.2; omega) i⟩
    · rintro ⟨h0, hpos⟩
      refine ⟨h0, fun n hn hnK i => ?_⟩
      exact hpos ⟨⟨n, by omega⟩, hn⟩ i
  rw [heq]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_)
  · have hz : {X : ℕ → Fin N → ℤ | ∀ i, X 0 i = 0} = ⋂ i, {X | X 0 i = 0} := by
      ext X
      simp
    rw [hz]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (measurable_eval (N := N) 0 i) measurable_const
  · exact measurableSet_lt measurable_const (measurable_eval (N := N) (n.1 : ℕ) i)

/-! ## 2. Continuity from above: the truncations carry the whole `strictPos` mass -/

/-- **The limit step.**  Two finite measures on path space that agree on every finite-horizon
cylinder `finStrict K ∩ B` agree on `strictPos ∩ B`.  No countability, thin-set or compactness
input is used: `finStrict K` decreases to `strictPos`, and both sides are continuous from above. -/
theorem finHorizon_to_strictPos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    {ν : Measure (ℕ → Fin N → ℤ)} [IsFiniteMeasure ν] (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : ∀ (K : ℕ) (B : Set (ℕ → Fin N → ℤ)), MeasurableSet B →
        μ (Φ ⁻¹' (finStrict (N := N) K ∩ B)) = c * ν (finStrict (N := N) K ∩ B)) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (Φ ⁻¹' (strictPos (N := N) ∩ B)) = c * ν (strictPos (N := N) ∩ B) := by
  intro B hB
  have hanti : Antitone fun K => finStrict (N := N) K ∩ B :=
    fun K L hKL => Set.inter_subset_inter_left _ (finStrict_antitone hKL)
  have hmeas : ∀ K, MeasurableSet (finStrict (N := N) K ∩ B) :=
    fun K => (measurableSet_finStrict K).inter hB
  have hInter : (⋂ K, (finStrict (N := N) K ∩ B)) = strictPos (N := N) ∩ B := by
    rw [← Set.iInter_inter, iInter_finStrict]
  have h1 : μ (Φ ⁻¹' (⋂ K, (finStrict (N := N) K ∩ B)))
      = ⨅ K, μ (Φ ⁻¹' (finStrict (N := N) K ∩ B)) := by
    rw [Set.preimage_iInter]
    refine Antitone.measure_iInter (fun K L hKL => Set.preimage_mono (hanti hKL))
      (fun K => (hΦ (hmeas K)).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  have h2 : (⨅ K, μ (Φ ⁻¹' (finStrict (N := N) K ∩ B)))
      = ⨅ K, c * ν (finStrict (N := N) K ∩ B) :=
    iInf_congr fun K => h K B hB
  have h3 : ν (⋂ K, (finStrict (N := N) K ∩ B))
      = ⨅ K, ν (finStrict (N := N) K ∩ B) :=
    Antitone.measure_iInter hanti (fun K => (hmeas K).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have h4 : c * (⨅ K, ν (finStrict (N := N) K ∩ B))
      = ⨅ K, c * ν (finStrict (N := N) K ∩ B) :=
    ENNReal.mul_iInf_of_ne hc0 hct
  calc μ (Φ ⁻¹' (strictPos (N := N) ∩ B))
      = μ (Φ ⁻¹' (⋂ K, (finStrict (N := N) K ∩ B))) := by rw [hInter]
    _ = ⨅ K, μ (Φ ⁻¹' (finStrict (N := N) K ∩ B)) := h1
    _ = ⨅ K, c * ν (finStrict (N := N) K ∩ B) := h2
    _ = c * (⨅ K, ν (finStrict (N := N) K ∩ B)) := h4.symm
    _ = c * ν (⋂ K, (finStrict (N := N) K ∩ B)) := by rw [h3]
    _ = c * ν (strictPos (N := N) ∩ B) := by rw [hInter]

/-! ## 3. `hstruct` follows from the finite-horizon family `(★ K)` -/

/-- **The finite-horizon prefix of `hstruct`, and its exact consequence.**

`(★ K)` (`h` below) says that for every `K` and every measurable `B` the mass of "the concatenated
path lies in the first-`K`-steps strict positivity event" is `π(F)` times the model's fresh
`K`-step mass.  It is a finite-dimensional statement: `finStrict K` reads the first `K` steps
only, and `P(posPath ∈ finStrict K ∩ B)` is a finite-horizon fresh mass.

The theorem proves that this family implies the (`∫⁻`-form) `hstruct` — with an *arbitrary*
probability `π` on record states and no invariant law, stationarity or tightness input.  The bridge
from the `π(F)·P(V ∩ B)` form to this `∫⁻`-form is `FreshState.fresh_mass_integral_srSet`; the
bridge from `A` to `Φ ⁻¹' strictPos` is the definitional identification `A = Φ ⁻¹' V` of
`DHStruct.ChainStep.A_eq_preimage`. -/
theorem hstruct_of_finHorizon [IsProbabilityMeasure (arrayMeasure N)] (hm : 1 ≤ m) (p : ℝ)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] (hπ : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (A : Set Ω) (hA : A = Φ ⁻¹' strictPos (N := N))
    (h : ∀ (K : ℕ) (B : Set (ℕ → Fin N → ℤ)), MeasurableSet B →
        μ (Φ ⁻¹' (finStrict (N := N) K ∩ B))
          = π (srSet N m) * (arrayMeasure N)
              {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ B}) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B)
        = ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
            SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y) ∧
              (fun n i => (trajFrom p m U (SwarmFreshState.walkStateOf y) n).pos i) ∈ B} ∂π := by
  have hfin : IsFiniteMeasure ((arrayMeasure N).map (posPath p m)) :=
    ⟨by rw [Measure.map_apply (measurable_posPath p m N) MeasurableSet.univ]; simp⟩
  haveI := hfin
  have hν : ∀ (K : ℕ) (B : Set (ℕ → Fin N → ℤ)), MeasurableSet B →
      ((arrayMeasure N).map (posPath p m)) (finStrict (N := N) K ∩ B)
        = (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ B} := by
    intro K B hB
    rw [Measure.map_apply (measurable_posPath p m N) ((measurableSet_finStrict K).inter hB)]
    rfl
  have hlim := finHorizon_to_strictPos (N := N) Φ hΦ
    (ν := (arrayMeasure N).map (posPath p m)) (c := π (srSet N m))
    (ne_of_gt hπ) (measure_ne_top _ _)
    (fun K B hB => by rw [h K B hB, hν K B hB])
  intro B hB
  have hAeq : A ∩ Φ ⁻¹' B = Φ ⁻¹' (strictPos (N := N) ∩ B) := by
    rw [hA, ← Set.preimage_inter]
  have hνS : ((arrayMeasure N).map (posPath p m)) (strictPos (N := N) ∩ B)
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
    rw [Measure.map_apply (measurable_posPath p m N) (measurableSet_strictPos.inter hB)]
    rfl
  rw [hAeq, hlim B hB, hνS,
    ← SwarmFreshState.fresh_mass_integral_srSet (N := N) hm p π (B := B)]

/-- **The `π(F)·P(V ∩ B)` form** of `hstruct`, i.e. the shape consumed by
`ChainAssemble.chain_hstruct_iff_stateMass` and by the Kac step: under the finite-horizon family
`(★ K)` the left-hand side collapses to the single number `π(F) · P(posPath ∈ V ∩ B)`. -/
theorem hstruct_mass_form_of_finHorizon [IsProbabilityMeasure (arrayMeasure N)] (hm : 1 ≤ m)
    (p : ℝ) (π : Measure (RecState N m)) [IsProbabilityMeasure π] (hπ : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (A : Set Ω) (hA : A = Φ ⁻¹' strictPos (N := N))
    (h : ∀ (K : ℕ) (B : Set (ℕ → Fin N → ℤ)), MeasurableSet B →
        μ (Φ ⁻¹' (finStrict (N := N) K ∩ B))
          = π (srSet N m) * (arrayMeasure N)
              {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ B}) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B)
        = π (srSet N m) * (arrayMeasure N)
            {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  have hmain := hstruct_of_finHorizon (N := N) hm p π hπ Φ hΦ A hA h
  intro B hB
  rw [hmain B hB, SwarmFreshState.fresh_mass_integral_srSet (N := N) hm p π (B := B)]

/-! ## 4. The horizon-`K` fresh weight is state independent on the fresh starts -/

/-- The `K`-horizon position pattern of a jump word: the positions at times `0, …, K`. -/
noncomputable def patOf {K : ℕ} (q : Fin K → JumpVec N) (n : Fin (K + 1)) (i : Fin N) : ℤ :=
  posAt (seqOf q) (n : ℕ) i

/-- **The finite-horizon fresh weight of an arbitrary pattern cylinder is the same at every fresh
start.**  `K` jumps, restricted to the words that never return to the level at times `≤ K` and
whose `K`-horizon pattern lies in `C`.  This is the finite-horizon, arbitrary-cylinder form of
`FreshPos.positive_mass_eq` (which is the case `C = univ`), and it is the array-side input of
`(★ K)`: the right-hand side of `(★ K)` is a single number, independent of the record state that
drives the chain. -/
theorem horizWeight_eq {p : ℝ} {s s' : State N m} (hs : FreshStart s) (hs' : FreshStart s')
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (∑ q : Fin K → JumpVec N,
        if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
          then ENNReal.ofReal (pathW p K q s) else 0)
      = ∑ q : Fin K → JumpVec N,
        if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
          then ENNReal.ofReal (pathW p K q s') else 0 := by
  classical
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
  · rw [if_pos hq, if_pos hq, SwarmFreshCyl.pathW_eq_fresh p hs hs' q hq.1]
  · rw [if_neg hq, if_neg hq]

/-- The same statement on the simultaneous-record set `F = srSet`: the finite-horizon fresh weight
does not depend on which `y ∈ F` the record chain starts from. -/
theorem horizWeight_eq_of_srSet {p : ℝ} (hm : 1 ≤ m) {y y' : RecState N m} (hy : y ∈ srSet N m)
    (hy' : y' ∈ srSet N m) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (∑ q : Fin K → JumpVec N,
        if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
          then ENNReal.ofReal (pathW p K q (Record.ofRecState y)) else 0)
      = ∑ q : Fin K → JumpVec N,
        if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
          then ENNReal.ofReal (pathW p K q (Record.ofRecState y')) else 0 :=
  horizWeight_eq (N := N) (freshStart_ofRecState hy hm) (freshStart_ofRecState hy' hm) K C


/-! ## 5. The finite-horizon fresh identity on the actual array trajectories

`FreshState.fresh_set_eq_srSet` is an identity of *sets*: from any `y ∈ F` the event "the future
stays strictly above the record level (for ever) and the translated path lies in `B`" is literally
the canonical fresh event `posPath ∈ V ∩ B`.  Its proof needs positivity at every time (the
agreement induction is driven by "the walkers never go below the level").  Here is the horizon-`K`
version: the *finite* event "stays strictly above the level at times `1, …, K` and the first `K`
positions lie in `C`" is again the same set at every `y ∈ F` and at the canonical start.  This is
the array-side half of the finite-horizon identity `(★ K)`: the `K`-step fresh mass does not depend
on the record state, so `(★ K)`'s right-hand side is one number. -/

/-- Strict positivity of the trajectory from a walk state at positive times up to the horizon
`K`.  The horizon truncation of `SwarmFreshState.FromV`. -/
def FromVupto {N : ℕ} (p : ℝ) (m : ℕ) (K : ℕ) (U : Array N) (s : WalkState N) : Prop :=
  ∀ (i : Fin N) (n : ℕ), 0 < n → n ≤ K → 0 < (trajFrom p m U s n).pos i

/-- The first `K+1` positions of a path, as a single finite pattern. -/
def pathPat {N : ℕ} (K : ℕ) (X : ℕ → Fin N → ℤ) : Fin (K + 1) → Fin N → ℤ :=
  fun n i => X (n : ℕ) i

/-- The first `K+1` positions of the trajectory from a walk state. -/
noncomputable def trajPat {N : ℕ} (p : ℝ) (m : ℕ) (K : ℕ) (U : Array N) (s : WalkState N) :
    Fin (K + 1) → Fin N → ℤ :=
  fun n i => (trajFrom p m U s (n : ℕ)).pos i

/-- **Agreement up to the horizon.**  Two starts with the same record profile have the same
positions (and the same local times at every site at or above the level) at every time `≤ K`, as
long as *one* of them stays strictly above the level up to `K`.  This is `FreshState`'s
`agree_above_upto` with the infinite positivity hypothesis replaced by its horizon truncation and
the nonnegativity of the second trajectory derived from the agreement itself. -/
theorem agree_upto_of_pos {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {s s' : WalkState N}
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x)
    (h0 : ∀ i, s.pos i = 0) (K : ℕ)
    (hV : FromVupto (N := N) p m K U s) :
    ∀ n, n ≤ K →
      ((∀ i, (trajFrom p m U s n).pos i = (trajFrom p m U s' n).pos i) ∧
        ∀ (i : Fin N) (x : ℤ), 0 ≤ x →
          (trajFrom p m U s n).ell i x = (trajFrom p m U s' n).ell i x) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hpos, hell⟩
  | succ n ih =>
      intro hnK
      obtain ⟨hp, he⟩ := ih (by omega)
      have hge : ∀ i, 0 ≤ (trajFrom p m U s n).pos i := by
        intro i
        rcases Nat.eq_zero_or_pos n with hz | hnp
        · subst hz
          rw [trajFrom_zero]
          exact le_of_eq (h0 i).symm
        · exact le_of_lt (hV i n hnp (by omega))
      have hstep := nextWalkState_agreeAbove (p := p) (m := m) (U := U) (U' := U)
        (s := trajFrom p m U s n) (s' := trajFrom p m U s' n)
        (fun _ _ _ _ => rfl) hp he hge
      refine ⟨?_, ?_⟩
      · rw [trajFrom_succ, trajFrom_succ]
        exact hstep.1
      · intro i x hx
        rw [trajFrom_succ, trajFrom_succ]
        exact hstep.2 i x hx

/-- The position paths agree up to the horizon. -/
theorem pos_eq_upto_of_pos {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {s s' : WalkState N}
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x)
    (h0 : ∀ i, s.pos i = 0) (K : ℕ) (hV : FromVupto (N := N) p m K U s) :
    ∀ n, n ≤ K → ∀ i, (trajFrom p m U s n).pos i = (trajFrom p m U s' n).pos i :=
  fun n hn i => (agree_upto_of_pos hpos hell h0 K hV n hn).1 i

/-- **The horizon-`K` event identity.**  Same record profile ⇒ the same finite event "strictly
above the level at times `1, …, K` and first `K` positions in `C`". -/
theorem fresh_set_eq_upto {N : ℕ} {p : ℝ} {m : ℕ} {s s' : WalkState N}
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x)
    (h0 : ∀ i, s.pos i = 0) (h0' : ∀ i, s'.pos i = 0) (K : ℕ)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    {U : Array N | FromVupto (N := N) p m K U s ∧ trajPat (N := N) p m K U s ∈ C}
      = {U : Array N | FromVupto (N := N) p m K U s' ∧ trajPat (N := N) p m K U s' ∈ C} := by
  ext U
  constructor
  · rintro ⟨hV, hC⟩
    have hpe := pos_eq_upto_of_pos hpos hell h0 K hV
    refine ⟨fun i n hn hnK => ?_, ?_⟩
    · rw [← hpe n (by omega) i]
      exact hV i n hn hnK
    · have hfun : trajPat (N := N) p m K U s = trajPat (N := N) p m K U s' := by
        funext n i
        exact hpe (n : ℕ) (by have := n.2; omega) i
      rw [← hfun]
      exact hC
  · rintro ⟨hV, hC⟩
    have hpe := pos_eq_upto_of_pos (s := s') (s' := s) (fun i => (hpos i).symm)
      (fun i x hx => (hell i x hx).symm) h0' K hV
    refine ⟨fun i n hn hnK => ?_, ?_⟩
    · rw [← hpe n (by omega) i]
      exact hV i n hn hnK
    · have hfun : trajPat (N := N) p m K U s' = trajPat (N := N) p m K U s := by
        funext n i
        exact hpe (n : ℕ) (by have := n.2; omega) i
      rw [← hfun]
      exact hC

/-- The canonical trajectory's path is `posPath`. -/
theorem trajFrom_initial_eq_posPath {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) :
    (fun (n : ℕ) (i : Fin N) =>
        (trajFrom p m U (initialWalkState (N := N)) n).pos i) = posPath p m U := by
  funext n i
  rw [posPath, trajectory_eq_trajFrom]

/-- On the canonical start, the horizon event is `posPath ∈ finStrict K` together with the pattern
condition. -/
theorem initial_eq_finStrict {N : ℕ} (p : ℝ) (m : ℕ) (K : ℕ)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    {U : Array N | FromVupto (N := N) p m K U (initialWalkState (N := N)) ∧
        trajPat (N := N) p m K U (initialWalkState (N := N)) ∈ C}
      = {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  ext U
  have hp := trajFrom_initial_eq_posPath (N := N) p m U
  have hpat : trajPat (N := N) p m K U (initialWalkState (N := N))
      = pathPat (N := N) K (posPath p m U) := by
    funext n i
    exact congrFun (congrFun hp (n : ℕ)) i
  constructor
  · rintro ⟨hV, hC⟩
    refine ⟨mem_finStrict.mpr ⟨fun i => posPath_zero p m U i, fun n hn hnK i => ?_⟩, ?_⟩
    · rw [← congrFun (congrFun hp n) i]
      exact hV i n hn hnK
    · rw [mem_preimage, ← hpat]
      exact hC
  · rintro ⟨hfin, hC⟩
    obtain ⟨-, hpos⟩ := mem_finStrict.mp hfin
    refine ⟨fun i n hn hnK => ?_, ?_⟩
    · rw [congrFun (congrFun hp n) i]
      exact hpos n hn hnK i
    · rw [mem_preimage] at hC
      rwa [hpat]

/-- **The horizon-`K` fresh event is the canonical one, from any simultaneous record.**  This is
the horizon truncation of `FreshState.fresh_set_eq_srSet`, with the truncation's positivity
hypothesis genuinely finite: no condition on the trajectory after time `K` is used. -/
theorem fresh_set_eq_srSet_upto {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) {y : RecState N m}
    (hy : y ∈ srSet N m) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    {U : Array N | FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
        trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C}
      = {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  obtain ⟨hpos, hell0, hellup⟩ := SwarmFreshState.profile_of_srSet (N := N) hm hy
  have hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x →
      (SwarmFreshState.walkStateOf y).ell i x = (initialWalkState (N := N)).ell i x := by
    intro i x hx
    show (SwarmFreshState.walkStateOf y).ell i x = (if x = 0 then 1 else 0)
    rcases lt_or_eq_of_le hx with hlt | heq
    · rw [hellup i x hlt, if_neg (by omega)]
    · subst heq
      rw [hell0 i, if_pos rfl]
  have h0init : ∀ i, (initialWalkState (N := N)).pos i = 0 := fun i => rfl
  rw [fresh_set_eq_upto hpos hell hpos h0init K C, initial_eq_finStrict]

/-- **The finite-horizon fresh mass identity at actual array trajectories.**  For every `y ∈ F`,
horizon `K` and every pattern cylinder `C` of the first `K+1` positions, the mass under the actual
array law of "the future of the interacting trajectory started from `y` stays strictly above the
record level at times `1, …, K` and its first `K+1` positions lie in `C`" equals the canonical
fresh mass `P(posPath ∈ finStrict K ∩ {first K+1 positions ∈ C})` — with no factor depending on
`y`.  This is the horizon-`K` form of the paper's `P_y(V ∩ B) = P(V ∩ B)`. -/
theorem fresh_mass_finStrict_eq_of_srSet {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) {y : RecState N m}
    (hy : y ∈ srSet N m) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
          trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C}
      = (arrayMeasure N) {U : Array N |
          posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  rw [fresh_set_eq_srSet_upto (N := N) hm p hy K C]


/-! ## 6. The residual family `(★)`, its consistency, and its non-degeneracy -/

/-- **The finite-horizon residual family `(★)`.**  For every `K` and every measurable `B`, the
mass of the first-`K`-steps strict positivity event of the concatenated path is `π(F)` times the
model's own `K`-step fresh mass.  This is the single named input of
`hstruct_of_finHorizon`; it mentions only finite horizons, and it is exactly the statement that
the record chain's first `K` raw steps have the array's fresh law. -/
def FinHorizonFamily {Ω : Type*} [MeasurableSpace Ω] (p : ℝ) (π : Measure (RecState N m))
    (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) : Prop :=
  ∀ (K : ℕ) (B : Set (ℕ → Fin N → ℤ)), MeasurableSet B →
    μ (Φ ⁻¹' (finStrict (N := N) K ∩ B))
      = π (srSet N m) * (arrayMeasure N)
          {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ B}

/-- `hstruct` from the residual family, phrased with `FinHorizonFamily`. -/
theorem hstruct_of_finHorizonFamily [IsProbabilityMeasure (arrayMeasure N)] (hm : 1 ≤ m) (p : ℝ)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] (hπ : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (A : Set Ω) (hA : A = Φ ⁻¹' strictPos (N := N))
    (h : FinHorizonFamily (N := N) (m := m) p π μ Φ) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B)
        = π (srSet N m) * (arrayMeasure N)
            {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} :=
  hstruct_mass_form_of_finHorizon (N := N) hm p π hπ Φ hΦ A hA h

/-- **The `K → ∞` side of `(★)` is consistent with the array's own law**: the array masses of the
horizon events decrease exactly to the paper's `P(V)`.  So the limit step of §2 lands on the right
number on the array side; the content of `(★)` is therefore entirely the chain-to-array
correspondence at finite horizons, and not the limit. -/
theorem iInf_arrayMass_finStrict (p : ℝ) (m : ℕ) :
    (⨅ K, (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) K})
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  have hmeas : ∀ K, MeasurableSet {U : Array N | posPath p m U ∈ finStrict (N := N) K} :=
    fun K => measurable_posPath p m N (measurableSet_finStrict K)
  have hanti : Antitone fun K => {U : Array N | posPath p m U ∈ finStrict (N := N) K} :=
    fun K L hKL => Set.preimage_mono (finStrict_antitone hKL)
  have hInter : (⋂ K, {U : Array N | posPath p m U ∈ finStrict (N := N) K})
      = {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
    rw [show (⋂ K, {U : Array N | posPath p m U ∈ finStrict (N := N) K})
        = ⋂ K, posPath p m ⁻¹' finStrict (N := N) K from rfl,
      Set.preimage_iInter.symm, iInter_finStrict]
    rfl
  rw [← hInter]
  exact (hanti.measure_iInter (fun K => (hmeas K).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩).symm

/-- At horizon `0` the event is exactly `X 0 ≡ 0` — the `Y_0 ∈ F` half of `strictPos` — and its
mass under the array law is `1`, because the canonical path starts at the record level.  So the
`K = 0` end of the residual family is a true statement, and the family is not vacuous at its
base. -/
theorem arrayMass_finStrict_zero (p : ℝ) (m : ℕ) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) 0} = 1 := by
  have hset : {U : Array N | posPath p m U ∈ finStrict (N := N) 0} = univ := by
    ext U
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact mem_finStrict.mpr
      ⟨fun i => posPath_zero p m U i, fun n hn h0 _ => absurd h0 (by omega)⟩
  rw [hset, measure_univ]

/-- **`finStrict K` is strictly larger than `strictPos` at every finite horizon.**  The path
`n ↦ n` up to time `K` and then `2K - n` is strictly positive up to `K` and hits `0` at time
`2K + 1`, so no truncation of `V` is literally `V`: the finite-horizon residual `(★ K)` is a
genuinely stronger statement than `hstruct`, not a rewriting of it. -/
theorem exists_finStrict_not_strictPos (hN : 0 < N) (K : ℕ) :
    ∃ X : ℕ → Fin N → ℤ, X ∈ finStrict (N := N) K ∧ X ∉ strictPos (N := N) := by
  refine ⟨fun n _ => if n ≤ K then (n : ℤ) else 2 * (K : ℤ) - (n : ℤ), ?_, ?_⟩
  · refine mem_finStrict.mpr ⟨fun _ => by simp, fun n hn hnK _ => ?_⟩
    rw [if_pos hnK]
    exact_mod_cast hn
  · intro hcon
    rw [mem_strictPos] at hcon
    have h := hcon.2 (2 * K + 1) (by omega) ⟨0, hN⟩
    rw [if_neg (by omega)] at h
    push_cast at h
    omega


/-- **The horizon-`K` analogue of `FreshState.fresh_mass_integral_srSet`.**  The `π`-average over
`F = srSet` of the per-state horizon-`K` fresh mass is `π(F)` times the canonical horizon-`K`
mass — i.e. the right-hand side of `hstruct`, truncated at horizon `K`, and computed with *no*
infinite-time condition.  This is the array-side (mixture) half of the finite-horizon residual
`(★ K)`; combining it with `FinHorizonFamily` recovers `hstruct` in the `∫⁻`-form. -/
theorem finHorizon_mass_integral_srSet (hm : 1 ≤ m) (p : ℝ) (π : Measure (RecState N m))
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
        FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
          trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C} ∂π
      = π (srSet N m) * (arrayMeasure N) {U : Array N |
          posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  have hcongr : ∀ y ∈ srSet N m,
      (arrayMeasure N) {U : Array N |
          FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
            trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C}
        = (arrayMeasure N) {U : Array N |
            posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} :=
    fun y hy => fresh_mass_finStrict_eq_of_srSet hm p hy K C
  rw [setLIntegral_congr_fun (SwarmRec.measurableSet_srSet N m) hcongr,
    setLIntegral_const, mul_comm]

end SwarmFinHorizon
