/-`Swarm/FreshTwoSeg.lean` proves the two-atom mass identity
`chainVec (asegK p hm y) (pairK p hm) 2 {v 0 = atom₀ ∧ v 1 = atom₁}` `= ∏_{j<2} ofReal (hitW p qⱼ y)`
for two positive first-record words `q₀, q₁` started from one and the same simultaneous record
state `y ∈ srSet`.  This file generalises it to an arbitrary finite number of consecutive
enriched record atoms, each one driven by the *endpoint record state* of the previous atom.

Content.

* Part 1 (`SwarmFreshPrefix.pin`, `chainVec_pin_mass_succ`): the abstract chain lemma.  For a Markov
  kernel `κ`, an s-finite start law `μ` and prescribed points `A 0, A 1, …` the law of
  `(x 0, …, x (n-1)) = chainVec μ κ n` charges the pinned cylinder
  `pin A n = {v | ∀ j, v j = A j}` with `μ {A 0} * ∏_{j<n-1} κ (A j) {A (j+1)}`.  The induction
  step is the exact one-coordinate extension `chainVec_snoc_apply`, an integral of the one-step
  kernel over the pinned prefix; the constancy of the last coordinate on the pinned prefix is what
  turns the integral into the product.
* Part 2 (`ep`, `atom`, `PosWords`): the model-side data.  `ep` is the *iterated* endpoint chain
  `ep 0 = y`, `ep (j+1) = out (q j) (ep j)` — every word is driven by the previous endpoint, never
  by a fresh copy of `y`.  `atom j` is the true `asegK` atom at level `j`.
* Part 3: `ep_mem_srSet` (every endpoint is again a simultaneous record state, by induction from
  `SwarmFreshCyl.out_mem_srSet_of_pos`), and the word weights read at `ep j` equal those read at
  `y` (`hitW_ep`).
* Part 4 (`chainVec_atom_path_mass`, `chainVec_atom_path_mass'`, `chainVec_last_seg_mass`): the
  finite-prefix fresh mass identity on the actual enriched chain, in the literal atom form, in the
  state-free-segment form (the segments are `segOf y` at every level), and in the "last coordinate
  constrained only by its segment" cylinder form which specialises to `twoSeg_joint_mass` at
  `n = 1`.
* Part 5 (`compat_level`): the true adjacent-segment compatibility with the level shift
  `(j : ℤ) + segⱼ(durⱼ) = ((j+1) : ℤ) + seg_{j+1}(0)`; `chainOf_clamp_seg` /
  `chainOf_clamp_X` / `chainOf_clamp_regen` assemble the finite prefix into a genuine
  `SwarmConcat.Chain` through `ChainAssemble.chainOf`, whose concatenated path `X` is the paper's
  translated path, and show that level `0` is a regeneration level of it (the no-return content of
  the positive words, with no claim about the future after the prefix).

Scope.  Everything is a finite-prefix statement about the actual enriched record chain started at
one genuine `y ∈ srSet`.  Nothing here asserts `hstruct`, an invariant `π`, positivity of `π
(srSet)`, an infinite product law, or any limit/almost-everywhere statement about the future.
The produced mass is a product of the *first-segment* word weights at the original `y`, not a
function of the endpoint record states' own local times.
-/
import Swarm.FreshTwoSeg
import Swarm.ChainAssemble

open MeasureTheory Set
open Classical
open scoped ENNReal
open SimJump ProbabilityTheory

namespace SwarmFreshPrefix

open SimJump.Record SwarmRec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-! ## Part 1. The pinned finite prefix of a Markov chain -/

section Abstract

variable {β : Type*} [MeasurableSpace β]

/-- The cylinder of vectors of length `n` whose coordinate `j` is the prescribed point `A j`. -/
def pin (A : ℕ → β) (n : ℕ) : Set (Fin n → β) := {v | ∀ j : Fin n, v j = A j}

/-- `Fin 1` has a unique element. -/
theorem fin1_unique (j : Fin 1) : j = 0 := by
  rw [Fin.ext_iff]
  exact Nat.lt_one_iff.mp j.2

theorem pin_zero (A : ℕ → β) : pin A 0 = univ := by
  ext v
  simp [pin]

theorem pin_one (A : ℕ → β) :
    pin A 1 = (fun v : Fin 1 → β => v 0) ⁻¹' ({A 0} : Set β) := by
  ext v
  constructor
  · intro h
    exact h 0
  · intro h j
    rw [fin1_unique j]
    exact h

/-- The length-`n+1` pin is the length-`n` pin of the initial coordinates together with the last
coordinate. -/
theorem pin_succ (A : ℕ → β) (n : ℕ) :
    pin A (n+1) = {v : Fin (n+1) → β | SwarmChain.initF v ∈ pin A n ∧ v (Fin.last n) = A n} := by
  ext v
  constructor
  · intro h
    exact ⟨fun j => h j.castSucc, h (Fin.last n)⟩
  · rintro ⟨h1, h2⟩ j
    refine Fin.lastCases ?_ ?_ j
    · simpa using h2
    · intro i
      simpa [SwarmChain.initF] using h1 i

theorem measurableSet_pin {A : ℕ → β} (hA : ∀ j, MeasurableSet ({A j} : Set β)) (n : ℕ) :
    MeasurableSet (pin A n) := by
  have h : pin A n = ⋂ j : Fin n, (fun v : Fin n → β => v j) ⁻¹' {A j} := by
    ext v
    simp [pin]
  rw [h]
  exact MeasurableSet.iInter fun j => (measurable_pi_apply j) (hA j)

theorem mem_pin_last {A : ℕ → β} {n : ℕ} {w : Fin (n+1) → β} (hw : w ∈ pin A (n+1)) :
    w (Fin.last n) = A n := hw (Fin.last n)

/-! S-finiteness of the chain laws, by induction on the number of coordinates (`chainVec` and
`chainStep` are defined by recursion, so instance search cannot see through them). -/

instance sfinite_chainStep (μ : Measure β) [SFinite μ] (κ : Kernel β β) [IsSFiniteKernel κ] :
    ∀ n, SFinite (SwarmChain.chainStep μ κ n)
  | 0 => by rw [SwarmChain.chainStep_zero]; infer_instance
  | n + 1 => by
      haveI := sfinite_chainStep μ κ n
      rw [SwarmChain.chainStep_succ]
      infer_instance

instance sfinite_chainVec (μ : Measure β) [SFinite μ] (κ : Kernel β β) [IsSFiniteKernel κ] :
    ∀ n, SFinite (SwarmChain.chainVec μ κ n)
  | 0 => by rw [SwarmChain.chainVec_zero]; infer_instance
  | n + 1 => by rw [SwarmChain.chainVec_succ]; exact sfinite_chainStep μ κ n

/-- **The exact one-coordinate extension of the chain law.**  The law of `(x 0, …, x (m+1))`
(`chainVec μ κ (m+2)`) charges the cylinder "the first `m+1` coordinates lie in `D` and the last
one in `B`" by the integral, over the length-`m+1` pinned prefix in `D`, of the one-step kernel at
the last coordinate.  Nothing is assumed about `D` beyond measurability. -/
theorem chainVec_snoc_apply (μ : Measure β) [SFinite μ] (κ : Kernel β β) [IsSFiniteKernel κ]
    (m : ℕ) {D : Set (Fin (m+1) → β)} (hD : MeasurableSet D) {B : Set β}
    (hB : MeasurableSet B) :
    (SwarmChain.chainVec μ κ (m+2))
        {v : Fin (m+2) → β | SwarmChain.initF v ∈ D ∧ v (Fin.last (m+1)) ∈ B}
      = ∫⁻ w in D, κ (w (Fin.last m)) B ∂(SwarmChain.chainVec μ κ (m+1)) := by
  classical
  have hpre : (fun p : (Fin (m+1) → β) × β => SwarmChain.snocF p.1 p.2) ⁻¹'
      {v : Fin (m+2) → β | SwarmChain.initF v ∈ D ∧ v (Fin.last (m+1)) ∈ B} = D ×ˢ B := by
    ext p
    simp [SwarmChain.initF_snocF, SwarmChain.snocF_last]
  have hS : MeasurableSet
      {v : Fin (m+2) → β | SwarmChain.initF v ∈ D ∧ v (Fin.last (m+1)) ∈ B} :=
    (SwarmChain.measurable_initF hD).inter ((measurable_pi_apply _) hB)
  haveI hlast : IsSFiniteKernel (SwarmChain.lastK κ m) := by
    unfold SwarmChain.lastK
    infer_instance
  rw [SwarmChain.chainVec_succ_succ μ κ m,
    Measure.map_apply SwarmChain.measurable_snocF hS, hpre,
    Measure.compProd_apply_prod hD hB]
  refine setLIntegral_congr_fun hD fun w _ => ?_
  rw [SwarmChain.lastK_apply]

/-- **The one-coordinate extension when the last coordinate of the pinned prefix is fixed.**  If
every `w ∈ D` has last coordinate `a`, the integral collapses and adjoining the prescribed next
point `b` multiplies the pinned mass by `κ a {b}`. -/
theorem chainVec_snoc_pin (μ : Measure β) [SFinite μ] (κ : Kernel β β) [IsSFiniteKernel κ]
    (m : ℕ) {D : Set (Fin (m+1) → β)} (hD : MeasurableSet D) {a b : β}
    (hb : MeasurableSet ({b} : Set β)) (hconst : ∀ w ∈ D, w (Fin.last m) = a) :
    (SwarmChain.chainVec μ κ (m+2))
        {v : Fin (m+2) → β | SwarmChain.initF v ∈ D ∧ v (Fin.last (m+1)) = b}
      = κ a {b} * (SwarmChain.chainVec μ κ (m+1)) D := by
  rw [show {v : Fin (m+2) → β | SwarmChain.initF v ∈ D ∧ v (Fin.last (m+1)) = b}
      = {v : Fin (m+2) → β | SwarmChain.initF v ∈ D ∧ v (Fin.last (m+1)) ∈ ({b} : Set β)}
      from by ext v; simp,
    chainVec_snoc_apply μ κ m hD hb,
    setLIntegral_congr_fun hD (fun w hw => by rw [hconst w hw]), setLIntegral_const]

/-- **The mass of a pinned finite prefix of a Markov chain.**  For prescribed points
`A 0, A 1, …` and a start law `μ`, the law of `(x 0, …, x m)` charges the pinned cylinder with the
start mass of `A 0` and the product of the one-step transition masses along the prescribed path.

Index convention (the `chainVec` of `Swarm/ChainWindow.lean`): `chainVec μ κ n` is the law of the
`n`-vector `(x 0, …, x (n-1))`, with `x 0 ~ μ` and transitions of `κ`; so a pinned path of length
`m+1` is a cylinder for `chainVec μ κ (m+1)`. -/
theorem chainVec_pin_mass_succ (μ : Measure β) [SFinite μ] (κ : Kernel β β) [IsSFiniteKernel κ]
    (A : ℕ → β) (hA : ∀ j, MeasurableSet ({A j} : Set β)) :
    ∀ m, (SwarmChain.chainVec μ κ (m+1)) (pin A (m+1))
      = μ {A 0} * ∏ j ∈ Finset.range m, κ (A j) {A (j+1)} := by
  intro m
  induction m with
  | zero =>
      have hpre : (fun b : β => fun _ : Fin 1 => b) ⁻¹'
          ((fun v : Fin 1 → β => v 0) ⁻¹' ({A 0} : Set β)) = ({A 0} : Set β) := by
        ext b
        simp only [mem_preimage, mem_singleton_iff]
      rw [pin_one, SwarmChain.chainVec_succ, SwarmChain.chainStep_zero,
        Measure.map_apply SwarmChain.measurable_fin1_const ((measurable_pi_apply (0 : Fin 1)) (hA 0)),
        hpre, Finset.prod_range_zero, mul_one]
  | succ m ih =>
      rw [pin_succ A (m+1), chainVec_snoc_pin μ κ m (measurableSet_pin hA (m+1))
        (a := A m) (b := A (m+1)) (hA (m+1)) (fun w hw => mem_pin_last hw), ih,
        Finset.prod_range_succ]
      ring

end Abstract

/-! ## Part 2. The iterated endpoint record states and the word-family hypothesis -/

variable {N m : ℕ}

/-- The record trajectory driven by the words `pq`: it starts at `y`, and the word `pq j` is applied
at the endpoint of the previous word.  This is the object that carries the dependence: nothing is
redrawn from `y`. -/
noncomputable def ep (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) : ℕ → RecState N m
  | 0 => y
  | (j + 1) => RecKernel.out hm (pq j).2 (ep hm y pq j)

@[simp] theorem ep_zero (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) : ep hm y pq 0 = y := rfl

theorem ep_succ (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (j : ℕ) :
    ep hm y pq (j + 1) = RecKernel.out hm (pq j).2 (ep hm y pq j) := rfl

/-- The hypothesis on a word family: every `pq j` is a positive first-record word from `y`, i.e.
`0 < k`, the first-record condition at the *reference* state `y`, and the strict-positivity
condition `PosSeqFin` (the paper's no-return clause for one segment).  This is a conjunction of the
hypotheses of `Swarm/FreshCyl.lean`, not a new mathematical assumption. -/
def PosWords (y : RecState N m) (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) : Prop :=
  (∀ j, 0 < (pq j).1) ∧
    (∀ j, Record.FirstRecord (Record.extendPath (pq j).2) (pq j).1 (Record.ofRecState y)) ∧
      (∀ j, SwarmFreshPos.PosSeqFin (N := N) (pq j).2)

theorem PosWords.hk {y : RecState N m} {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)}
    (h : PosWords y pq) (j : ℕ) : 0 < (pq j).1 := h.1 j

theorem PosWords.hfr {y : RecState N m} {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)}
    (h : PosWords y pq) (j : ℕ) :
    Record.FirstRecord (Record.extendPath (pq j).2) (pq j).1 (Record.ofRecState y) := h.2.1 j

theorem PosWords.hq {y : RecState N m} {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)}
    (h : PosWords y pq) (j : ℕ) : SwarmFreshPos.PosSeqFin (N := N) (pq j).2 := h.2.2 j

/-! ## Part 3. The endpoints stay in `srSet`, and the word weights do not see them -/

/-- **Every endpoint of the iterated trajectory is again a simultaneous record state.**  This is the
induction that lets the *next* positive word be read at the previous endpoint; it is the reason the
product formula below is a product of first-segment weights at `y`. -/
theorem ep_mem_srSet (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) :
    ∀ j, ep hm y pq j ∈ srSet N m := by
  intro j
  induction j with
  | zero => exact hy
  | succ j ih =>
      exact SwarmFreshCyl.out_mem_srSet_of_pos hm hN ih (pq j).2
        ((SwarmFreshCyl.firstRecord_ofRecState_iff ih hy _ _).mpr (h.hfr j)) (h.hq j)

/-- The first-record condition of word `j`, read at its own start point `ep j`. -/
theorem firstRecord_ep (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) :
    Record.FirstRecord (Record.extendPath (pq j).2) (pq j).1
      (Record.ofRecState (ep hm y pq j)) :=
  (SwarmFreshCyl.firstRecord_ofRecState_iff (ep_mem_srSet hm hN hy h j) hy _ _).mpr (h.hfr j)

/-- **The word weight at the endpoint is the word weight at `y`.** -/
theorem hitW_ep (p : ℝ) (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) :
    RecKernel.hitW p (pq j).2 (ep hm y pq j) = RecKernel.hitW p (pq j).2 y :=
  SwarmFreshCyl.hitW_eq_of_srSet hm (ep_mem_srSet hm hN hy h j) hy (pq j).2 (h.hq j)

/-- **The segment read at the endpoint is the segment read at `y`.** -/
theorem segOf_ep (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) :
    SwarmSegKernel.segOf (ep hm y pq j) (pq j).1 (pq j).2
      = SwarmSegKernel.segOf y (pq j).1 (pq j).2 :=
  SwarmFreshCyl.segOf_eq_of_srSet (ep_mem_srSet hm hN hy h j) hy (h.hk j) (pq j).2
    (firstRecord_ep hm hN hy h j)

/-! ## Part 4. The atoms and the finite-prefix mass identity -/

/-- The literal `asegK` atom of step `j` of the iterated trajectory: the segment of the word read at
its own start point, together with the next endpoint record state. -/
noncomputable def atom (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (j : ℕ) :
    SwarmConcat.Seg N × RecState N m :=
  (SwarmSegKernel.segOf (ep hm y pq j) (pq j).1 (pq j).2, ep hm y pq (j + 1))

/-- The same atom with the state-free segment `segOf y` — equal to `atom` by `segOf_ep`, but the
form in which the cylinder is stated in the paper (the segment does not see the endpoint record
state; the endpoint record state itself is still part of the atom). -/
noncomputable def atomY (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (j : ℕ) :
    SwarmConcat.Seg N × RecState N m :=
  (SwarmSegKernel.segOf y (pq j).1 (pq j).2, ep hm y pq (j + 1))

theorem atom_eq_atomY (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) :
    atom hm y pq j = atomY hm y pq j := by
  simp only [atom, atomY, segOf_ep hm hN hy h j]

theorem measurableSet_atom_singleton (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (j : ℕ) :
    MeasurableSet ({atom hm y pq j} : Set (SwarmConcat.Seg N × RecState N m)) := by
  have h := (SwarmFreshTwoSeg.measurableSet_seg_singleton
    (SwarmSegKernel.segOf (ep hm y pq j) (pq j).1 (pq j).2)).prod
    (measurableSet_singleton (ep hm y pq (j + 1)))
  rwa [Set.singleton_prod_singleton] at h

theorem measurableSet_atomY_singleton (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m}
    (hy : y ∈ srSet N m) {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq)
    (j : ℕ) :
    MeasurableSet ({atomY hm y pq j} : Set (SwarmConcat.Seg N × RecState N m)) := by
  rw [← atom_eq_atomY hm hN hy h j]
  exact measurableSet_atom_singleton hm y pq j

/-- **The first atom of the chain, read at `y`.** -/
theorem asegK_atom_zero (p : ℝ) (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) :
    (SwarmSegKernel.asegK p hm y) {atom hm y pq 0}
      = ENNReal.ofReal (RecKernel.hitW p (pq 0).2 y) := by
  have hset : ({atom hm y pq 0} : Set (SwarmConcat.Seg N × RecState N m))
      = {(SwarmSegKernel.segOf y (pq 0).1 (pq 0).2, RecKernel.out hm (pq 0).2 y)} := by
    simp [atom, ep]
  rw [hset]
  exact SwarmFreshTwoSeg.asegK_atom p hm hy (h.hk 0) (pq 0).2 (h.hfr 0)

/-- **The transition mass from one atom to the next.**  From the endpoint `ep (j+1)` of the atom `j`
the one-step law charges the atom `j+1` exactly the first-segment weight of the *next* word, read at
the original `y`. -/
theorem pairK_atom_mass (p : ℝ) (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m}
    (hy : y ∈ srSet N m) {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq)
    (j : ℕ) :
    (SwarmSegKernel.pairK p hm (atom hm y pq j)) {atom hm y pq (j + 1)}
      = ENNReal.ofReal (RecKernel.hitW p (pq (j + 1)).2 y) := by
  have hmem : ep hm y pq (j + 1) ∈ srSet N m := ep_mem_srSet hm hN hy h (j + 1)
  have hstate : (atom hm y pq j).2 = ep hm y pq (j + 1) := rfl
  have hset : ({atom hm y pq (j + 1)} : Set (SwarmConcat.Seg N × RecState N m))
      = {(SwarmSegKernel.segOf (ep hm y pq (j + 1)) (pq (j + 1)).1 (pq (j + 1)).2,
          RecKernel.out hm (pq (j + 1)).2 (ep hm y pq (j + 1)))} := by
    simp [atom, ep]
  rw [SwarmSegKernel.pairK_apply, hstate, hset,
    SwarmFreshTwoSeg.asegK_atom p hm hmem (h.hk (j + 1)) (pq (j + 1)).2
      (firstRecord_ep hm hN hy h (j + 1))]
  rw [hitW_ep p hm hN hy h (j + 1)]

/-- **The finite-prefix fresh-mass identity, literal atom form.**  Start the actual enriched record
chain at one genuine simultaneous record state `y ∈ srSet`.  The law of the first `n` consecutive
atoms — each one driven by the endpoint record state of the previous one — charges the pinned
cylinder exactly with the product of the first-segment word weights `hitW p (pq j) y` at the
*original* `y`. -/
theorem chainVec_atom_path_mass (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n : ℕ) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) n)
        (pin (atom hm y pq) n)
      = ∏ j ∈ Finset.range n, ENNReal.ofReal (RecKernel.hitW p (pq j).2 y) := by
  haveI hmark : IsMarkovKernel (SwarmSegKernel.pairK p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hprob : IsProbabilityMeasure (SwarmSegKernel.asegK p hm y) :=
    SwarmSegKernel.isProbabilityMeasure_asegK p hm hp hp1 y
  cases n with
  | zero =>
      rw [pin_zero, SwarmChain.chainVec_zero, Measure.dirac_apply_of_mem (by simp)]
      simp
  | succ n =>
      rw [chainVec_pin_mass_succ (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm)
        (atom hm y pq) (measurableSet_atom_singleton hm y pq) n,
        asegK_atom_zero p hm hy h]
      rw [show (∏ j ∈ Finset.range (n+1), ENNReal.ofReal (RecKernel.hitW p (pq j).2 y))
          = (∏ j ∈ Finset.range n, ENNReal.ofReal (RecKernel.hitW p (pq (j+1)).2 y))
            * ENNReal.ofReal (RecKernel.hitW p (pq 0).2 y) from
        Finset.prod_range_succ' (fun j => ENNReal.ofReal (RecKernel.hitW p (pq j).2 y)) n,
        mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      exact pairK_atom_mass p hm hN hy h j

/-- **The finite-prefix fresh-mass identity, state-free segment form.**  The pinned cylinder written
with the segments `segOf y` instead of the literal `segOf (ep j)`. -/
theorem chainVec_atomY_path_mass (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n : ℕ) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) n)
        (pin (atomY hm y pq) n)
      = ∏ j ∈ Finset.range n, ENNReal.ofReal (RecKernel.hitW p (pq j).2 y) := by
  rw [← chainVec_atom_path_mass p hm hp hp1 hN hy h n]
  congr 1
  ext v
  simp only [pin, atom_eq_atomY hm hN hy h]

/-- **The finite-prefix fresh-mass identity, cylinder form.**  In the last coordinate only the
segment is fixed, the endpoint record state being summed over; this is the form that specialises to
the accepted two-atom identity `SwarmFreshTwoSeg.twoSeg_joint_mass` at `m = 0`. -/
theorem chainVec_last_seg_mass (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (m' : ℕ) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) (m' + 2))
        {v : Fin (m' + 2) → SwarmConcat.Seg N × RecState N m |
          SwarmChain.initF v ∈ pin (atomY hm y pq) (m' + 1) ∧
            v (Fin.last (m' + 1)) ∈ {b : SwarmConcat.Seg N × RecState N m |
              b.1 = SwarmSegKernel.segOf y (pq (m' + 1)).1 (pq (m' + 1)).2}}
      = (∏ j ∈ Finset.range (m' + 1), ENNReal.ofReal (RecKernel.hitW p (pq j).2 y))
        * ENNReal.ofReal (RecKernel.hitW p (pq (m' + 1)).2 y) := by
  haveI hmark : IsMarkovKernel (SwarmSegKernel.pairK p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hprob : IsProbabilityMeasure (SwarmSegKernel.asegK p hm y) :=
    SwarmSegKernel.isProbabilityMeasure_asegK p hm hp hp1 y
  have hD : MeasurableSet (pin (atomY hm y pq) (m' + 1)) :=
    measurableSet_pin (fun j => measurableSet_atomY_singleton hm hN hy h j) (m' + 1)
  have hB : MeasurableSet
      {b : SwarmConcat.Seg N × RecState N m |
        b.1 = SwarmSegKernel.segOf y (pq (m' + 1)).1 (pq (m' + 1)).2} :=
    measurable_fst (SwarmFreshTwoSeg.measurableSet_seg_singleton _)
  have hEq : ∀ w ∈ pin (atomY hm y pq) (m' + 1),
      (SwarmSegKernel.pairK p hm (w (Fin.last m')))
          {b : SwarmConcat.Seg N × RecState N m |
            b.1 = SwarmSegKernel.segOf y (pq (m' + 1)).1 (pq (m' + 1)).2}
        = ENNReal.ofReal (RecKernel.hitW p (pq (m' + 1)).2 y) := by
    intro w hw
    have hwlast : w (Fin.last m') = atomY hm y pq m' := mem_pin_last hw
    have hmem : ep hm y pq (m' + 1) ∈ srSet N m := ep_mem_srSet hm hN hy h (m' + 1)
    have hB' : {b : SwarmConcat.Seg N × RecState N m |
          b.1 = SwarmSegKernel.segOf y (pq (m' + 1)).1 (pq (m' + 1)).2}
        = {b : SwarmConcat.Seg N × RecState N m |
          b.1 = SwarmSegKernel.segOf (ep hm y pq (m' + 1)) (pq (m' + 1)).1 (pq (m' + 1)).2} := by
      rw [segOf_ep hm hN hy h (m' + 1)]
    rw [hwlast, atomY, SwarmSegKernel.pairK_apply, hB',
      SwarmFreshTwoSeg.asegK_segCyl p hm hmem (h.hk (m' + 1)) (pq (m' + 1)).2
        (firstRecord_ep hm hN hy h (m' + 1)),
      hitW_ep p hm hN hy h (m' + 1)]
  rw [chainVec_snoc_apply (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) m' hD hB,
    setLIntegral_congr_fun hD hEq, setLIntegral_const,
    chainVec_atomY_path_mass p hm hp hp1 hN hy h (m' + 1), mul_comm]

/-! ## Part 5. Level-shifted compatibility and the concatenated record path -/

/-- The end of the atom `j` in its own segment coordinates sits at the next level. -/
theorem atom_p_dur_eq_one (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) (i : Fin N) :
    (atom hm y pq j).1.p (atom hm y pq j).1.dur i = 1 := by
  have hdur : (atom hm y pq j).1.dur = (pq j).1 :=
    SwarmFreshCyl.segOf_dur_of_firstRecord (h.hk j) (pq j).2 (firstRecord_ep hm hN hy h j)
  rw [hdur]
  exact SwarmFreshTwoSeg.seg_end_eq_one hm hN (ep_mem_srSet hm hN hy h j) (h.hk j) (pq j).2
    (firstRecord_ep hm hN hy h j) (h.hq j) i

/-- **The level-shifted adjacent compatibility of consecutive atoms.**  The segment at level `j`
ends exactly one level above the start of the segment at level `j+1`: the paper's
`Chain.compat`, at the level shift `j`.  This is the *actual* repeated compatibility of the
enriched atoms, not a hypothesis. -/
theorem compat_level (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) (i : Fin N) :
    (j : ℤ) + (atom hm y pq j).1.p (atom hm y pq j).1.dur i
      = ((j + 1 : ℕ) : ℤ) + (atom hm y pq (j + 1)).1.p 0 i := by
  have hstart : (atom hm y pq (j + 1)).1.p 0 i = 0 :=
    SwarmSegKernel.segOf_p_zero_srSet (ep_mem_srSet hm hN hy h (j + 1)) (pq (j + 1)).1
      (pq (j + 1)).2 i
  rw [atom_p_dur_eq_one hm hN hy h j i, hstart]
  push_cast
  ring

/-- **The positive-word condition inside an atom.**  At every positive local time of the segment,
below its duration, every walker is strictly above its own start level. -/
theorem atom_p_pos (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (j : ℕ) {t : ℕ}
    (ht1 : 1 ≤ t) (htd : t ≤ (pq j).1) (i : Fin N) :
    0 < (atom hm y pq j).1.p t i := by
  have hseg : (atom hm y pq j).1
      = SwarmSegKernel.segOfFirst (ep hm y pq j) (pq j).1 (pq j).2 (h.hk j)
          (firstRecord_ep hm hN hy h j) :=
    SwarmDHStruct.segOf_of_firstRecord (h.hk j) (firstRecord_ep hm hN hy h j)
  rw [hseg]
  show 0 < SwarmSegKernel.relP (ep hm y pq j) (Record.extendPath (pq j).2) t i
  rw [SwarmFreshCyl.relP_eq_posAt (ep_mem_srSet hm hN hy h j) (Record.extendPath (pq j).2) t i]
  exact (SwarmFreshCyl.posWord_iff (pq j).2).mp (h.hq j) t ht1 htd i

/-- The finite prefix of `n+1` atoms, with the last atom repeated afterwards, as an infinite
enriched trajectory. -/
noncomputable def trajClamp (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (n : ℕ) :
    ℕ → SwarmConcat.Seg N × RecState N m :=
  fun j => atom hm y pq (min j n)

theorem trajClamp_apply (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (n j : ℕ) :
    trajClamp hm y pq n j = atom hm y pq (min j n) := rfl

/-- The clamped trajectory is compatible: on the prefix this is `compat_level`, on the clamp it is
the pair "ends at level 1, starts at level 0" of the repeated last atom. -/
theorem trajCompat_clamp (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n : ℕ) :
    SwarmChainAssemble.TrajCompat (trajClamp hm y pq n) := by
  intro k i
  by_cases hk : k < n
  · have h1 : min k n = k := min_eq_left (le_of_lt hk)
    have h2 : min (k + 1) n = k + 1 := min_eq_left (by omega)
    show (atom hm y pq (min k n)).1.p (atom hm y pq (min k n)).1.dur i
      = 1 + (atom hm y pq (min (k + 1) n)).1.p 0 i
    rw [h1, h2]
    have hc := compat_level hm hN hy h k i
    push_cast at hc ⊢
    linarith
  · have h1 : min k n = n := min_eq_right (by omega)
    have h2 : min (k + 1) n = n := min_eq_right (by omega)
    show (atom hm y pq (min k n)).1.p (atom hm y pq (min k n)).1.dur i
      = 1 + (atom hm y pq (min (k + 1) n)).1.p 0 i
    have hstart : (atom hm y pq n).1.p 0 i = 0 :=
      SwarmSegKernel.segOf_p_zero_srSet (ep_mem_srSet hm hN hy h n) (pq n).1 (pq n).2 i
    rw [h1, h2, atom_p_dur_eq_one hm hN hy h n i, hstart]
    norm_num

/-- **The assembled chain of the finite prefix**: `ChainAssemble.chainOf` applied to the clamped
trajectory.  Its segments are the atoms of the prefix, so it is a genuine `SwarmConcat.Chain` whose
concatenated path is the paper's translated record path. -/
noncomputable def chainClamp (hm : 1 ≤ m) (y : RecState N m)
    (pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)) (n : ℕ) : SwarmConcat.Chain N :=
  SwarmChainAssemble.chainOf (trajClamp hm y pq n)

theorem chainClamp_seg (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n j : ℕ) (hj : j ≤ n) :
    (chainClamp hm y pq n).seg j = (atom hm y pq j).1 := by
  rw [chainClamp, SwarmChainAssemble.chainOf_seg_of_compat (trajCompat_clamp hm hN hy h n) j,
    trajClamp_apply, min_eq_left hj]

/-- **The concatenated record path at the record times.**  At the record time of level `j` every
walker sits exactly at level `j` — the paper's "translate the segment at index `k` by `k`", read at
the record times of the finite prefix. -/
theorem chainClamp_X_record (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n j : ℕ) (hj : j ≤ n)
    (i : Fin N) :
    (chainClamp hm y pq n).X ((chainClamp hm y pq n).cum j) i = (j : ℤ) := by
  rw [chainClamp, SwarmChainAssemble.chainOf_X_record (trajCompat_clamp hm hN hy h n) j i]
  show (j : ℤ) + (atom hm y pq (min j n)).1.p 0 i = (j : ℤ)
  have hstart : (atom hm y pq j).1.p 0 i = 0 :=
    SwarmSegKernel.segOf_p_zero_srSet (ep_mem_srSet hm hN hy h j) (pq j).1 (pq j).2 i
  rw [min_eq_left hj, hstart, add_zero]

/-- Inside the `j`-th segment the concatenated path is the atom's own relative positions shifted by
the level `j`. -/
theorem chainClamp_X_cum_add (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n j : ℕ) (hj : j ≤ n)
    {t : ℕ} (ht1 : 1 ≤ t) (htd : t ≤ (atom hm y pq j).1.dur) (i : Fin N) :
    (chainClamp hm y pq n).X ((chainClamp hm y pq n).cum j + t) i
      = (j : ℤ) + (atom hm y pq j).1.p t i := by
  have hseg : (chainClamp hm y pq n).seg j = (atom hm y pq j).1 := chainClamp_seg hm hN hy h n j hj
  have hd : t ≤ ((chainClamp hm y pq n).seg j).dur := by rw [hseg]; exact htd
  rw [SwarmConcat.Chain.X_cum_add (c := chainClamp hm y pq n) ht1 hd i, hseg]

/-- **Level `0` is a regeneration level of the assembled chain.**  Every positive word keeps all
walkers strictly above their level inside its segment, so the concatenated path never returns to
level `0` after time `0`.  This is the no-return content of the finite prefix — nothing is claimed
about the future beyond the prefix, which is the clamped repetition. -/
theorem chainClamp_regen (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n : ℕ) :
    (chainClamp hm y pq n).Regen 0 := by
  constructor
  · intro i
    rw [chainClamp_seg hm hN hy h n 0 (Nat.zero_le n)]
    exact SwarmSegKernel.segOf_p_zero_srSet (ep_mem_srSet hm hN hy h 0) (pq 0).1 (pq 0).2 i
  · intro j _ t ht1 htd i
    have hseg : (chainClamp hm y pq n).seg j = (atom hm y pq (min j n)).1 := by
      rw [chainClamp, SwarmChainAssemble.chainOf_seg_of_compat (trajCompat_clamp hm hN hy h n) j,
        trajClamp_apply]
    rw [hseg] at htd ⊢
    have hdur : (atom hm y pq (min j n)).1.dur = (pq (min j n)).1 :=
      SwarmFreshCyl.segOf_dur_of_firstRecord (h.hk (min j n)) (pq (min j n)).2
        (firstRecord_ep hm hN hy h (min j n))
    have htd' : t ≤ (pq (min j n)).1 := by rw [← hdur]; exact htd
    have hpos := atom_p_pos hm hN hy h (min j n) ht1 htd' i
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    omega

/-- The path form of `chainClamp_regen`: at and after the level-`0` record time the concatenated
path is at level `0` and then strictly above it. -/
theorem chainClamp_regenPath (hm : 1 ≤ m) (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n : ℕ) :
    (chainClamp hm y pq n).RegenPath 0 :=
  (SwarmConcat.Chain.regen_iff (c := chainClamp hm y pq n) 0).mp (chainClamp_regen hm hN hy h n)

/-! ## Part 6. Consistency with the accepted two-atom checkpoint, and positivity -/

/-- The two-word family `⟨k₀,q₀⟩, ⟨k₁,q₁⟩, ⟨k₁,q₁⟩, …`. -/
noncomputable def pqTwo (k0 : ℕ) (q0 : Fin k0 → JumpVec N) (k1 : ℕ) (q1 : Fin k1 → JumpVec N) :
    ℕ → (k : ℕ) × (Fin k → JumpVec N) :=
  fun j => Nat.rec (motive := fun _ => (k : ℕ) × (Fin k → JumpVec N)) ⟨k0, q0⟩
    (fun _ _ => ⟨k1, q1⟩) j

@[simp] theorem pqTwo_zero (k0 : ℕ) (q0 : Fin k0 → JumpVec N) (k1 : ℕ)
    (q1 : Fin k1 → JumpVec N) : pqTwo k0 q0 k1 q1 0 = ⟨k0, q0⟩ := rfl

@[simp] theorem pqTwo_succ (k0 : ℕ) (q0 : Fin k0 → JumpVec N) (k1 : ℕ)
    (q1 : Fin k1 → JumpVec N) (j : ℕ) : pqTwo k0 q0 k1 q1 (j + 1) = ⟨k1, q1⟩ := rfl

/-- **Consistency with the accepted checkpoint.**  At `n = 2` the finite-prefix theorem is exactly
`SwarmFreshTwoSeg.twoSeg_atom_mass` (same cylinder, same product): with `pq 0 = ⟨k₀, q₀⟩` and
`pq 1 = ⟨k₁, q₁⟩` the iterated endpoint after two atoms is `out q₁ (out q₀ y)` and the segments are
the state-free `segOf y`. -/
theorem twoSeg_atom_mass_consistency (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m) {k0 : ℕ} (hk0 : 0 < k0)
    (q0 : Fin k0 → JumpVec N)
    (hfr0 : Record.FirstRecord (Record.extendPath q0) k0 (Record.ofRecState y))
    (hq0 : SwarmFreshPos.PosSeqFin (N := N) q0) {k1 : ℕ} (hk1 : 0 < k1)
    (q1 : Fin k1 → JumpVec N)
    (hfr1 : Record.FirstRecord (Record.extendPath q1) k1 (Record.ofRecState y))
    (hq1 : SwarmFreshPos.PosSeqFin (N := N) q1) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) 2)
        {v : Fin 2 → SwarmConcat.Seg N × RecState N m |
          v 0 = (SwarmSegKernel.segOf y k0 q0, RecKernel.out hm q0 y) ∧
          v 1 = (SwarmSegKernel.segOf y k1 q1, RecKernel.out hm q1 (RecKernel.out hm q0 y))}
      = ENNReal.ofReal (RecKernel.hitW p q0 y) * ENNReal.ofReal (RecKernel.hitW p q1 y) := by
  exact SwarmFreshTwoSeg.twoSeg_atom_mass p hm hp hp1 hN hy hk0 q0 hfr0 hq0 hk1 q1 hfr1 hq1

/-- **The finite-prefix mass is positive when the word weights are.**  So the pinned cylinder is a
genuine positive-mass path — the product is not a degenerate constant. -/
theorem chainVec_atom_path_mass_pos (p : ℝ) (hm : 1 ≤ m) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hN : 0 < N) {y : RecState N m} (hy : y ∈ srSet N m)
    {pq : ℕ → (k : ℕ) × (Fin k → JumpVec N)} (h : PosWords y pq) (n : ℕ)
    (hpos : ∀ j, j < n → 0 < RecKernel.hitW p (pq j).2 y) :
    0 < (SwarmChain.chainVec (SwarmSegKernel.asegK p hm y) (SwarmSegKernel.pairK p hm) n)
      (pin (atom hm y pq) n) := by
  rw [chainVec_atom_path_mass p hm hp hp1 hN hy h n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have ih' : 0 < ∏ j ∈ Finset.range n,
        ENNReal.ofReal (RecKernel.hitW p (pq j).2 y) := ih (fun j hj => hpos j (Nat.lt_succ_of_lt hj))
    exact ENNReal.mul_pos ih'.ne' (ENNReal.ofReal_pos.mpr (hpos n (Nat.lt_succ_self n))).ne'

end SwarmFreshPrefix
