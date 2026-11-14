/-
  **The actual `Γ`-trial *finishing time* as a strict-drift container.**

  `GammaSigma.lean` (accepted, `areas/filtration/`) constructs the paper's trial event `Γ_y^A`
  as the first passage `σ_y^A = j` of the group record to `y`, followed by the `2m-1`-step
  prescribed word `wordRun`.  `LocMoveH.lean` (accepted, `areas/martingale/`) proves the strict
  `(Wstrict)` step `condExp_indicator_WA_strict_le`: at a time `n` at which `(sep)` holds, if
  some `i₀ ∈ I` sits at a site excited for its group (`w_n^{I}(X^{i₀}) = p`) but not for itself
  (`α_n^{i₀} = 1/2`), then the conditional mean of `W_{n+1}^{I,J} - W_n^{I,J}` is at most
  `-(2p-1)/|I|`.

  What was missing is the *transfer*: showing that at the time the trial finishes,
  `n = σ_y^A + (2m-1)`, the leader `i_y` is such a walker, and that `(sep)` at that time is what
  the windowed finishing event has to supply.  That is this file.

  Proved here, all on the actual trajectory, for `I = A`, `J = Aᶜ`:

  * `measurableSet_prefPred` and its consequences — every prefix-determined event (`ARMax`,
    `IsLeader`, `wordRun`, hence the trial pieces) is `posFilt n`-measurable at every level `n`
    at or above the level at which it is decided;
  * `GammaFinPiece`, `GammaFin` — the *Gamma-when-finished* event at the finishing time
    `n = j + (2m-1)`: the paper's trial pieces **plus** `(sep)` at `n`.  This is exactly the
    shape `condExp_indicator_WA_strict_le` consumes, and `(sep)` at `n` is *not* a consequence
    of the trial word (the word constrains only the walkers of `A`), so it is carried
    explicitly as part of the windowed event rather than assumed away;
  * the pathwise content of the finished trial: the leader sits at `y+1` at time `n`
    (`GammaFin_leader_pos`), every other walker is at or below `y` throughout the window
    (`GammaFin_other_X_le`), the leader's local time at `y+1` is at least `m`
    (`GammaFin_leader_L_ge`) while every other walker's local time there is zero
    (`GammaFin_other_L_zero`);
  * `GammaFin_rightProbability` (`α_n^{i_y} = 1/2`) and `GammaFin_wA` (`w_n^{A}(y+1) = p`) —
    the two hypotheses `hα`, `hw` of the strict step, *derived* at the finishing time;
  * `GammaFin_subset_SepSet`, `GammaFin_subset_GammaSet`, `GammaFin_subset_sigmaA` — the
    windowed event is separated at `n`, is a subevent of the paper's `Γ_y^A`, and sits on the
    record level `σ_y^A = j`;
  * `GammaFin_two_le_gapMin` — the separation conjunct is exactly `2 ≤ gapMin` at `n` in the
    vocabulary of the accepted `SepWindow`/`SepLight` geometry;
  * `condExp_indicator_WA_strict_le_exists` — the `∃`-form of the strict step, which is what a
    path-dependent leader requires; and
  * `condExp_indicator_GammaFin_strict_le` — **the strict conditional mean at the actual
    finishing time**:
    `E[1_{Γ-fin}(W_{n+1}^{A,Aᶜ} - W_n^{A,Aᶜ}) | F_n] ≤ᵐ -(2p-1)/|A| · 1_{Γ-fin}`,
    its integrated form `integral_GammaFin_strict_le`, and — via `GammaFinAt` — the same bound
    **simultaneously at every finishing time** on a single almost-sure set
    (`ae_forall_condExp_GammaFinAt_strict_le`), so that a window sum can be taken pathwise.

  Scope.  This is the `-(R_t^A - R_s^A)` *half* of `(locmove)` at the paper's constant.  Not
  proved here and not asserted: a lower bound on the number of strict times (that is the Gamma
  count, a separate package), the `H^A`-growth half, `(locgroup)`, `(diam)`, tightness,
  regeneration, `Ballistic` or `MainClaim`.  No probability of `GammaFin` is computed.
-/
import Swarm.LocMoveH
import Swarm.GammaSigma
import Swarm.SepWindow

set_option maxHeartbeats 2000000
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Swarming.GammaFin

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift Swarming.Enl LocMove

variable {N : ℕ}

/-! ## 1. Prefix-determined events are measurable for the position filtration -/

lemma measurableSet_prefOf_coord (p : ℝ) (m : ℕ) (n : ℕ) (t : Fin (n+1)) (i : Fin N)
    {A : Set ℤ} (hA : MeasurableSet A) :
    MeasurableSet[posFilt N p m n] {U : Array N | (prefOf p m n U) t i ∈ A} :=
  measurable_pos_posFilt p m i (k := (t : ℕ)) (n := n) (by omega) hA

lemma measurableSet_prefOf_singleton (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) :
    MeasurableSet[posFilt N p m n] {U : Array N | prefOf p m n U = γ} := by
  have h : {U : Array N | prefOf p m n U = γ} =
      ⋂ (t : Fin (n+1)), ⋂ (i : Fin N), {U : Array N | (prefOf p m n U) t i = γ t i} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  rw [h]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
    measurableSet_prefOf_coord p m n t i (measurableSet_singleton (γ t i))

/-- **Every prefix-determined event is `posFilt n`-measurable.**  The prefix space is countable,
so no measurability condition on the predicate is needed. -/
lemma measurableSet_prefPred (p : ℝ) (m : ℕ) (n : ℕ) (P : Pref N n → Prop) :
    MeasurableSet[posFilt N p m n] {U : Array N | P (prefOf p m n U)} := by
  have hset : {U : Array N | P (prefOf p m n U)} =
      ⋃ γ ∈ {γ : Pref N n | P γ}, {U : Array N | prefOf p m n U = γ} := by
    ext U
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨prefOf p m n U, Set.mem_iUnion.mpr ⟨h, rfl⟩⟩
    · intro h
      obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp h
      obtain ⟨hP, rfl⟩ := Set.mem_iUnion.mp hγ
      exact hP
  rw [hset]
  exact MeasurableSet.biUnion (Set.countable_univ.mono (Set.subset_univ _))
    (fun γ _ => measurableSet_prefOf_singleton p m n γ)

/-- `ARMax` read off the position prefix. -/
lemma measurableSet_ARMax_pos (p : ℝ) (m : ℕ) (n : ℕ) {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {k : ℕ} (hk : k ≤ n) :
    MeasurableSet[posFilt N p m n] {U : Array N | ARMax p m U hA y k} := by
  have hset : {U : Array N | ARMax p m U hA y k} =
      {U : Array N | (fun γ : Pref N n =>
        y ≤ runMaxAExt hA γ k ∧ ∀ s < k, runMaxAExt hA γ s < y) (prefOf p m n U)} := by
    ext U
    exact ARMax_iff_ext (prefAgree_prefOf U) hk
  rw [hset]
  exact measurableSet_prefPred p m n (fun γ : Pref N n =>
    y ≤ runMaxAExt hA γ k ∧ ∀ s < k, runMaxAExt hA γ s < y)

/-- The leader predicate is `posFilt n`-measurable at every level above `t`. -/
lemma measurableSet_leader_pos (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) {y : ℤ} {t : ℕ}
    (ht : t ≤ n) (iy : Fin N) :
    MeasurableSet[posFilt N p m n] {U : Array N | IsLeader p m U A y t iy} := by
  have hset : {U : Array N | IsLeader p m U A y t iy} =
      {U : Array N | (fun γ : Pref N n =>
        ext γ t iy = y ∧ ∀ k ∈ A, k < iy → ext γ t k ≠ y) (prefOf p m n U)} := by
    ext U
    exact leader_iff_ext (prefAgree_prefOf U) A ht iy
  rw [hset]
  exact measurableSet_prefPred p m n (fun γ : Pref N n =>
    ext γ t iy = y ∧ ∀ k ∈ A, k < iy → ext γ t k ≠ y)

/-- The trial word is `posFilt n`-measurable at every level at which it has finished. -/
lemma measurableSet_wordRun_pos (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (iy : Fin N)
    {j k : ℕ} (hk : j + k ≤ n) :
    MeasurableSet[posFilt N p m n] (wordRun p m j A iy k) := by
  have hset : wordRun p m j A iy k =
      {U : Array N | (fun γ : Pref N n => ∀ u ≤ k, ∀ i ∈ A, ext γ (j + u) i = ext γ j i +
        (if i = iy then (((u % 2 : ℕ)) : ℤ) else -((u : ℕ) : ℤ))) (prefOf p m n U)} := by
    ext U
    exact wordRun_iff_ext (prefAgree_prefOf U) hk
  rw [hset]
  exact measurableSet_prefPred p m n (fun γ : Pref N n => ∀ u ≤ k, ∀ i ∈ A,
    ext γ (j + u) i = ext γ j i +
      (if i = iy then (((u % 2 : ℕ)) : ℤ) else -((u : ℕ) : ℤ)))

/-- The trial piece at its own level, read at any later level. -/
lemma measurableSet_GammaPiece_pos (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N))
    (hA : A.Nonempty) (y : ℤ) {j : ℕ} (hj : j ≤ n) (iy : Fin N) :
    MeasurableSet[posFilt N p m n] (GammaPiece p m A hA y j iy) :=
  (measurableSet_ARMax_pos p m n hj).inter (measurableSet_leader_pos p m n A hj iy)

/-! ## 2. The Gamma-when-finished event -/

/-- One labelled piece of the *finished* trial at `y`: the paper's trial started at the record
level `j` and finished at time `n = j + (2m-1)`, together with the separation event `(sep)` at
the finishing time for `I = A`, `J = Aᶜ`. -/
noncomputable def GammaFinPiece (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (j n : ℕ) (iy : Fin N) : Set (Array N) :=
  GammaPiece p m A hA y j iy ∩ wordRun p m j A iy (2 * m - 1) ∩ SepSet p m n A Aᶜ

/-- **The Gamma-when-finished event** at finishing time `n` with first-passage level `j`:
the union of the labelled pieces over the group. -/
noncomputable def GammaFin (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (j n : ℕ) : Set (Array N) :=
  ⋃ iy ∈ A, GammaFinPiece p m A hA y j n iy

lemma measurableSet_GammaFin (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) {j n : ℕ} (hj : j + (2 * m - 1) ≤ n) :
    MeasurableSet[posFilt N p m n] (GammaFin p m A hA y j n) := by
  refine Finset.measurableSet_biUnion A (fun iy _ => ?_)
  exact ((measurableSet_GammaPiece_pos p m n A hA y (by omega) iy).inter
    (measurableSet_wordRun_pos p m n A iy (by omega))).inter
    (measurableSet_sepSet p m n A Aᶜ)

lemma GammaFin_subset_SepSet (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (j n : ℕ) :
    GammaFin p m A hA y j n ⊆ {U : Array N | SepSet p m n A Aᶜ U} := by
  intro U hU
  simp only [GammaFin, Set.mem_iUnion] at hU
  obtain ⟨iy, -, ⟨⟨-, -⟩, hsep⟩⟩ := hU
  exact hsep

/-- **The separation conjunct of the finishing event in the accepted geometry vocabulary**:
`(sep)` at the finishing time is exactly `2 ≤ gapMin` for `I = A`, `J = Aᶜ`, the worst-case gap of
`SepWindow`/`SepLight`.  This is the quantity whose failure `SepWindow.descent_or_ascent`
decomposes into one-sided walker events. -/
lemma GammaFin_two_le_gapMin (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (y : ℤ) (j n : ℕ) {U : Array N}
    (hU : U ∈ GammaFin p m A hA y j n) :
    2 ≤ LocSepWindow.gapMin p m n A Aᶜ hA hAc U := by
  have h : Sep p m U n A Aᶜ := GammaFin_subset_SepSet p m A hA y j n hU
  exact (LocSepWindow.sepClause_iff_two_le_gapMin hA hAc).mp h.2

/-- The finished trial is a subevent of the paper's `Γ_y^A` (same level, same leader label). -/
lemma GammaFin_subset_GammaSet (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (j n : ℕ) :
    GammaFin p m A hA y j n ⊆ GammaSet p m hA y := by
  intro U hU
  simp only [GammaFin, Set.mem_iUnion] at hU
  obtain ⟨iy, hiy, hpiece⟩ := hU
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨iy, Set.mem_iUnion.mpr ⟨hiy, hpiece.1⟩⟩⟩

/-- The finished trial sits on the first-passage level `j` of the group record. -/
lemma GammaFin_subset_sigmaA (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (j n : ℕ) :
    GammaFin p m A hA y j n ⊆ {U : Array N | sigmaA p m U hA y = (j : WithTop ℕ)} := by
  intro U hU
  simp only [GammaFin, Set.mem_iUnion] at hU
  obtain ⟨iy, -, hpiece⟩ := hU
  exact sigmaA_eq_coe_iff.mpr hpiece.1.1.1

/-! ## 3. What the finished trial provides, pathwise

All statements below are at the finishing time `j + (2m-1)`. -/

variable {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {y : ℤ} {j : ℕ} {iy : Fin N}

lemma two_mul_sub_one_mod_two {m : ℕ} (hm : 1 ≤ m) : (2 * m - 1) % 2 = 1 := by
  have h : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  rw [h, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]

lemma two_mul_add_one_mod_two (r : ℕ) : (2 * r + 1) % 2 = 1 := by
  rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]

/-- At the finishing time the leader sits at `y + 1`. -/
lemma GammaFin_leader_pos (hm : 1 ≤ m) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A) :
    X p m U (j + (2 * m - 1)) iy = y + 1 := by
  obtain ⟨⟨hpiece, hword⟩, -⟩ := hU
  have hXj : (trajectory p m U j).pos iy = y := hpiece.2.1
  have h := hword (2 * m - 1) le_rfl iy hiy
  rw [hXj, two_mul_sub_one_mod_two hm] at h
  simpa [X_apply] using h

/-- Every walker other than the leader is at or below `y` at every time up to the finishing
time.  Walkers of `A` are at most `y` because the group record is still `y` at `j` and the word
moves them down; walkers outside `A` are pinned below `y` by `(sep)` at the finishing time. -/
lemma GammaFin_other_X_le (hm : 1 ≤ m) (hy : 0 ≤ y) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A)
    {i : Fin N} (hii : i ≠ iy) :
    ∀ t ≤ j + (2 * m - 1), X p m U t i ≤ y := by
  obtain ⟨⟨hpiece, hword⟩, hsep⟩ := hU
  have hsep' : Sep p m U (j + (2 * m - 1)) A Aᶜ := hsep
  have hreq : runMaxA p m U hA j = y := ARMax.eq hy hpiece.1
  have hposn : X p m U (j + (2 * m - 1)) iy = y + 1 := GammaFin_leader_pos hm ⟨⟨hpiece, hword⟩, hsep⟩ hiy
  intro t ht
  by_cases hiA : i ∈ A
  · by_cases htj : t ≤ j
    · show (trajectory p m U t).pos i ≤ y
      calc (trajectory p m U t).pos i ≤ runMaxA p m U hA t := pos_le_runMaxA hiA
        _ ≤ runMaxA p m U hA j := runMaxA_mono htj
        _ = y := hreq
    · obtain ⟨u, rfl⟩ : ∃ u, t = j + u := ⟨t - j, by omega⟩
      have hu1 : 1 ≤ u := by omega
      have huk : u ≤ 2 * m - 1 := by omega
      have h := hword u huk i hiA
      rw [if_neg hii] at h
      have hXj : (trajectory p m U j).pos i ≤ y := by
        calc (trajectory p m U j).pos i ≤ runMaxA p m U hA j := pos_le_runMaxA hiA
          _ = y := hreq
      show (trajectory p m U (j + u)).pos i ≤ y
      rw [h]
      have : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu1
      omega
  · have hsepij := hsep'.2 iy hiy i (by simpa [Finset.mem_compl] using hiA)
    have h1 : Swarming.Trajectory.runMax p m U i (j + (2 * m - 1)) ≤ y - 1 := by omega
    have h2 : X p m U t i ≤ Swarming.Trajectory.runMax p m U i t := le_runMax p m U i t
    have h3 : Swarming.Trajectory.runMax p m U i t ≤
        Swarming.Trajectory.runMax p m U i (j + (2 * m - 1)) :=
      Swarming.Trajectory.runMax_mono p m U i ht
    omega

/-- The leader's local time at `y+1` is at least `m`: the word visits `y+1` at the `m` odd
offsets `1, 3, …, 2m-1`. -/
lemma GammaFin_leader_L_ge (hm : 1 ≤ m) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A) :
    m ≤ L p m U (j + (2 * m - 1)) iy (y + 1) := by
  obtain ⟨⟨hpiece, hword⟩, -⟩ := hU
  have hXj : (trajectory p m U j).pos iy = y := hpiece.2.1
  rw [L_apply, ell_eq_localTime, localTime_def]
  have hinj : Function.Injective (fun r : ℕ => j + (2 * r + 1)) := by
    intro a b hab
    simp only at hab
    omega
  have hsub : (Finset.range m).image (fun r => j + (2 * r + 1)) ⊆
      {t ∈ Finset.range (j + (2 * m - 1) + 1) | (trajectory p m U t).pos iy = y + 1} := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    have hrm : r < m := Finset.mem_range.mp hr
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have h := hword (2 * r + 1) (by omega) iy hiy
    rw [hXj, two_mul_add_one_mod_two r] at h
    simpa using h
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_range] at hcard

/-- Every other walker's local time at `y+1` is zero at the finishing time. -/
lemma GammaFin_other_L_zero (hm : 1 ≤ m) (hy : 0 ≤ y) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A)
    {i : Fin N} (hii : i ≠ iy) :
    L p m U (j + (2 * m - 1)) i (y + 1) = 0 := by
  rw [L_apply, ell_eq_localTime, localTime_def]
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr ?_)
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨htr, htx⟩ := ht
  have hle := GammaFin_other_X_le hm hy hU hiy hii t (by omega)
  have htx' : X p m U t i = y + 1 := htx
  omega

/-- **`α_n^{i_y} = 1/2` at the finishing time**: the leader's own site is not excited for
itself, because no other walker visits `y+1` by then. -/
lemma GammaFin_rightProbability (hm : 1 ≤ m) (hy : 0 ≤ y) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A) :
    rightProbability p m (trajectory p m U (j + (2 * m - 1))).ell iy
      (X p m U (j + (2 * m - 1)) iy) = 1 / 2 := by
  classical
  have hpos : X p m U (j + (2 * m - 1)) iy = y + 1 := GammaFin_leader_pos hm hU hiy
  have hzero : otherVisits (trajectory p m U (j + (2 * m - 1))).ell iy (y + 1) = 0 := by
    simp only [otherVisits]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hii : i = iy
    · simp [hii]
    · rw [if_neg hii]
      exact GammaFin_other_L_zero hm hy hU hiy hii
  have hexp : ¬ Excited m (trajectory p m U (j + (2 * m - 1))).ell iy
      (X p m U (j + (2 * m - 1)) iy) := by
    simp only [Excited, hpos]
    rw [hzero]
    omega
  unfold rightProbability
  simp only [hexp, if_false]

/-- **`w_n^{A}(y+1) = p` at the finishing time**: the group's total local time at `y+1` has
reached `m`, since the leader alone has `m` visits there. -/
lemma GammaFin_wA (hm : 1 ≤ m) (hy : 0 ≤ y) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A) :
    wA p m U (j + (2 * m - 1)) A (X p m U (j + (2 * m - 1)) iy).toNat = p := by
  have hpos : X p m U (j + (2 * m - 1)) iy = y + 1 := GammaFin_leader_pos hm hU hiy
  have hnonneg : (0 : ℤ) ≤ y + 1 := by omega
  have hcast : ((X p m U (j + (2 * m - 1)) iy).toNat : ℤ) = y + 1 := by
    rw [hpos, Int.toNat_of_nonneg hnonneg]
  have hle : m ≤ ∑ i ∈ A, L p m U (j + (2 * m - 1)) i
      ((X p m U (j + (2 * m - 1)) iy).toNat : ℤ) := by
    rw [hcast]
    exact le_trans (GammaFin_leader_L_ge hm hU hiy)
      (Finset.single_le_sum (f := fun i => L p m U (j + (2 * m - 1)) i (y + 1))
        (fun i _ => Nat.zero_le _) hiy)
  simp only [wA, if_pos hle]
  ring

/-! ## 4. The `∃`-form of the strict step, and the strict mean at the finishing time -/

/-- **The strict step with a path-dependent leader.**  Same conclusion as
`LocMove.condExp_indicator_WA_strict_le`, but the witness `i₀` may be chosen from `I`
separately at each `U ∈ A₀`.  This is what the paper's `Γ_y^A` needs, since the leader is
determined by the path. -/
theorem condExp_indicator_WA_strict_le_exists
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {A₀ : Set (Array N)} (hA₀ : MeasurableSet[posFilt N p m n] A₀)
    (hsub : A₀ ⊆ {U | SepSet p m n I J U})
    (hex : ∀ U ∈ A₀, ∃ i₀ ∈ I,
      rightProbability p m (trajectory p m U n).ell i₀ (X p m U n i₀) = 1 / 2 ∧
        wA p m U n Jᶜ (X p m U n i₀).toNat = p) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => A₀.indicator
        (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
    ≤ᵐ[arrayMeasure N] fun U =>
      (-(2 * p - 1) / ((I.card : ℕ) : ℝ)) * A₀.indicator (fun _ => (1 : ℝ)) U := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  refine (condExp_indicator_WA_drift_le_cavg hp0 hp1 m n I J hI hJ hA₀ hsub).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  by_cases hU : U ∈ A₀
  · obtain ⟨i₀, hi₀, hα, hw⟩ := hex U hU
    have hsep : Sep p m U n I J := hsub hU
    have hnonpos : ∀ i ∈ I, corr p m U n Jᶜ i ≤ 0 :=
      fun i hi => corr_nonpos_of_sep hp hp1' hid hsep hi
    have hc : Cavg p m n I J U ≤ -(2 * p - 1) / ((I.card : ℕ) : ℝ) :=
      cavg_le_neg_card hp hp1' m n U I J hI hi₀ hα hw hnonpos
    simpa only [Set.indicator_of_mem hU, mul_one] using hc
  · simp only [Set.indicator_of_notMem hU, mul_zero, le_refl]

/-- **The strict conditional mean at the actual finishing time of the trial `Γ_y^A`.**

For `n = j + (2m-1)` with `y ≥ 0`, `m ≥ 1`, `A` and `Aᶜ` nonempty:

`E[ 1_{Γ-fin}(W_{n+1}^{A,Aᶜ} - W_n^{A,Aᶜ}) | F_n ] ≤ᵐ -(2p-1)/|A| · 1_{Γ-fin}`,

where `Γ-fin = GammaFin p m A hA y j n` is the windowed finishing event: the trial at level `y`
starting at `σ_y^A = j`, finishing at `n`, **together with** `(sep)` at `n`.  The separation
conjunct is consumed here as part of the event, not derived from the trial. -/
theorem condExp_indicator_GammaFin_strict_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {y : ℤ} (hy : 0 ≤ y) {j n : ℕ} (hj : n = j + (2 * m - 1)) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => (GammaFin p m A hA y j n).indicator
        (fun U => WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc) U)
    ≤ᵐ[arrayMeasure N] fun U =>
      (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
        (GammaFin p m A hA y j n).indicator (fun _ => (1 : ℝ)) U := by
  subst hj
  refine condExp_indicator_WA_strict_le_exists hp0 hp1 m (j + (2 * m - 1)) A Aᶜ hA hAc
    disjoint_compl_right (measurableSet_GammaFin p m A hA y (le_refl _))
    (GammaFin_subset_SepSet p m A hA y j (j + (2 * m - 1))) ?_
  intro U hU
  simp only [GammaFin, Set.mem_iUnion] at hU
  obtain ⟨iy, hiy, hpiece⟩ := hU
  exact ⟨iy, hiy, GammaFin_rightProbability hm hy hpiece hiy,
    (by simpa using GammaFin_wA hm hy hpiece hiy)⟩

/-! ## 5. The record advance, and disjointness of the strict levels -/

/-- The leader stays at or below `y+1` throughout the window. -/
lemma GammaFin_leader_X_le (hm : 1 ≤ m) (hy : 0 ≤ y) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A) :
    ∀ t ≤ j + (2 * m - 1), X p m U t iy ≤ y + 1 := by
  obtain ⟨⟨hpiece, hword⟩, -⟩ := hU
  have hXj : (trajectory p m U j).pos iy = y := hpiece.2.1
  have hreq : runMaxA p m U hA j = y := ARMax.eq hy hpiece.1
  intro t ht
  by_cases htj : t ≤ j
  · calc X p m U t iy ≤ runMaxA p m U hA t := pos_le_runMaxA hiy
      _ ≤ runMaxA p m U hA j := runMaxA_mono htj
      _ = y := hreq
      _ ≤ y + 1 := by omega
  · obtain ⟨u, rfl⟩ : ∃ u, t = j + u := ⟨t - j, by omega⟩
    have huk : u ≤ 2 * m - 1 := by omega
    have h := hword u huk iy hiy
    rw [if_pos rfl] at h
    show (trajectory p m U (j + u)).pos iy ≤ y + 1
    rw [h, hXj]
    have h2 : ((u % 2 : ℕ) : ℤ) ≤ 1 := by
      have := Nat.mod_lt u (by norm_num : 0 < 2)
      omega
    omega

/-- **The trial advances the group record by exactly one**: at the finishing time the group
record is `y+1`.  The leader sits at `y+1`, everybody else is at most `y`. -/
lemma GammaFin_runMaxA (hm : 1 ≤ m) (hy : 0 ≤ y) {U : Array N}
    (hU : U ∈ GammaFinPiece p m A hA y j (j + (2 * m - 1)) iy) (hiy : iy ∈ A) :
    runMaxA p m U hA (j + (2 * m - 1)) = y + 1 := by
  refine le_antisymm ?_ ?_
  · refine runMaxA_le_iff.mpr (fun i hi => ?_)
    by_cases hii : i = iy
    · subst hii
      exact runMax_le_of_forall U i (fun t ht => GammaFin_leader_X_le hm hy hU hiy t ht)
    · exact runMax_le_of_forall U i (fun t ht =>
        le_trans (GammaFin_other_X_le hm hy hU hiy hii t ht) (by omega))
  · calc y + 1 = X p m U (j + (2 * m - 1)) iy := (GammaFin_leader_pos hm hU hiy).symm
      _ ≤ runMaxA p m U hA (j + (2 * m - 1)) := pos_le_runMaxA hiy

/-- The strict levels are disjoint: two finished trials of the same group at different
first-passage levels `j ≠ j'` cannot both hold at the same array.  Consequently the strict
times of a residue class are pairwise disjoint events, as the drift sum needs. -/
lemma GammaFin_disjoint_of_ne {j j' n n' : ℕ} (h : j ≠ j') :
    Disjoint (GammaFin p m A hA y j n) (GammaFin p m A hA y j' n') := by
  rw [Set.disjoint_left]
  intro U hU hU'
  have h1 := GammaFin_subset_sigmaA p m A hA y j n hU
  have h2 := GammaFin_subset_sigmaA p m A hA y j' n' hU'
  have hcoe : (j : WithTop ℕ) = (j' : WithTop ℕ) := by rw [← h1, h2]
  exact h (WithTop.coe_inj.mp hcoe)

/-! ## 6. The integrated strict bound -/

/-- **The strict bound in integrated form**, which is the shape the drift summation over a
window consumes: the mean increment of `W^{A,Aᶜ}` over the finished trial is at most
`-(2p-1)/|A|` times the measure of the event. -/
theorem integral_GammaFin_strict_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {y : ℤ} (hy : 0 ≤ y) {j n : ℕ} (hj : n = j + (2 * m - 1)) :
    ∫ U, (GammaFin p m A hA y j n).indicator
        (fun U => WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc) U
        ∂(arrayMeasure N)
      ≤ (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
          (arrayMeasure N).real (GammaFin p m A hA y j n) := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  haveI hprob := arrayMeasure_isProbabilityMeasure N
  subst hj
  set G : Set (Array N) := GammaFin p m A hA y j (j + (2 * m - 1)) with hG
  set F : Array N → ℝ := fun U => G.indicator
    (fun U => WA p m U (j + (2 * m - 1) + 1) A Aᶜ hA hAc -
      WA p m U (j + (2 * m - 1)) A Aᶜ hA hAc) U with hF
  set c : ℝ := -(2 * p - 1) / ((A.card : ℕ) : ℝ) with hc
  have hGmeas : MeasurableSet G :=
    ((posFilt N p m).le _) _ (measurableSet_GammaFin p m A hA y (le_refl _))
  have h1 : Integrable (fun U => WA p m U (j + (2 * m - 1) + 1) A Aᶜ hA hAc)
      (arrayMeasure N) :=
    integrable_WA hp hp1' m (j + (2 * m - 1) + 1) A Aᶜ hA hAc
  have h2 : Integrable (fun U => WA p m U (j + (2 * m - 1)) A Aᶜ hA hAc)
      (arrayMeasure N) :=
    integrable_WA hp hp1' m (j + (2 * m - 1)) A Aᶜ hA hAc
  have hint : Integrable F (arrayMeasure N) := by
    rw [hF]
    exact (h1.sub h2).indicator hGmeas
  have hintCE : Integrable (fun U => condExp (posFilt N p m (j + (2 * m - 1)))
      (arrayMeasure N) F U) (arrayMeasure N) := integrable_condExp
  have hrhsint : Integrable (fun U => c * G.indicator (fun _ => (1 : ℝ)) U)
      (arrayMeasure N) :=
    ((integrable_const (1 : ℝ)).indicator hGmeas).const_mul _
  have hce : condExp (posFilt N p m (j + (2 * m - 1))) (arrayMeasure N) F
      ≤ᵐ[arrayMeasure N] fun U => c * G.indicator (fun _ => (1 : ℝ)) U := by
    rw [hF, hG, hc]
    exact condExp_indicator_GammaFin_strict_le (p := p) hp0 hp1 hm A hA hAc hy
      (j := j) (n := j + (2 * m - 1)) rfl
  calc ∫ U, (GammaFin p m A hA y j (j + (2 * m - 1))).indicator
        (fun U => WA p m U (j + (2 * m - 1) + 1) A Aᶜ hA hAc -
          WA p m U (j + (2 * m - 1)) A Aᶜ hA hAc) U ∂(arrayMeasure N)
      = ∫ U, condExp (posFilt N p m (j + (2 * m - 1))) (arrayMeasure N) F U
          ∂(arrayMeasure N) := by
        rw [hF]
        exact (integral_condExp ((posFilt N p m).le _)).symm
    _ ≤ ∫ U, c * G.indicator (fun _ => (1 : ℝ)) U ∂(arrayMeasure N) :=
        integral_mono_ae hintCE hrhsint hce
    _ = (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
          (arrayMeasure N).real (GammaFin p m A hA y j (j + (2 * m - 1))) := by
        have hind : (∫ a, G.indicator (fun _ => (1 : ℝ)) a ∂(arrayMeasure N))
            = (arrayMeasure N).real G := integral_indicator_one (μ := arrayMeasure N) hGmeas
        rw [integral_const_mul, hind, hc, hG]

/-! ## 7. The finishing time as such, and the simultaneous a.e. bound -/

/-- The finished trial at the finishing time `n` alone: the first-passage level is then
`n - (2m-1)`.  This is the event a window summation refers to by its time index. -/
noncomputable def GammaFinAt (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (n : ℕ) : Set (Array N) :=
  if 2 * m - 1 ≤ n then GammaFin p m A hA y (n - (2 * m - 1)) n else ∅

lemma measurableSet_GammaFinAt (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (n : ℕ) : MeasurableSet[posFilt N p m n] (GammaFinAt p m A hA y n) := by
  unfold GammaFinAt
  split_ifs with h
  · exact measurableSet_GammaFin p m A hA y (by omega)
  · exact (posFilt N p m n).measurableSet_empty

/-- The strict bound at the finishing time `n` itself. -/
theorem condExp_indicator_GammaFinAt_strict_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {y : ℤ} (hy : 0 ≤ y) (n : ℕ) :
    condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => (GammaFinAt p m A hA y n).indicator
        (fun U => WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc) U)
    ≤ᵐ[arrayMeasure N] fun U =>
      (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
        (GammaFinAt p m A hA y n).indicator (fun _ => (1 : ℝ)) U := by
  unfold GammaFinAt
  split_ifs with h
  · exact condExp_indicator_GammaFin_strict_le hp0 hp1 hm A hA hAc hy (j := n - (2 * m - 1))
      (by omega)
  · simp
    exact Filter.Eventually.of_forall (fun _ => le_refl 0)

/-- **The strict bound simultaneously at every time**, almost surely: a single null set works
for all finishing times, so a window sum can be taken pathwise. -/
theorem ae_forall_condExp_GammaFinAt_strict_le
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {y : ℤ} (hy : 0 ≤ y) :
    ∀ᵐ (U : Array N) ∂(arrayMeasure N), ∀ n : ℕ,
      condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => (GammaFinAt p m A hA y n).indicator
          (fun U => WA p m U (n + 1) A Aᶜ hA hAc - WA p m U n A Aᶜ hA hAc) U) U
      ≤ (-(2 * p - 1) / ((A.card : ℕ) : ℝ)) *
          (GammaFinAt p m A hA y n).indicator (fun _ => (1 : ℝ)) U :=
  ae_all_iff.mpr (fun n => condExp_indicator_GammaFinAt_strict_le hp0 hp1 hm A hA hAc hy n)

end Swarming.GammaFin
