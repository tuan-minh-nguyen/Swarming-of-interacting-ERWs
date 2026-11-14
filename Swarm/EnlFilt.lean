/-
The enlarged filtration of the strong construction, built on the **actual** interacting
trajectory `Swarming.Trajectory.trajectory` of `Swarm/Swarm/Trajectory.lean`.

The paper (`main_1d_revised.tex` §2.1) works with

  `𝓕_n = σ(X_t^i , U^i(X_t^i, L_t^i(X_t^i)) : t < n)`,

the position path up to time `n` together with every array coordinate already revealed.
This module constructs it as a genuine nested `MeasureTheory.Filtration` of the ambient
product σ-algebra of the i.i.d. uniform array `Swarming.Uniform.Array N`.

Why the pieces are indexed by *path prefixes* and not by the truncated state: the state
`(pos, ell)` at time `n` is not a function of the state at time `n+1` together with the
revealed coordinates (the predecessor position is lost), so the filtration described
through `{state n = s}` is not monotone.  The path prefix loses nothing, so
prefix-indexed pieces give the monotone object directly.

Contents:

* `Pref`, `ext`, `prefRead` — a position prefix up to time `n`, its extension to a total
  path, and the finite set of array coordinates read strictly before time `n`.
* `prefRead_restrict_subset` — the read set grows with the horizon (nesting).
* `traj_depends_on_prefRead` — the whole state path up to time `n` is a function of the
  coordinates in `prefRead n γ` only.
* `prefAgree_preimage` — `{prefix = γ}` is the preimage, under those coordinates, of a
  measurable subset of the finite product.
* `enlMeas`, `enlFilt` — the enlarged filtration; `enlMeas_le` (inside the ambient
  σ-algebra), `enlMeas_mono` (nested), `enl_pos_measurable` (the actual positions are
  adapted), `enl_revealed_measurable` (every revealed coordinate value is adapted).
* `posFilt_le_enlFilt` — the minimal position filtration of `ExitStop.lean` is contained
  in the enlarged filtration, so the paper's exit times are stopping times for it.

There is no proof hole and no custom axiom in this file.
-/
import Swarm.Imports
import Swarm.UniformArray
import Swarm.Trajectory
import Swarm.FreshIndependence
import Swarm.ExitStop

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### Position prefixes and the coordinates they reveal -/

/-- A candidate position path of the swarm up to time `n`. -/
abbrev Pref (N : ℕ) (n : ℕ) := Fin (n + 1) → Fin N → ℤ

/-- The position path up to time `n` of the actual trajectory. -/
noncomputable def prefOf (p : ℝ) (m : ℕ) (n : ℕ) (U : Array N) : Pref N n :=
  fun t => (trajectory p m U t.1).pos

/-- Extension of a prefix to a total path (constant after time `n`). -/
noncomputable def ext {n : ℕ} (γ : Pref N n) : ℕ → Fin N → ℤ :=
  fun s i => if h : s < n + 1 then γ ⟨s, h⟩ i else γ ⟨n, Nat.lt_succ_self n⟩ i

lemma ext_of_lt {n s : ℕ} (γ : Pref N n) (h : s < n + 1) (i : Fin N) :
    ext γ s i = γ ⟨s, h⟩ i := by
  simp only [ext, dif_pos h]

lemma ext_prefOf {p : ℝ} {m : ℕ} {n : ℕ} (U : Array N) {s : ℕ} (hs : s ≤ n) (i : Fin N) :
    ext (prefOf p m n U) s i = (trajectory p m U s).pos i := by
  have h : s < n + 1 := by omega
  rw [ext_of_lt _ h]
  rfl

/-- Restriction of a prefix to a smaller horizon. -/
noncomputable def restrict {n : ℕ} (γ : Pref N (n + 1)) : Pref N n :=
  fun t i => γ ⟨t.1, Nat.lt_trans t.2 (Nat.lt_succ_self (n + 1))⟩ i

lemma restrict_prefOf {p : ℝ} {m : ℕ} {n : ℕ} (U : Array N) :
    restrict (prefOf p m (n + 1) U) = prefOf p m n U := rfl

lemma ext_restrict {n : ℕ} (γ : Pref N (n + 1)) {s : ℕ} (hs : s ≤ n) (i : Fin N) :
    ext (restrict γ) s i = ext γ s i := by
  have h1 : s < n + 1 := by omega
  have h2 : s < n + 2 := by omega
  rw [ext_of_lt (restrict γ) h1, ext_of_lt γ h2]
  rfl

/-- The finite set of array coordinates read strictly before time `n` by the path `γ`:
walker `i` reads `(i, X_t^i, L_t^i(X_t^i))` at each departure time `t`. -/
noncomputable def prefRead (n : ℕ) (γ : Pref N n) : Finset (Fin N × ℤ × ℕ) :=
  (Finset.range n).biUnion fun t =>
    Finset.univ.image fun i => (i, ext γ t i, localTime (fun s => ext γ s i) t (ext γ t i))

lemma mem_prefRead {n : ℕ} {γ : Pref N n} {i : Fin N} {x : ℤ} {k : ℕ} :
    ((i, x, k) : Fin N × ℤ × ℕ) ∈ prefRead n γ ↔
      ∃ t < n, ext γ t i = x ∧ localTime (fun s => ext γ s i) t x = k := by
  classical
  simp only [prefRead, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, c, rfl, rfl, rfl⟩
    exact ⟨t, ht, rfl, rfl⟩
  · rintro ⟨t, ht, hx, hk⟩
    exact ⟨t, ht, i, rfl, hx, by rw [hx]; exact hk⟩

/-- Local times depend only on the path up to the current time. -/
lemma localTime_congr {X Y : ℕ → ℤ} {n : ℕ} {x : ℤ} (h : ∀ s, s ≤ n → X s = Y s) :
    localTime X n x = localTime Y n x := by
  simp only [localTime]
  congr 1
  exact Finset.filter_congr fun s hs => by
    simp only [Finset.mem_range] at hs
    rw [h s (by omega)]

lemma localTime_congr_restrict {n t : ℕ} (γ : Pref N (n + 1)) (i : Fin N) {x : ℤ}
    (ht : t ≤ n) :
    localTime (fun s => ext (restrict γ) s i) t x = localTime (fun s => ext γ s i) t x :=
  localTime_congr fun s hs => ext_restrict γ (s := s) (by omega) i

/-- The revealed set grows with the horizon. -/
lemma prefRead_restrict_subset {n : ℕ} (γ : Pref N (n + 1)) :
    prefRead n (restrict γ) ⊆ prefRead (n + 1) γ := by
  rintro ⟨i, x, k⟩ hc
  rw [mem_prefRead] at hc ⊢
  obtain ⟨t, ht, hx, hk⟩ := hc
  have hx' : ext γ t i = x := by
    rw [← ext_restrict γ (s := t) (by omega) i]; exact hx
  have hk' : localTime (fun s => ext γ s i) t x = k := by
    rw [← localTime_congr (X := fun s => ext (restrict γ) s i)
      (Y := fun s => ext γ s i) (fun s hs => ext_restrict γ (s := s) (by omega) i)]
    exact hk
  exact ⟨t, by omega, hx', hk'⟩

/-- The set of arrays whose position path follows the prefix `γ`. -/
noncomputable def prefAgree (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) : Set (Array N) :=
  {U | ∀ t : Fin (n + 1), (trajectory p m U t.1).pos = γ t}

lemma mem_prefAgree {p : ℝ} {m : ℕ} {n : ℕ} {γ : Pref N n} {U : Array N} :
    U ∈ prefAgree p m γ ↔ ∀ t : Fin (n + 1), (trajectory p m U t.1).pos = γ t := Iff.rfl

lemma prefAgree_prefOf {p : ℝ} {m : ℕ} {n : ℕ} (U : Array N) :
    U ∈ prefAgree p m (prefOf p m n U) := fun _ => rfl

lemma ext_prefOf_of_mem {p : ℝ} {m : ℕ} {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) {s : ℕ} (hs : s ≤ n) (i : Fin N) :
    ext γ s i = (trajectory p m U s).pos i := by
  have h : s < n + 1 := by omega
  rw [ext_of_lt _ h]
  exact (congrFun (hU ⟨s, h⟩) i).symm

lemma departCoord_eq {p : ℝ} {m : ℕ} {n : ℕ} (U : Array N) (i : Fin N) :
    departureCoord p m U n i =
      (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i ((trajectory p m U n).pos i)) :=
  rfl

/-! ### The state depends only on the revealed coordinates -/

lemma drivenStep_cases (u α : ℝ) : drivenStep u α = 1 ∨ drivenStep u α = -1 := by
  unfold drivenStep
  split <;> simp

lemma nextPos_ne (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (i : Fin N) :
    nextPos p m U s i ≠ s.pos i := by
  rw [nextPos]
  rcases drivenStep_cases _ _ with h | h <;> rw [h] <;> omega

lemma nextWalkState_congr (p : ℝ) (m : ℕ) {s : WalkState N} {U U' : Array N}
    (h : ∀ i, U (i, s.pos i, s.ell i (s.pos i)) = U' (i, s.pos i, s.ell i (s.pos i))) :
    nextWalkState p m U s = nextWalkState p m U' s := by
  have hpos : nextPos p m U s = nextPos p m U' s := by
    funext i
    simp only [nextPos]
    rw [h i]
  cases s with
  | mk pos ell =>
    rw [nextWalkState, nextWalkState, hpos]

/-- Two arrays agreeing on the coordinates read before time `n` along `γ` produce the
same trajectory states up to time `n`, provided the first follows `γ`. -/
theorem traj_depends_on_prefRead (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (U U' : Array N)
    (hU : U ∈ prefAgree p m γ) (h : ∀ c ∈ prefRead n γ, U c = U' c) :
    ∀ k ≤ n, trajectory p m U k = trajectory p m U' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hprev : trajectory p m U k = trajectory p m U' k := ih (by omega)
      have hcoord : ∀ i : Fin N,
          U (i, (trajectory p m U k).pos i, (trajectory p m U k).ell i ((trajectory p m U k).pos i))
            = U' (i, (trajectory p m U k).pos i,
                (trajectory p m U k).ell i ((trajectory p m U k).pos i)) := by
        intro i
        refine h _ ?_
        rw [mem_prefRead]
        refine ⟨k, by omega, ?_, ?_⟩
        · exact ext_prefOf_of_mem (s := k) hU (by omega) i
        · rw [Swarming.Trajectory.ell_eq_localTime]
          exact localTime_congr fun s hs => ext_prefOf_of_mem (s := s) hU (by omega) i
      rw [trajectory_succ, trajectory_succ, ← hprev]
      exact nextWalkState_congr (s := trajectory p m U k) p m hcoord

/-! ### Finite products over the revealed coordinates -/

/-- Extension of a function on a finite set of coordinates to the whole array. -/
noncomputable def extendArr {S : Finset (Fin N × ℤ × ℕ)} (g : S → ℝ) : Array N :=
  fun c => if h : c ∈ S then g ⟨c, h⟩ else 0

lemma extendArr_of_mem {S : Finset (Fin N × ℤ × ℕ)} {g : S → ℝ} {c : Fin N × ℤ × ℕ}
    (h : c ∈ S) : extendArr g c = g ⟨c, h⟩ := by
  simp only [extendArr, dif_pos h]

lemma extendArr_of_not_mem {S : Finset (Fin N × ℤ × ℕ)} {g : S → ℝ} {c : Fin N × ℤ × ℕ}
    (h : c ∉ S) : extendArr g c = 0 := by
  simp only [extendArr, dif_neg h]

lemma measurable_extendArr {S : Finset (Fin N × ℤ × ℕ)} (c : Fin N × ℤ × ℕ) :
    Measurable fun g : S → ℝ => extendArr g c := by
  by_cases h : c ∈ S
  · have hfun : (fun g : S → ℝ => extendArr g c) = fun g => g ⟨c, h⟩ := by
      funext g
      exact extendArr_of_mem h
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun g : S → ℝ => extendArr g c) = fun _ => (0 : ℝ) := by
      funext g
      exact extendArr_of_not_mem h
    rw [hfun]
    exact measurable_const

/-- The σ-algebra generated by the array coordinates in a finite set `S`. -/
@[reducible] def cylAt (S : Finset (Fin N × ℤ × ℕ)) : MeasurableSpace (Array N) :=
  MeasurableSpace.comap (fun (g : Array N) (c : S) => g c)
    (inferInstance : MeasurableSpace (S → ℝ))

lemma cylAt_mono {S T : Finset (Fin N × ℤ × ℕ)} (h : S ⊆ T) : cylAt (N := N) S ≤ cylAt T := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  refine MeasurableSpace.measurableSet_comap.2
    ⟨(fun (g : T → ℝ) (c : S) => g ⟨c, h c.2⟩) ⁻¹' B, ?_, ?_⟩
  · exact hB.preimage (measurable_pi_lambda _ fun c => measurable_pi_apply _)
  · ext U
    rfl

lemma measurableSet_cylAt_of_mem {S : Finset (Fin N × ℤ × ℕ)} {c : Fin N × ℤ × ℕ} (hc : c ∈ S)
    {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet[cylAt (N := N) S] {U : Array N | U c ∈ A} := by
  refine MeasurableSpace.measurableSet_comap.2
    ⟨{g : S → ℝ | g ⟨c, hc⟩ ∈ A}, hA.preimage (measurable_pi_apply _), ?_⟩
  ext U
  simp

lemma measurableSet_prefAgree_ambient (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) :
    MeasurableSet (prefAgree p m γ) := by
  have hset : prefAgree p m γ = ⋂ t : Fin (n + 1), ⋂ i : Fin N,
      {U : Array N | (trajectory p m U t.1).pos i = γ t i} := by
    ext U
    simp only [prefAgree, Set.mem_setOf_eq, Set.mem_iInter, funext_iff]
  rw [hset]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
    (Swarming.Fair.measurable_trajectory p m t.1).1 i (measurableSet_singleton _)

/-- The agreement event is the preimage of a measurable set of the finite product over the
revealed coordinates. -/
lemma prefAgree_preimage (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) :
    prefAgree p m γ =
      (fun U (c : prefRead n γ) => U c) ⁻¹'
        {g : prefRead n γ → ℝ | ∀ t : Fin (n + 1),
          (trajectory p m (extendArr g) t.1).pos = γ t} := by
  ext U
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prefAgree]
  have hagree : ∀ c : Fin N × ℤ × ℕ, c ∈ prefRead n γ →
      U c = extendArr (S := prefRead n γ) (fun c' => U c') c := by
    intro c hc
    rw [extendArr_of_mem hc]
  constructor
  · intro hU
    have hdep := traj_depends_on_prefRead p m γ U (extendArr (S := prefRead n γ) fun c' => U c') hU
      (fun c hc => hagree c hc)
    intro t
    rw [← hU t]
    exact congrArg (fun s : WalkState N => s.pos) (hdep t.1 (by omega)).symm
  · intro hg
    have hdep := traj_depends_on_prefRead p m γ (extendArr (S := prefRead n γ) fun c' => U c') U
      (fun t => hg t) (fun c hc => (hagree c hc).symm)
    intro t
    rw [← hg t]
    exact congrArg (fun s : WalkState N => s.pos) (hdep t.1 (by omega)).symm

/-- The determining set in the finite product is measurable. -/
lemma measurableSet_prefRead_preimage (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) :
    MeasurableSet {g : prefRead n γ → ℝ | ∀ t : Fin (n + 1),
      (trajectory p m (extendArr g) t.1).pos = γ t} := by
  have hsingle : ∀ (t : Fin (n + 1)) (i : Fin N), Measurable fun g : prefRead n γ → ℝ =>
      (trajectory p m (extendArr g) t.1).pos i := by
    intro t i
    have h1 : Measurable fun g : prefRead n γ → ℝ => extendArr g :=
      measurable_pi_iff.2 fun c => measurable_extendArr c
    exact ((Swarming.Fair.measurable_trajectory p m t.1).1 i).comp h1
  have h : ∀ t : Fin (n + 1), Measurable fun g : prefRead n γ → ℝ =>
      (trajectory p m (extendArr g) t.1).pos := fun t => measurable_pi_iff.2 (hsingle t)
  have hset : {g : prefRead n γ → ℝ | ∀ t : Fin (n + 1),
      (trajectory p m (extendArr g) t.1).pos = γ t} =
      ⋂ t : Fin (n + 1), {g : prefRead n γ → ℝ |
        (trajectory p m (extendArr g) t.1).pos = γ t} := by
    ext g
    simp
  rw [hset]
  exact MeasurableSet.iInter fun t => (h t) (measurableSet_singleton _)

/-! ### The enlarged filtration -/

/-- A piece of the enlarged filtration at time `n`: the path follows `γ` and the array
lies in a set determined by the coordinates revealed before time `n`. -/
noncomputable def enlPiece (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (A : Set (Array N)) :
    Set (Array N) :=
  prefAgree p m γ ∩ A

/-- **The enlarged filtration at time `n`**, as a σ-algebra.  A set belongs to it exactly
when, on each piece `{path = γ}`, it agrees with a set determined by the coordinates
revealed before time `n` along `γ`. -/
noncomputable def enlMeas (p : ℝ) (m : ℕ) (n : ℕ) : MeasurableSpace (Array N) where
  MeasurableSet' G := ∀ γ : Pref N n, ∃ B : Set (Array N),
    MeasurableSet[cylAt (N := N) (prefRead n γ)] B ∧ prefAgree p m γ ∩ G = prefAgree p m γ ∩ B
  measurableSet_empty := by
    intro γ
    exact ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, by simp⟩
  measurableSet_compl := by
    intro G hG γ
    obtain ⟨B, hB, hEq⟩ := hG γ
    refine ⟨Bᶜ, (cylAt (prefRead n γ)).measurableSet_compl _ hB, ?_⟩
    have hstep : prefAgree p m γ ∩ Gᶜ = prefAgree p m γ ∩ (prefAgree p m γ ∩ G)ᶜ := by
      ext U
      simp only [Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 hc.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hg => h2 ⟨h1, hg⟩⟩
    have hgoal : prefAgree p m γ ∩ (prefAgree p m γ ∩ B)ᶜ = prefAgree p m γ ∩ Bᶜ := by
      ext U
      simp only [Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hb => h2 ⟨h1, hb⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 hc.2⟩
    rw [hstep, hEq, hgoal]
  measurableSet_iUnion := by
    intro G hG γ
    choose B hB hEq using fun i => hG i γ
    exact ⟨⋃ i, B i, (cylAt (prefRead n γ)).measurableSet_iUnion B hB, by
      rw [Set.inter_iUnion, Set.inter_iUnion]
      congr 1
      funext i
      exact hEq i⟩

/-- A single piece of the enlarged filtration is measurable. -/
lemma enl_piece_measurable (p : ℝ) (m : ℕ) {n : ℕ} (γ₀ : Pref N n) {A : Set (Array N)}
    (hA : MeasurableSet[cylAt (N := N) (prefRead n γ₀)] A) :
    MeasurableSet[enlMeas p m n] (enlPiece p m γ₀ A) := by
  intro γ
  by_cases h : γ = γ₀
  · subst h
    refine ⟨A, hA, ?_⟩
    refine Set.Subset.antisymm Set.inter_subset_right ?_
    rintro U ⟨h1, h2⟩
    exact ⟨h1, h1, h2⟩
  · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
    show prefAgree p m γ ∩ enlPiece p m γ₀ A = prefAgree p m γ ∩ (∅ : Set (Array N))
    rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
    rintro U ⟨h1, h2, -⟩
    exact h (by funext t; rw [← h1 t, ← h2 t])

/-- The path is adapted to the enlarged filtration: every prefix event is measurable. -/
lemma enl_prefAgree_measurable (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) :
    MeasurableSet[enlMeas p m n] (prefAgree p m γ) := by
  have h := enl_piece_measurable (N := N) p m (n := n) γ (A := Set.univ) MeasurableSet.univ
  rwa [enlPiece, Set.inter_univ] at h

/-- Every walker position at every time `k ≤ n` is adapted to the enlarged filtration. -/
lemma enl_pos_measurable (p : ℝ) (m : ℕ) (n : ℕ) {k : ℕ} (hk : k ≤ n) (i : Fin N) :
    Measurable[enlMeas p m n] fun U : Array N => (trajectory p m U k).pos i := by
  intro S hS γ
  by_cases h : γ ⟨k, by omega⟩ i ∈ S
  · have hEq : prefAgree p m γ ∩ (fun U : Array N => (trajectory p m U k).pos i) ⁻¹' S
        = prefAgree p m γ := by
      refine Set.Subset.antisymm Set.inter_subset_left ?_
      rintro U h1
      exact ⟨h1, by rw [Set.mem_preimage, congrFun (h1 ⟨k, by omega⟩) i]; exact h⟩
    exact ⟨Set.univ, MeasurableSet.univ, by rw [Set.inter_univ]; exact hEq⟩
  · have hEq : prefAgree p m γ ∩ (fun U : Array N => (trajectory p m U k).pos i) ⁻¹' S
        = prefAgree p m γ ∩ (∅ : Set (Array N)) := by
      rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
      rintro U ⟨h1, h2⟩
      rw [Set.mem_preimage, congrFun (h1 ⟨k, by omega⟩) i] at h2
      exact h h2
    exact ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, hEq⟩

/-- The local times of the trajectory are adapted to the enlarged filtration. -/
lemma enl_ell_measurable (p : ℝ) (m : ℕ) (n : ℕ) {k : ℕ} (hk : k ≤ n) (i : Fin N) (x : ℤ) :
    Measurable[enlMeas p m n] fun U : Array N => (trajectory p m U k).ell i x := by
  have hval : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ →
      (trajectory p m U k).ell i x = localTime (fun s => ext γ s i) k x := by
    intro γ U h1
    rw [Swarming.Trajectory.ell_eq_localTime]
    exact localTime_congr fun s hs => (ext_prefOf_of_mem h1 (by omega) i).symm
  intro S hS γ
  by_cases h : localTime (fun s => ext γ s i) k x ∈ S
  · have hEq : prefAgree p m γ ∩ (fun U : Array N => (trajectory p m U k).ell i x) ⁻¹' S
        = prefAgree p m γ := by
      refine Set.Subset.antisymm Set.inter_subset_left ?_
      rintro U h1
      exact ⟨h1, by rw [Set.mem_preimage, hval γ U h1]; exact h⟩
    exact ⟨Set.univ, MeasurableSet.univ, by rw [Set.inter_univ]; exact hEq⟩
  · have hEq : prefAgree p m γ ∩ (fun U : Array N => (trajectory p m U k).ell i x) ⁻¹' S
        = prefAgree p m γ ∩ (∅ : Set (Array N)) := by
      rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
      rintro U ⟨h1, h2⟩
      rw [Set.mem_preimage, hval γ U h1] at h2
      exact h h2
    exact ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, hEq⟩

/-- The value of a coordinate that has been revealed by time `n` is measurable for the
enlarged filtration (the row of the array is known once it has been read). -/
lemma enl_revealed_measurable (p : ℝ) (m : ℕ) (n : ℕ) {k : ℕ} (hk : k < n) (i : Fin N)
    {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet[enlMeas p m n]
      {U : Array N | U (departureCoord p m U k i) ∈ I} := by
  have hcoord : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ →
      departureCoord p m U k i
        = (i, ext γ k i, localTime (fun s => ext γ s i) k (ext γ k i)) := by
    intro γ U h1
    rw [departCoord_eq]
    have hpos : ext γ k i = (trajectory p m U k).pos i := ext_prefOf_of_mem h1 (by omega) i
    have hell : localTime (fun s => ext γ s i) k (ext γ k i)
        = (trajectory p m U k).ell i ((trajectory p m U k).pos i) := by
      rw [Swarming.Trajectory.ell_eq_localTime, hpos]
      exact localTime_congr (X := fun s => ext γ s i)
        (Y := fun s => (trajectory p m U s).pos i) (n := k)
        (fun s hs => ext_prefOf_of_mem h1 (by omega) i)
    rw [hpos, ← hell, hpos]
  intro γ
  have hEq : prefAgree p m γ ∩ {U : Array N | U (departureCoord p m U k i) ∈ I}
      = prefAgree p m γ ∩ {U : Array N |
          U (i, ext γ k i, localTime (fun s => ext γ s i) k (ext γ k i)) ∈ I} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro U ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [Set.mem_setOf_eq] at h2 ⊢
      rw [← hcoord γ U h1]
      exact h2
    · rintro U ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [Set.mem_setOf_eq] at h2 ⊢
      rw [hcoord γ U h1]
      exact h2
  exact ⟨_, measurableSet_cylAt_of_mem (S := prefRead n γ)
    (by rw [mem_prefRead]; exact ⟨k, hk, rfl, rfl⟩) hI, hEq⟩

/-- The enlarged filtration is inside the ambient σ-algebra. -/
lemma enlMeas_le (p : ℝ) (m : ℕ) (n : ℕ) :
    enlMeas p m n ≤ (inferInstance : MeasurableSpace (Array N)) := by
  intro G hG
  choose B hB hEq using hG
  have hpiece : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := by
    intro γ
    have hB' : MeasurableSet (B γ) := by
      obtain ⟨C, hC, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 (hB γ)
      rw [← hBeq]
      exact hC.preimage (measurable_pi_lambda _ fun c => measurable_pi_apply _)
    exact (measurableSet_prefAgree_ambient p m γ).inter hB'
  have hunion : G = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have h3 : U ∈ prefAgree p m (prefOf p m n U) ∩ G := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at h3
      exact h3.2
    · rintro ⟨γ, h1, h2⟩
      have h3 : U ∈ prefAgree p m γ ∩ G := by
        rw [hEq γ]
        exact ⟨h1, h2⟩
      exact h3.2
  rw [hunion]
  exact MeasurableSet.iUnion hpiece

/-- **The enlarged filtration is nested.** -/
lemma enlMeas_mono (p : ℝ) (m : ℕ) {n : ℕ} :
    enlMeas (N := N) p m n ≤ enlMeas (N := N) p m (n + 1) := by
  intro G hG γ'
  obtain ⟨B, hB, hEq⟩ := hG (restrict γ')
  have hsub : prefAgree p m γ' ⊆ prefAgree p m (restrict γ') := by
    intro U hU t
    exact hU ⟨t.1, Nat.lt_trans t.2 (Nat.lt_succ_self (n + 1))⟩
  have hB₁ : MeasurableSet[cylAt (N := N) (prefRead (n + 1) γ')] B :=
    cylAt_mono (prefRead_restrict_subset γ') B hB
  refine ⟨B, hB₁, ?_⟩
  have heq' : prefAgree p m γ' ∩ G = prefAgree p m γ' ∩ B := by
    ext U
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 : U ∈ prefAgree p m (restrict γ') ∩ G := ⟨hsub h1, h2⟩
      rw [hEq] at h3
      exact h3.2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 : U ∈ prefAgree p m (restrict γ') ∩ B := ⟨hsub h1, h2⟩
      rw [← hEq] at h3
      exact h3.2
  rw [heq']

/-- **The enlarged filtration of the actual interacting walk**, as a genuine nested
`MeasureTheory.Filtration` of the ambient product σ-algebra. -/
noncomputable def enlFilt (p : ℝ) (m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Array N)) where
  seq := enlMeas p m
  mono' := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact ih.trans (enlMeas_mono (N := N) p m)
  le' := fun n => enlMeas_le p m n

lemma enlFilt_apply (p : ℝ) (m : ℕ) (n : ℕ) : enlFilt (N := N) p m n = enlMeas p m n := rfl

/-- **The minimal position filtration of `ExitStop.lean` is contained in the enlarged
filtration**: the enlarged filtration is really finer than the one on which the paper's
exit times are stopping times. -/
theorem posFilt_le_enlFilt (p : ℝ) (m : ℕ) : posFilt N p m ≤ enlFilt (N := N) p m := by
  rw [posFilt_le_iff]
  intro n i
  exact enl_pos_measurable p m n le_rfl i

/-- Consequently the paper's exit time out of the window `(lo, hi)`, started at the
stopping time `σ`, is a stopping time for the enlarged filtration. -/
theorem isStoppingTime_trajExit_enlFilt (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ} (hσ : IsStoppingTime (enlFilt (N := N) p m) σ) :
    IsStoppingTime (enlFilt (N := N) p m) (trajExit N p m i lo hi σ) :=
  isStoppingTime_trajExit_of_posFilt_le (posFilt_le_enlFilt p m) hσ

end Swarming.Enl
