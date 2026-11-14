/-
  **Measurability of the full-history seed `h_j(M_n^j)` for the record-enlarged σ-algebra.**

  This is direction A of the swarm.  `RecSeed.lean` proves the conditional recursion
  `condExp_shiftG` for an *arbitrary* seed `h0` that is `enlRecMeas p m n j`-measurable,
  deterministically bounded and integrable.  The paper's seed is

      `H0 U = h_j(M_n^j) = hof p (siteMarks p m U j) (M_n^j).toNat`,

  where `M_n^j = runMax p m U j n = recVal j (prefOf p m n U)` is the *running record* of the
  actual interacting trajectory, and the site marks `siteMarks p m U j x` are the actual
  coordinates of the actual `arrayMeasure N`.  Nothing in the integrated development produces
  the measurability of that particular `h0`: the record value is random, and the marks at the
  sites `0, …, M_n^j` are individually *not* `enlFilt`-measurable (the walker may not have
  departed from them yet).  This file closes exactly that gap, for `enlRecMeas`.

  Mathematical content (all deterministic, no probability):

  * for a fixed prefix `γ : Pref N n` and a site `x : ℕ` with `x ≤ recVal j γ`, the marked
    event `{U | SiteMark p m U j x}` is decided by the coordinates in `recRead m j γ`:

      - at `x = recVal j γ` the mark reads the adjoined row (`recRow`), which is in `recRead`;
      - at `x < recVal j γ`, either the revelation gate `m ≤ L_n^j(x)` holds on the piece — the
        gate is prefix-determined, so `measurableSet_cylAt_mark` turns the mark into a cylinder
        over `prefRead n γ ⊆ recRead m j γ` — or the gate fails, and then `reveal_runMax`
        (which needs `x ≥ 0` and `x + 1 ≤ M_n^j`) says that *no* array on the piece is marked;
      - constant-false pieces are handled by the `markSet`/`if` construction below, and the
        empty pieces (`prefAgree p m γ = ∅`) by the outer `if`.

  * consequently `H0` is `enlRecMeas p m n j`-measurable (`measurable_seedH`), being the
    composition of `hof` with the marks `0, …, M` read through those cylinders
    (`hof_congr` uses only `i ≤ M`; the nonnegativity of the record is
    `zero_le_recVal_of_mem_prefAgree`, i.e. `zero_le_runMax`).

  Hypotheses: only `1/2 ≤ p` (needed for `reveal_runMax`).  In particular **no** `p ≠ 0`:
  `SwarmMarks.measurable_hof` asks for `p ≠ 0` because it bootstraps through `hstep_eq_rho`, but
  `hof p ω n` is measurable in `ω` for every `p` since `hstep p b ·` is affine
  (`hstep_ite`/`measurable_hof_any`).  (`p ≠ 0` *is* needed later, by the shifted recursion
  itself, and by the deterministic bound `abs_hof_le'`.)

  Caveats that are *not* papered over:

  * Two arrays with the same prefix do **not** automatically agree on their revealed values;
    every step here goes through an explicit cylinder set or the gate, never through such an
    inference (`markSet` is *defined* by the gate, and membership in it is *proved* equal to the
    mark on the piece).
  * Nothing here is `enlFilt`-measurable beyond the gate-passing sites: off the gate a site
    strictly below the record genuinely is not read, which is why the record-enlarged
    σ-algebra `enlRecMeas` of `RecEnv.lean` is the correct home.
  * No shifted identification `hof p (siteMarks…) (M + g) = shiftG h0 p m n j g` and no bound
    `|H0| ≤ 2 n + 3` is proved here; those are direction B.  See `NOTES.md`.
-/
import Swarm.RecExp
import Swarm.EnlReveal
import Swarm.RawLogRatio

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### Anchoring of a nonempty prefix at zero -/

/-- On a nonempty piece the prefix starts at the origin. -/
lemma ext_zero_of_mem_prefAgree {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (j : Fin N) : ext γ 0 j = 0 := by
  rw [ext_prefOf_of_mem hU (Nat.zero_le n) j]
  simp

/-- **The prefix record is nonnegative on a nonempty piece.**  This is `zero_le_runMax`
read on the prefix; it is what lets the record be used as a natural-number index into `hof`. -/
lemma zero_le_recVal_of_mem_prefAgree {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (j : Fin N) : 0 ≤ recVal j γ := by
  have h := Finset.le_sup' (fun t => ext γ t j)
    (Finset.mem_range.mpr (Nat.succ_pos n) : 0 ∈ Finset.range (n + 1))
  rw [ext_zero_of_mem_prefAgree hU j] at h
  exact h

/-! ### The mark at the record site -/

/-- **The mark at the running record is a cylinder over the record read set.**  The adjoined row
`recRow m j (recVal j γ)` is part of `recRead m j γ`, so all `m - 1` departure coordinates of the
record site are read. -/
theorem measurableSet_siteMark_recVal_cylAt (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (j : Fin N) :
    MeasurableSet[cylAt (N := N) (recRead m j γ)] {U : Array N | SiteMark p m U j (recVal j γ)} := by
  have hset : {U : Array N | SiteMark p m U j (recVal j γ)}
      = ⋂ k : ↥(Finset.Icc 1 (m - 1)),
          {U : Array N | U (j, recVal j γ, (k : ℕ)) ∈ Set.Ioi p} := by
    ext U
    simp only [SiteMark, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi]
    exact ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩
  rw [hset]
  exact MeasurableSet.iInter fun k =>
    measurableSet_cylAt_of_mem
      (Finset.mem_union_right _ (mem_recRow.mpr ⟨(k : ℕ), k.2, rfl⟩)) measurableSet_Ioi

/-! ### The revelation gate below the record -/

/-- **(reveal) read on a piece.**  If walker `j` is marked at the nonnegative site `x`, and `x`
lies strictly below the record of the prefix, then the revelation gate `m ≤ L_n^j(x)` holds.

This is `reveal_runMax` with the running record identified with the prefix record; it is the
contrapositive form used below: a *failing* gate on a piece forbids every mark at that site. -/
theorem gate_of_siteMark_of_lt_recVal {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) {γ : Pref N n}
    {U : Array N} (hU : U ∈ prefAgree p m γ) (j : Fin N) {x : ℕ} (hx : (x : ℤ) < recVal j γ)
    (hmark : SiteMark p m U j (x : ℤ)) :
    m ≤ localTime (fun t => ext γ t j) n (x : ℤ) := by
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := by exact_mod_cast Nat.zero_le x
  have hmax : (x : ℤ) + 1 ≤ runMax p m U j n := by
    rw [runMax_eq_recVal p m U j n, recVal_prefOf_of_mem hU j]
    omega
  have hrev := reveal_runMax hp m U j hx0 hmark hmax
  rwa [localTime_congr (X := fun k => (trajectory p m U k).pos j)
    (Y := fun t => ext γ t j) (fun s hs => (ext_prefOf_of_mem hU hs j).symm)] at hrev

/-! ### The cylinder event carrying the mark at a site -/

/-- The cylinder event through which the piece `γ` reads the mark at the site `x`.  At the
record site it is the mark itself (the row is adjoined); strictly below the record it is the
mark *on the gate*, and off the gate it is empty.  It is a genuine cylinder set over
`recRead m j γ` (`measurableSet_markSet`) and it agrees with the mark throughout the piece
(`mem_markSet_iff`), for every site `x` at or below the prefix record. -/
noncomputable def markSet (p : ℝ) (m n : ℕ) (j : Fin N) (γ : Pref N n) (x : ℕ) :
    Set (Array N) :=
  if (x : ℤ) = recVal j γ then {U : Array N | SiteMark p m U j (x : ℤ)}
  else {U : Array N | m ≤ localTime (fun t => ext γ t j) n (x : ℤ) ∧ SiteMark p m U j (x : ℤ)}

/-- **`markSet` at a site is a cylinder over `recRead m j γ`.**  No hypothesis on `x` is needed:
the record site is the adjoined row, and off the record site the gate either holds — and then
`measurableSet_cylAt_mark` applies — or fails, and then the set is empty. -/
theorem measurableSet_markSet {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    {γ : Pref N n} {U₀ : Array N} (hU₀ : U₀ ∈ prefAgree p m γ) (x : ℕ) :
    MeasurableSet[cylAt (N := N) (recRead m j γ)] (markSet p m n j γ x) := by
  classical
  unfold markSet
  by_cases heq : (x : ℤ) = recVal j γ
  · rw [if_pos heq]
    simpa only [heq] using measurableSet_siteMark_recVal_cylAt p m γ j
  · rw [if_neg heq]
    by_cases hg : m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
    · have hgate : m ≤ (trajectory p m U₀ n).ell j (x : ℤ) := by
        rw [ell_eq_localTime_of_prefAgree p m n hU₀ le_rfl j (x : ℤ)]
        exact hg
      have hmark := measurableSet_cylAt_mark p m n le_rfl hU₀ j (x : ℤ) hgate
      have hset : {U : Array N | m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
            ∧ SiteMark p m U j (x : ℤ)}
          = {U : Array N | SiteMark p m U j (x : ℤ)} := by
        ext U
        exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
      rw [hset]
      exact cylAt_mono (fun c hc => Finset.mem_union_left _ hc) _ hmark
    · have hset : {U : Array N | m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
            ∧ SiteMark p m U j (x : ℤ)} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        rintro U ⟨hg', -⟩
        exact hg hg'
      rw [hset]
      exact (cylAt (recRead m j γ)).measurableSet_empty

/-- **`markSet` agrees with the mark throughout the piece**, for every site `x` at or below the
prefix record.  The strict case is `gate_of_siteMark_of_lt_recVal`: a marked site below the
record satisfies the gate. -/
theorem mem_markSet_iff {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) {γ : Pref N n}
    {U : Array N} (hU : U ∈ prefAgree p m γ) {x : ℕ} (hx : (x : ℤ) ≤ recVal j γ) :
    U ∈ markSet p m n j γ x ↔ SiteMark p m U j (x : ℤ) := by
  classical
  unfold markSet
  by_cases heq : (x : ℤ) = recVal j γ
  · rw [if_pos heq]
    exact Iff.rfl
  · rw [if_neg heq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    exact gate_of_siteMark_of_lt_recVal hp m n hU j (lt_of_le_of_ne hx heq) h


/-! ### `hof` is measurable in the mark configuration with no hypothesis on `p`

`SwarmMarks.measurable_hof` bootstraps through `hstep_eq_rho` and therefore asks for `p ≠ 0`.
Measurability of `hof p ω n` in `ω` holds for *every* `p`: `hstep p b ·` is affine for each `b`
(`hstep_false`, `hstep_true`), so the recursion is a composition of measurable maps.  The seed
below is then measurable with no hypothesis on `p` beyond the gate `1/2 ≤ p`. -/

lemma hstep_ite (p : ℝ) (b : Bool) (h : ℝ) :
    SwarmMarks.hstep p b h = if b = true then 1 / p + ((1 - p) / p) * h else h + 2 := by
  cases b <;> simp [SwarmMarks.hstep]

/-- `hstep` is jointly measurable in the mark and the incoming value. -/
lemma measurable_hstep_pair (p : ℝ) : Measurable fun q : Bool × ℝ => SwarmMarks.hstep p q.1 q.2 := by
  have heq : (fun q : Bool × ℝ => SwarmMarks.hstep p q.1 q.2)
      = fun q => if q.1 = true then 1 / p + ((1 - p) / p) * q.2 else q.2 + 2 := by
    funext q
    exact hstep_ite p q.1 q.2
  rw [heq]
  exact Measurable.ite (measurable_fst (measurableSet_singleton true)) (by fun_prop) (by fun_prop)

/-- The event that a single mark is `true` is measurable for the product σ-algebra. -/
lemma measurableSet_pi_true (i : ℕ) : MeasurableSet {ω : ℕ → Bool | ω i = true} := by
  have hEq : ((fun f : ℕ → Bool => f i) ⁻¹' ({true} : Set Bool)) = {ω : ℕ → Bool | ω i = true} := by
    ext ω
    simp
  rw [← hEq]
  exact measurable_pi_apply i (measurableSet_singleton true)

/-- **`hof p ω n` is measurable in `ω` for every real `p`** (no `p ≠ 0`). -/
lemma measurable_hof_any (p : ℝ) (n : ℕ) : Measurable fun ω : ℕ → Bool => SwarmMarks.hof p ω n := by
  induction n with
  | zero =>
      have heq : (fun ω : ℕ → Bool => SwarmMarks.hof p ω 0)
          = fun ω => if ω 0 = true then 1 / p + ((1 - p) / p) * 1 else 1 + 2 := by
        funext ω
        rw [SwarmMarks.hof_zero]
        exact hstep_ite p (ω 0) 1
      rw [heq]
      exact Measurable.ite (measurableSet_pi_true 0) measurable_const measurable_const
  | succ k ih =>
      have heq : (fun ω : ℕ → Bool => SwarmMarks.hof p ω (k + 1))
          = fun ω => if ω (k + 1) = true then
              1 / p + ((1 - p) / p) * SwarmMarks.hof p ω k else SwarmMarks.hof p ω k + 2 := by
        funext ω
        rw [SwarmMarks.hof_succ]
        exact hstep_ite p (ω (k + 1)) (SwarmMarks.hof p ω k)
      rw [heq]
      exact Measurable.ite (measurableSet_pi_true (k + 1))
        (measurable_const.add (measurable_const.mul ih)) (ih.add measurable_const)

/-! ### The seed and its piece approximation -/

/-- **The paper's full-history seed**: `h_j` at the running record `M_n^j`, driven by the actual
site marks of the actual array. -/
noncomputable def seedH (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) : ℝ :=
  SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (recVal j (prefOf p m n U)).toNat

/-- The seed written with the running maximum, which is the actual record `M_n^j`. -/
theorem seedH_eq_runMax (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    seedH p m n j U
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (runMax p m U j n).toNat := by
  unfold seedH
  rw [runMax_eq_recVal p m U j n]

/-- **Alignment of the paper's site marks with `RecExp.markB`.**  `siteMarks p m U j x` is the
`decide` of `SiteMark p m U j (x : ℤ)`, while the shifted recursion of `RecExp.lean` is driven by
`markB p m j y U`, the `if`-version at the *integer* site `y`.  At `y = (x : ℤ)` the two agree.
This is the bridge needed to compare `markSeq`/`rhoStep` with `siteMarks`. -/
theorem siteMarks_eq_markB_at (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) :
    SwarmLogRatio.siteMarks p m U j x = markB p m j (x : ℤ) U := by
  classical
  by_cases h : SiteMark p m U j (x : ℤ)
  · rw [markB_pos h]
    exact decide_eq_true h
  · rw [markB_neg h]
    exact decide_eq_false h

/-- The `γ`-piece approximation of the seed: on the piece it reads the marks `0, …, M` through
the cylinder events `markSet p m n j γ`, and off every piece it is `0`. -/
noncomputable def seedPiece (p : ℝ) (m n : ℕ) (j : Fin N) (γ : Pref N n) : Array N → ℝ := by
  classical
  exact if (∃ U' : Array N, U' ∈ prefAgree p m γ) then
    (fun U : Array N => SwarmMarks.hof p (fun x : ℕ =>
      if x ≤ (recVal j γ).toNat then (if U ∈ markSet p m n j γ x then true else false)
      else false) (recVal j γ).toNat)
  else 0

/-- **The piece approximation is a cylinder function over `recRead m j γ`.**  Each of the marks
`0, …, M` is read through its cylinder event; the marks above `M` are replaced by `false`, which
`hof` does not see. -/
theorem measurable_seedPiece {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (γ : Pref N n) :
    Measurable[cylAt (N := N) (recRead m j γ)] (seedPiece p m n j γ) := by
  classical
  unfold seedPiece
  by_cases hne : ∃ U' : Array N, U' ∈ prefAgree p m γ
  · rw [if_pos hne]
    obtain ⟨U₀, hU₀⟩ := hne
    have hcomp : ∀ x : ℕ, Measurable[cylAt (N := N) (recRead m j γ)]
        (fun U : Array N => if x ≤ (recVal j γ).toNat then
          (if U ∈ markSet p m n j γ x then true else false) else false) := by
      intro x
      by_cases hxM : x ≤ (recVal j γ).toNat
      · have heq : (fun U : Array N => if x ≤ (recVal j γ).toNat then
            (if U ∈ markSet p m n j γ x then true else false) else false)
            = fun U : Array N => if U ∈ markSet p m n j γ x then true else false := by
          funext U
          rw [if_pos hxM]
        rw [heq]
        exact Measurable.ite (p := fun U : Array N => U ∈ markSet p m n j γ x)
          (measurableSet_markSet hp m n j hU₀ x) measurable_const measurable_const
      · have heq : (fun U : Array N => if x ≤ (recVal j γ).toNat then
            (if U ∈ markSet p m n j γ x then true else false) else false)
            = fun _ : Array N => false := by
          funext U
          rw [if_neg hxM]
        rw [heq]
        exact measurable_const
    have hseq : Measurable[cylAt (N := N) (recRead m j γ)] (fun U : Array N => (fun x : ℕ =>
        if x ≤ (recVal j γ).toNat then (if U ∈ markSet p m n j γ x then true else false)
        else false)) := by
      letI : MeasurableSpace (Array N) := cylAt (N := N) (recRead m j γ)
      exact measurable_pi_iff.2 hcomp
    exact fun s hs => hseq (measurable_hof_any p (recVal j γ).toNat hs)
  · rw [if_neg hne]
    exact measurable_const

/-- **The piece approximation reproduces the seed on its piece.** -/
theorem seedH_eq_seedPiece {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    {γ : Pref N n} {U : Array N} (hU : U ∈ prefAgree p m γ) :
    seedH p m n j U = seedPiece p m n j γ U := by
  classical
  have hne : ∃ U' : Array N, U' ∈ prefAgree p m γ := ⟨U, hU⟩
  have hnonneg : 0 ≤ recVal j γ := zero_le_recVal_of_mem_prefAgree hU j
  have hM : ((recVal j γ).toNat : ℤ) = recVal j γ := Int.toNat_of_nonneg hnonneg
  have hrec : recVal j (prefOf p m n U) = recVal j γ := recVal_prefOf_of_mem hU j
  have hsite : ∀ i : ℕ, SwarmLogRatio.siteMarks p m U j i
      = if SiteMark p m U j (i : ℤ) then true else false := by
    intro i
    simp only [SwarmLogRatio.siteMarks]
    by_cases h : SiteMark p m U j (i : ℤ) <;> simp [h]
  unfold seedH seedPiece
  rw [if_pos hne, hrec]
  refine SwarmMarks.hof_congr (recVal j γ).toNat (fun i hi => ?_)
  rw [if_pos hi, hsite i]
  have hxi : (i : ℤ) ≤ recVal j γ := by
    have h1 : (i : ℤ) ≤ ((recVal j γ).toNat : ℤ) := by exact_mod_cast hi
    rwa [hM] at h1
  have hmem := mem_markSet_iff hp m n j hU (x := i) hxi
  by_cases hU' : U ∈ markSet p m n j γ i
  · rw [if_pos hU', if_pos (hmem.mp hU')]
  · rw [if_neg hU', if_neg (fun h => hU' (hmem.mpr h))]

/-! ### The seed is measurable for the record-enlarged σ-algebra -/

/-- **Full-history seed measurability.**  The paper's seed `h_j(M_n^j)` is measurable for the
record-enlarged σ-algebra `enlRecMeas p m n j` of `RecEnv.lean`: the piecewise cylinder
approximation `seedPiece` is `cylAt (recRead m j γ)`-measurable and agrees with the seed on each
piece, which is exactly the defining property of `pieceMeas`. -/
theorem measurable_seedH {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[enlRecMeas (N := N) p m n j] (seedH p m n j) := by
  refine measurable_pieceMeas (f' := fun γ => seedPiece p m n j γ)
    (fun γ => measurable_seedPiece hp m n j γ) (fun γ U hU => seedH_eq_seedPiece hp m n j hU)

/-- The same statement with the running maximum in place of the prefix record. -/
theorem measurable_seedH_runMax {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ)
    (j : Fin N) :
    Measurable[enlRecMeas (N := N) p m n j]
      (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (runMax p m U j n).toNat) := by
  have heq : (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      (runMax p m U j n).toNat) = seedH p m n j := by
    funext U
    exact (seedH_eq_runMax p m n j U).symm
  rw [heq]
  exact measurable_seedH hp m n j

/-- **The seed measurability in fully expanded form**, for consumers that do not want to unfold
`seedH`: `h_j` at the running record `M_n^j`, driven by the actual site marks, is
`enlRecMeas p m n j`-measurable. -/
theorem measurable_hof_siteMarks_recVal {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[enlRecMeas (N := N) p m n j]
      (fun U : Array N => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        (recVal j (prefOf p m n U)).toNat) :=
  measurable_seedH hp m n j

/-- **The site-level content, in the form used downstream**: at every site at or below the actual
running record, the marked event is `enlRecMeas`-measurable.  (Above the record this is false in
general, which is why the seed is read as `hof` of the marks `0, …, M` and nothing else.) -/
theorem measurableSet_siteMark_of_le_recVal {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (x : ℕ) :
    MeasurableSet[enlRecMeas (N := N) p m n j]
      ({U : Array N | (x : ℤ) ≤ recVal j (prefOf p m n U)}
        ∩ {U : Array N | SiteMark p m U j (x : ℤ)}) := by
  classical
  intro γ
  by_cases hne : ∃ U' : Array N, U' ∈ prefAgree p m γ
  · obtain ⟨U₀, hU₀⟩ := hne
    by_cases hx : (x : ℤ) ≤ recVal j γ
    · refine ⟨markSet p m n j γ x, measurableSet_markSet hp m n j hU₀ x, ?_⟩
      ext U
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, (mem_markSet_iff hp m n j h1 hx).mpr h3⟩
      · rintro ⟨h1, h2⟩
        have hle : (x : ℤ) ≤ recVal j (prefOf p m n U) := by
          rw [recVal_prefOf_of_mem h1 j]; exact hx
        exact ⟨h1, hle, (mem_markSet_iff hp m n j h1 hx).mp h2⟩
    · refine ⟨∅, (cylAt (recRead m j γ)).measurableSet_empty, ?_⟩
      rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
      rintro U ⟨h1, h2, -⟩
      have hle : (x : ℤ) ≤ recVal j γ := by
        rw [← recVal_prefOf_of_mem h1 j]; exact h2
      exact hx hle
  · refine ⟨∅, (cylAt (recRead m j γ)).measurableSet_empty, ?_⟩
    rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
    rintro U ⟨h1, -⟩
    exact hne ⟨U, h1⟩

end Swarming.Enl


