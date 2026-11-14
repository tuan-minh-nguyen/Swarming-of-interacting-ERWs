/-
  **Enlarged-filtration measurability of the revealed weight.**

  The paper's proof of Lemma `transience` uses the sentence

    "On this event, the variables `omega_j(x)` for `b0 < x <= b1` are `F_s`-measurable
     by (reveal)."

  `Swarm/BadCarrier.lean` proves the *deterministic* content of that sentence
  (`siteMark_coords_read`, `revealedWeight_eq_omegaAt_of_badPos`) but explicitly does not
  produce a σ-algebra statement.  This file supplies it, for the genuine enlarged filtration
  `Swarming.Enl.enlFilt` of `Swarm/EnlFilt.lean` built on the actual interacting
  trajectory.

  Main results (namespace `Swarming.Enl`):

  * `ell_eq_localTime_of_prefAgree` — the local time `L_s^j(x)` is a function of the position
    prefix up to `n >= s` only;
  * `mem_prefRead_of_gate` — if the revelation gate `m <= L_s^j(x)` holds, then *every*
    coordinate `(j, x, k)`, `1 <= k <= m-1`, of the site mark belongs to the finite read set
    `prefRead n γ` of the prefix.  Together with `SiteMark` being a cylinder condition on those
    coordinates this is the entire mathematical content of the paper's sentence;
  * `measurableSet_cylAt_mark` — on a piece with a passing gate the site mark is a cylinder set;
  * `measurableSet_revealedGate` — the set `{m <= L_s^j(x)} ∩ {B_j(x) = 1}` on which the
    revealed weight is `p` belongs to `enlMeas p m n`;
  * `measurable_revealedWeight` / `measurable_revealedWeight_enlFilt` — the revealed weight
    `(U, x) |-> revealedWeight p m U j s x` is `enlMeas p m n`-measurable for `s <= n`, and in
    particular `enlFilt s`-measurable;
  * `measurable_revealedWeight_enlFilt_of_le` — it is `enlFilt t`-measurable for every `t >= s`
    (monotonicity of the filtration), which is the form the crossing estimate consumes, because
    the weights revealed at time `s` are used at all later times `t >= s`;
  * `measurableSet_badPos` — the paper's bad-time event is itself `enlFilt s`-measurable;
  * `measurableSet_omegaAt_inter_badPos`, `measurable_omegaAt_of_badPos`,
    `measurable_window_omegaAt_of_badPos` — **the paper's sentence**: on the bad-time event the
    *environment* values `omega_j(x)` of the window `b0 < x <= b1` are measurable for the
    enlarged filtration at time `s`, pointwise and jointly.

  The restriction to the bad-time event is not an artefact: off the gate the coordinate
  `(j, x, 1)` is not read by the prefix, so `B_j(x)` is genuinely not determined by `enlFilt s`
  (the fallback `1/2` in `revealedWeight` is exactly the conservative replacement).  What is
  proved here is that on the binding event of the crossing estimate nothing is lost.

  No proof hole, no custom axiom.  Depends only on the integrated modules
  `Swarm/EnlFilt.lean` and `Swarm/BadCarrier.lean`.
-/
import Swarm.Imports
import Swarm.EnlFilt
import Swarm.BadCarrier

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The prefix determines the local time -/

/-- **The local time at time `s` is a function of the position prefix up to `n >= s`.**  This is
the reason the enlarged filtration is indexed by path prefixes: `enlMeas p m n` sees the path up
to `n`, hence every visit count up to `n`. -/
lemma ell_eq_localTime_of_prefAgree (p : ℝ) (m n : ℕ) {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) {s : ℕ} (hs : s ≤ n) (j : Fin N) (x : ℤ) :
    (trajectory p m U s).ell j x = localTime (fun t => ext γ t j) s x := by
  rw [Swarming.Trajectory.ell_eq_localTime]
  exact localTime_congr fun t ht => (ext_prefOf_of_mem hU (by omega) j).symm

/-! ### The gate puts the site mark's coordinates into the read set -/

/-- **Revelation at the level of read sets.**  If the gate `m <= L_s^j(x)` holds and `s <= n`,
then each coordinate `(j, x, k)` with `1 <= k <= m - 1` of the site mark `B_j(x)` lies in the
finite set `prefRead n γ` of coordinates read strictly before time `n` along the prefix `γ` that
`U` follows.  This is `siteMark_coords_read` transported to the prefix-indexed read set, and it
is exactly what makes the mark a cylinder function on the event `{gate}`. -/
lemma mem_prefRead_of_gate (p : ℝ) (m n : ℕ) {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) {s : ℕ} (hs : s ≤ n) {j : Fin N} {x : ℤ}
    (hgate : m ≤ (trajectory p m U s).ell j x) {k : ℕ} (hk : k ∈ Finset.Icc 1 (m - 1)) :
    (j, x, k) ∈ prefRead n γ := by
  obtain ⟨t, hts, ht⟩ := Swarming.Trajectory.siteMark_coords_read p m U j s x hgate hk
  rw [departCoord_eq] at ht
  simp only [Prod.mk.injEq] at ht
  obtain ⟨-, hpos, hell⟩ := ht
  rw [mem_prefRead]
  refine ⟨t, by omega, ?_, ?_⟩
  · rw [ext_prefOf_of_mem hU (by omega) j, hpos]
  · have h1 : (trajectory p m U t).ell j x = localTime (fun s => ext γ s j) t x :=
      ell_eq_localTime_of_prefAgree p m n hU (by omega) j x
    have h2 : (trajectory p m U t).ell j x = k := by
      rw [← hpos]
      exact hell
    rw [← h1]
    exact h2

/-! ### The mark is a cylinder function on the gate -/

/-- **The site mark is a cylinder set on a piece whose gate passes.**  The mark
`B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p}` is a condition on the finitely many coordinates
`(j, x, k)`, `1 <= k <= m-1`; on a piece with `m <= L_s^j(x)` and `s <= n` all of them lie in
`prefRead n γ`, hence the mark belongs to the σ-algebra `cylAt (prefRead n γ)` of the piece. -/
lemma measurableSet_cylAt_mark (p : ℝ) (m n : ℕ) {γ : Pref N n} {s : ℕ} (hs : s ≤ n)
    {U₀ : Array N} (hU₀ : U₀ ∈ prefAgree p m γ) (j : Fin N) (x : ℤ)
    (hgate : m ≤ (trajectory p m U₀ s).ell j x) :
    MeasurableSet[cylAt (N := N) (prefRead n γ)]
      {U : Array N | ∀ k ∈ Finset.Icc 1 (m - 1), p < U (j, x, k)} := by
  have hset : {U : Array N | ∀ k ∈ Finset.Icc 1 (m - 1), p < U (j, x, k)}
      = ⋂ k : ↥(Finset.Icc 1 (m - 1)), {U : Array N | U (j, x, (k : ℕ)) ∈ Set.Ioi p} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Ioi]
    exact ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩
  rw [hset]
  exact MeasurableSet.iInter fun k =>
    measurableSet_cylAt_of_mem (mem_prefRead_of_gate p m n hU₀ hs hgate k.2) measurableSet_Ioi

/-- Set form of the mark, for rewriting. -/
lemma siteMark_eq_cylinder (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    {U : Array N | SiteMark p m U j x}
      = {U : Array N | ∀ k ∈ Finset.Icc 1 (m - 1), p < U (j, x, k)} := rfl

/-! ### Measurability of the revealed set -/

/-- **The revealed set `{gate} ∩ {mark}` is measurable for the enlarged filtration.**  On each
prefix `γ` the gate `m <= L_s^j(x)` is a constant (`ell_eq_localTime_of_prefAgree`); if it is
false, or if the piece is empty, the intersection with the piece is empty, and if it is true the
mark is the cylinder set of `measurableSet_cylAt_mark`. -/
theorem measurableSet_revealedGate (p : ℝ) (m n : ℕ) {s : ℕ} (hs : s ≤ n) (j : Fin N) (x : ℤ) :
    MeasurableSet[enlMeas p m n]
      {U : Array N | m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x} := by
  intro γ
  by_cases hne : ∃ U : Array N, U ∈ prefAgree p m γ
  · obtain ⟨U₀, hU₀⟩ := hne
    by_cases hg : m ≤ localTime (fun t => ext γ t j) s x
    · refine ⟨{U : Array N | ∀ k ∈ Finset.Icc 1 (m - 1), p < U (j, x, k)},
        measurableSet_cylAt_mark p m n hs hU₀ j x ?_, ?_⟩
      · rw [ell_eq_localTime_of_prefAgree p m n hU₀ hs j x]
        exact hg
      · refine Set.Subset.antisymm ?_ ?_
        · rintro U ⟨hU, -, hmark⟩
          exact ⟨hU, hmark⟩
        · rintro U ⟨hU, hmark⟩
          exact ⟨hU, by
            rw [ell_eq_localTime_of_prefAgree p m n hU hs j x]; exact hg, hmark⟩
    · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
      rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
      rintro U ⟨hU, h1, -⟩
      exact hg (by rw [← ell_eq_localTime_of_prefAgree p m n hU hs j x]; exact h1)
  · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
    rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
    rintro U ⟨hU, -⟩
    exact hne ⟨U, hU⟩

/-- **The revealed weight is measurable for the enlarged filtration at every time `n >= s`.**

This is the genuine σ-algebra statement behind the paper's "the variables `omega_j(x)` are
`F_s`-measurable by (reveal)": the weight is `p` exactly on the measurable set
`{m <= L_s^j(x)} ∩ {B_j(x) = 1}` and `1/2` on its complement, and both values are constant, so
`Measurable.ite` concludes. -/
theorem measurable_revealedWeight (p : ℝ) (m n : ℕ) {s : ℕ} (hs : s ≤ n) (j : Fin N) (x : ℤ) :
    Measurable[enlMeas p m n] fun U : Array N => revealedWeight p m U j s x := by
  classical
  have hA := measurableSet_revealedGate p m n hs j x
  have hfun : (fun U : Array N => revealedWeight p m U j s x)
      = fun U => if U ∈ {U : Array N |
            m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x} then p else 1 / 2 := by
    funext U
    by_cases h : U ∈ {U : Array N |
        m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x}
    · have h' : m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x := h
      rw [revealedWeight, if_pos h', if_pos h]
    · have h' : ¬ (m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x) := h
      rw [revealedWeight, if_neg h', if_neg h]
  rw [hfun]
  exact Measurable.ite hA measurable_const measurable_const

/-- The same statement directly for the **genuine `MeasureTheory.Filtration`** `enlFilt`. -/
theorem measurable_revealedWeight_enlFilt (p : ℝ) (m s : ℕ) (j : Fin N) (x : ℤ) :
    Measurable[enlFilt (N := N) p m s] fun U : Array N => revealedWeight p m U j s x :=
  measurable_revealedWeight p m s le_rfl j x

/-- **The weight revealed at time `s` is measurable at every later time `t >= s`.**  The crossing
estimate fixes the environment at the revelation time `s` but consumes it at all later times
`t >= s`; nesting of `enlFilt` transports the measurability. -/
theorem measurable_revealedWeight_enlFilt_of_le (p : ℝ) (m : ℕ) {s t : ℕ} (hst : s ≤ t)
    (j : Fin N) (x : ℤ) :
    Measurable[enlFilt (N := N) p m t] fun U : Array N => revealedWeight p m U j s x :=
  Measurable.mono (measurable_revealedWeight_enlFilt p m s j x)
    (Filtration.mono (enlFilt (N := N) p m) hst) le_rfl

/-! ### Measurability of the bad-time event -/

/-- **The paper's bad-time event is measurable for the enlarged filtration.**  The position
constraint is adapted (`enl_pos_measurable`); the running-maximum constraint
`b1 + 1 <= M_s^j` is a finite disjunction of position constraints. -/
theorem measurableSet_badPos (p : ℝ) (m n : ℕ) {s : ℕ} (hs : s ≤ n) (i j : Fin N) (b1 : ℤ) :
    MeasurableSet[enlMeas p m n] {U : Array N | badPos p m U i j b1 s} := by
  have hpos : MeasurableSet[enlMeas p m n]
      {U : Array N | (trajectory p m U s).pos i = b1} :=
    enl_pos_measurable p m n hs i (measurableSet_singleton b1)
  have hmax : MeasurableSet[enlMeas p m n]
      {U : Array N | b1 + 1 ≤ runMax p m U j s} := by
    have hset : {U : Array N | b1 + 1 ≤ runMax p m U j s}
        = ⋃ t : ↥(Finset.range (s + 1)),
            {U : Array N | b1 + 1 ≤ (trajectory p m U (t : ℕ)).pos j} := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j s
        refine ⟨⟨t, Finset.mem_range.mpr (by omega)⟩, ?_⟩
        show b1 + 1 ≤ (trajectory p m U t).pos j
        rw [hte]
        exact h
      · rintro ⟨⟨t, ht⟩, hle⟩
        have hts : (t : ℕ) ≤ s := by
          simp only [Finset.mem_range] at ht
          omega
        exact le_trans hle (le_trans (le_runMax p m U j (t : ℕ)) (runMax_mono p m U j hts))
    rw [hset]
    exact MeasurableSet.iUnion fun t =>
      enl_pos_measurable p m n (k := (t : ℕ)) (by
        have := t.2
        simp only [Finset.mem_range] at this
        omega) j measurableSet_Ici
  have hEq : {U : Array N | badPos p m U i j b1 s}
      = {U : Array N | (trajectory p m U s).pos i = b1}
        ∩ {U : Array N | b1 + 1 ≤ runMax p m U j s} := rfl
  rw [hEq]
  exact hpos.inter hmax

/-! ### The paper's sentence: the environment of the window is measurable on the bad event -/

/-- **`omega_j(x)` is measurable at time `s` on the bad-time event.**  For a site `x` of the
window `0 <= x <= b1`, `revealedWeight_eq_omegaAt_of_badPos` identifies the paper's environment
value with the revealed weight throughout the bad-time event, so the measurability of the latter
transfers.  This is the exact form of the paper's affirmation, and it is where the restriction to
`{bad}` is unavoidable: the fallback zone is what implements the coordinates not yet read. -/
theorem measurableSet_omegaAt_inter_badPos (hp : 1 / 2 ≤ p) (m n : ℕ) {s : ℕ} (hs : s ≤ n)
    {i j : Fin N} {b1 : ℤ} {x : ℤ} (hx0 : 0 ≤ x) (hxb : x ≤ b1) {T : Set ℝ}
    (hT : MeasurableSet T) :
    MeasurableSet[enlMeas p m n]
      ({U : Array N | badPos p m U i j b1 s} ∩ {U : Array N | omegaAt p m U j x ∈ T}) := by
  have hbad := measurableSet_badPos p m n hs i j b1
  have hw : MeasurableSet[enlMeas p m n]
      {U : Array N | revealedWeight p m U j s x ∈ T} :=
    measurable_revealedWeight p m n hs j x hT
  have hEq : {U : Array N | badPos p m U i j b1 s} ∩ {U : Array N | omegaAt p m U j x ∈ T}
      = {U : Array N | badPos p m U i j b1 s}
        ∩ {U : Array N | revealedWeight p m U j s x ∈ T} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro U ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq] at h2
      refine ⟨h1, ?_⟩
      show revealedWeight p m U j s x ∈ T
      rw [revealedWeight_eq_omegaAt_of_badPos hp m h1 hx0 hxb]
      exact h2
    · rintro U ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq] at h2
      refine ⟨h1, ?_⟩
      show omegaAt p m U j x ∈ T
      rw [← revealedWeight_eq_omegaAt_of_badPos hp m h1 hx0 hxb]
      exact h2
  rw [hEq]
  exact hbad.inter hw

/-! ### The revealed environment as a measurable integrand -/

/-- The environment value of a window site, extended off the bad-time event by the safe constant
`1/2`.  This is the integrand that carries the paper's revealed environment into a conditional
expectation. -/
noncomputable def envAt {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i j : Fin N) (b1 : ℤ) (s : ℕ)
    (x : ℤ) : ℝ := by
  classical
  exact if badPos p m U i j b1 s then omegaAt p m U j x else 1 / 2

lemma envAt_eq_omegaAt {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {i j : Fin N} {b1 : ℤ} {s : ℕ}
    {x : ℤ} (h : badPos p m U i j b1 s) : envAt p m U i j b1 s x = omegaAt p m U j x := by
  classical
  rw [envAt, if_pos h]

lemma envAt_eq_half {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {i j : Fin N} {b1 : ℤ} {s : ℕ}
    {x : ℤ} (h : ¬ badPos p m U i j b1 s) : envAt p m U i j b1 s x = 1 / 2 := by
  classical
  rw [envAt, if_neg h]

/-- **Functional form.**  The environment value of a window site, read as a function that falls
back to the safe constant `1/2` off the bad-time event, is measurable for `enlFilt s`.  This is
the form in which the revealed environment enters a conditional expectation as an integrand. -/
theorem measurable_envAt (hp : 1 / 2 ≤ p) (m n : ℕ) {s : ℕ} (hs : s ≤ n)
    {i j : Fin N} {b1 : ℤ} {x : ℤ} (hx0 : 0 ≤ x) (hxb : x ≤ b1) :
    Measurable[enlMeas p m n] fun U : Array N => envAt p m U i j b1 s x := by
  classical
  have hbad := measurableSet_badPos p m n hs i j b1
  intro T hT
  have hT' : MeasurableSet[enlMeas p m n]
      {U : Array N | badPos p m U i j b1 s ∧ omegaAt p m U j x ∈ T} := by
    have h1 := measurableSet_omegaAt_inter_badPos hp m n hs (i := i) (j := j) (b1 := b1)
      (x := x) hx0 hxb hT
    simpa only [Set.ofPred_and] using h1
  by_cases hhalf : (1 / 2 : ℝ) ∈ T
  · have hunion : {U : Array N | envAt p m U i j b1 s x ∈ T}
        = {U : Array N | badPos p m U i j b1 s}ᶜ
          ∪ {U : Array N | badPos p m U i j b1 s ∧ omegaAt p m U j x ∈ T} := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
      by_cases h : badPos p m U i j b1 s
      · rw [envAt_eq_omegaAt h]
        exact ⟨fun hx => Or.inr ⟨h, hx⟩,
          fun hx => hx.elim (fun h' => absurd h h') (fun h' => h'.2)⟩
      · rw [envAt_eq_half h]
        exact ⟨fun _ => Or.inl h, fun _ => hhalf⟩
    rw [show ((fun U : Array N => envAt p m U i j b1 s x) ⁻¹' T)
        = {U : Array N | envAt p m U i j b1 s x ∈ T} from rfl, hunion]
    exact hbad.compl.union hT'
  · have heq : {U : Array N | envAt p m U i j b1 s x ∈ T}
        = {U : Array N | badPos p m U i j b1 s ∧ omegaAt p m U j x ∈ T} := by
      ext U
      simp only [Set.mem_ofPred_eq]
      by_cases h : badPos p m U i j b1 s
      · rw [envAt_eq_omegaAt h]
        exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩
      · rw [envAt_eq_half h]
        exact ⟨fun hc => absurd hc hhalf, fun hc => absurd hc.1 h⟩
    rw [show ((fun U : Array N => envAt p m U i j b1 s x) ⁻¹' T)
        = {U : Array N | envAt p m U i j b1 s x ∈ T} from rfl, heq]
    exact hT'

/-- **Window form: the paper's sentence as stated.**  The product of the revealed environment
values over the whole window `b0 < y <= b1` is measurable for the enlarged filtration at time
`s`.  This is the coefficient that the crossing estimate multiplies along the window, and it is
measurable jointly in all window sites, not merely site by site. -/
theorem measurable_prod_envAt (hp : 1 / 2 ≤ p) (m n : ℕ) {s : ℕ} (hs : s ≤ n)
    {i j : Fin N} {b1 : ℤ} {b0 : ℤ} (W : Finset ℤ)
    (hW0 : ∀ y ∈ W, 0 ≤ y) (hWb : ∀ y ∈ W, y ≤ b1) :
    Measurable[enlMeas p m n] (fun U : Array N => ∏ y ∈ W, envAt p m U i j b1 s y) := by
  classical
  exact Finset.measurable_prod W fun y hy =>
    measurable_envAt hp m n hs (i := i) (j := j) (b1 := b1) (x := y) (hW0 y hy) (hWb y hy)

/-- The same joint statement for the *revealed weights* themselves: their product over a window is
measurable, since each factor is (`measurable_revealedWeight`). -/
theorem measurable_prod_revealedWeight (p : ℝ) (m n : ℕ) {s : ℕ} (hs : s ≤ n) (j : Fin N)
    (W : Finset ℤ) :
    Measurable[enlMeas p m n] (fun U : Array N =>
      ∏ x ∈ W, revealedWeight p m U j s x) := by
  classical
  exact Finset.measurable_prod W fun x _ => measurable_revealedWeight p m n hs j x

/-- **Window form of the revealed set.**  The event on which the revealed weight is the environment
at *every* site of a finite window is measurable for the enlarged filtration. -/
theorem measurableSet_forall_revealedGate (p : ℝ) (m n : ℕ) {s : ℕ} (hs : s ≤ n) (j : Fin N)
    (W : Finset ℤ) :
    MeasurableSet[enlMeas p m n] {U : Array N | ∀ x ∈ W,
      m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x} := by
  classical
  have hset : {U : Array N | ∀ x ∈ W,
        m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x}
      = ⋂ x ∈ W, {U : Array N | m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact Finset.measurableSet_biInter W fun x _ => measurableSet_revealedGate p m n hs j x

/-- **The revealed weight evaluated at a random site is measurable.**  For `t >= s`, the set
`{revealedWeight p m U j s (X_t^i) ∈ T}` belongs to `enlFilt t`: it is the countable union over the
possible values `x` of the site, on which the weight is a fixed-site (hence measurable) function.
This is the form in which the revealed environment of time `s` is compared with the right
probability `alpha_t^i` at the walker's *current* site, for all `t >= s`. -/
theorem measurableSet_revealedWeight_comp_pos (p : ℝ) (m : ℕ) {s t : ℕ} (hst : s ≤ t) (j : Fin N)
    {i : Fin N} {T : Set ℝ} (hT : MeasurableSet T) :
    MeasurableSet[enlFilt (N := N) p m t]
      {U : Array N | revealedWeight p m U j s ((trajectory p m U t).pos i) ∈ T} := by
  classical
  have hset : {U : Array N | revealedWeight p m U j s ((trajectory p m U t).pos i) ∈ T}
      = ⋃ x : ℤ, ({U : Array N | (trajectory p m U t).pos i = x}
          ∩ {U : Array N | revealedWeight p m U j s x ∈ T}) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨x, hx, hT⟩ => hx ▸ hT⟩
  rw [hset]
  refine MeasurableSet.iUnion fun x => ?_
  refine (enl_pos_measurable p m t le_rfl i (measurableSet_singleton x)).inter ?_
  exact measurable_revealedWeight_enlFilt_of_le p m hst j x hT

/-- **Lower bound, uniformly in the array.**  The revealed weight is at least `1/2` everywhere,
which is the hypothesis `hloh` of the generic crossing layer
(`Swarm/Cross.lean`). -/
theorem forall_one_half_le_revealedWeight (hp : 1 / 2 ≤ p) (m : ℕ) (j : Fin N) (s : ℕ) :
    ∀ (U : Array N) (x : ℤ), 1 / 2 ≤ revealedWeight p m U j s x :=
  fun U x => one_half_le_revealedWeight hp m U j s x

/-- **Upper bound, uniformly in the array.**  For `p < 1` the revealed weight is strictly below
`1` everywhere, which is the hypothesis `hhih` of the generic crossing layer. -/
theorem forall_revealedWeight_lt_one (hp : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (j : Fin N) (s : ℕ) :
    ∀ (U : Array N) (x : ℤ), revealedWeight p m U j s x < 1 :=
  fun U x => lt_of_le_of_lt (revealedWeight_le_p hp m U j s x) hp1

/-! ### The actual right probability and the domination event -/

/-- **Piecewise-constant functions are measurable for the enlarged filtration.**  If a function is
constant on every piece `{path = γ}`, then its level sets are unions of whole pieces and hence
belong to `enlMeas`. -/
lemma measurable_of_piece_constant {p : ℝ} {m n : ℕ} {f : Array N → ℝ}
    (h : ∀ γ : Pref N n, ∃ c : ℝ, ∀ U : Array N, U ∈ prefAgree p m γ → f U = c) :
    Measurable[enlMeas p m n] f := by
  intro T hT γ
  obtain ⟨c, hc⟩ := h γ
  by_cases hcT : c ∈ T
  · refine ⟨Set.univ, MeasurableSet.univ, ?_⟩
    rw [Set.inter_univ]
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    rintro U hU
    exact ⟨hU, by rw [Set.mem_preimage, hc U hU]; exact hcT⟩
  · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
    rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
    rintro U ⟨hU, hUT⟩
    exact hcT (by rwa [Set.mem_preimage, hc U hU] at hUT)

/-- The right probability at the current site is constant on each prefix piece. -/
lemma rightProbability_piece_constant (p : ℝ) (m n : ℕ) (i : Fin N) :
    ∀ γ : Pref N n, ∃ c : ℝ, ∀ U : Array N, U ∈ prefAgree p m γ →
      rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) = c := by
  intro γ
  refine ⟨rightProbability p m
    (fun j x => localTime (fun t => ext γ t j) n x) i (ext γ n i), ?_⟩
  intro U hU
  have hpos : (trajectory p m U n).pos i = ext γ n i := (ext_prefOf_of_mem hU le_rfl i).symm
  have hell : (trajectory p m U n).ell
      = fun j x => localTime (fun t => ext γ t j) n x := by
    funext j x
    exact ell_eq_localTime_of_prefAgree p m n hU le_rfl j x
  rw [hpos, hell]

/-- **The actual right probability at the walker's current site is adapted to the enlarged
filtration**: it is a function of the time-`n` position prefix alone. -/
theorem measurable_rightProbability_enl (p : ℝ) (m n : ℕ) (i : Fin N) :
    Measurable[enlMeas p m n] fun U : Array N =>
      rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) :=
  measurable_of_piece_constant (rightProbability_piece_constant p m n i)

/-- Function form of `measurableSet_revealedWeight_comp_pos`. -/
theorem measurable_revealedWeight_comp_pos_fun (p : ℝ) (m : ℕ) {s t : ℕ} (hst : s ≤ t)
    (j : Fin N) (i : Fin N) :
    Measurable[enlFilt (N := N) p m t] fun U : Array N =>
      revealedWeight p m U j s ((trajectory p m U t).pos i) :=
  fun T hT => measurableSet_revealedWeight_comp_pos p m hst j hT

/-- **The domination event is measurable.**  The event on which the weight revealed at time `s`
dominates walker `i`'s actual right probability at its current site at time `t >= s` belongs to
`enlFilt t`.  This is the measurability side of the domination premise `hdom` of the generic
crossing estimate; the probabilistic content (that it holds a.e. under the bad-time event) is the
separate domination step. -/
theorem measurableSet_domination (p : ℝ) (m : ℕ) {s t : ℕ} (hst : s ≤ t) {i j : Fin N} :
    MeasurableSet[enlFilt (N := N) p m t] {U : Array N |
      revealedWeight p m U j s ((trajectory p m U t).pos i) ≤
        rightProbability p m (trajectory p m U t).ell i ((trajectory p m U t).pos i)} :=
  measurableSet_le (measurable_revealedWeight_comp_pos_fun p m hst j i)
    (measurable_rightProbability_enl p m t i)

end Swarming.Enl


