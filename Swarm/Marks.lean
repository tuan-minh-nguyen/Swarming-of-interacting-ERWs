/-
# Bernoulli site marks on the walk's own randomness, and the mark–excitation bridge

Paper `main_1d_revised.tex`, §2.1 and the strategy paragraph of §1
("Following the comparison argument in [BP, Lemma 2.5], we construct independent Bernoulli
marks by marking a site for a walker when the first `m-1` uniform variables governing its
jumps from that site all exceed `p`. At such a site, that walker must make at least `m`
visits before its first right jump. We therefore know that every nonnegative marked site
strictly below its running maximum is excited for every other walker.").

`GAP_LEDGER.md` records displays `(marks)`, `(reveal)`, `(dominate)` as *not formalised*.
This file formalises `(marks)` for the campaign's concrete trajectory
(`Swarming.Trajectory.trajectory`, driven by the i.i.d. uniform array of
`Swarming.Uniform.arrayMeasure`) and the deterministic consequence that links the marks to
the excitation indicator `Swarming.Model.Excited`:

* `SiteMark p m U i x` — the paper's mark: the first `m-1` departure uniforms from site `x`
  for walker `i` all exceed `p`;
* `step_left_of_mark` — at a marked site, while the walker has made at most `m-1` departures
  from it, the jump is to the left (the paper's "at least `m` visits before its first right
  jump", in one-step form);
* `pos_le_of_no_mark_visits` — if walker `i` has made at most `m-1` visits to `x` by time `n`
  then it has not been above `x` by time `n` (deterministic intermediate-value argument);
* `localTime_ge_of_mark` — **the paper's statement**: at a marked site `x >= 0` strictly below
  the walker's running maximum, the walker has visited `x` at least `m` times;
* `excited_of_mark` — hence at every time at which **another** walker sits at such a site it is
  excited, with the exact hypothesis needed by `rightProbability` (so the drift is `2p-1`);
* `arrayMeasure_siteMark` and `arrayMeasure_marks_family` — the mark family on the array is
  i.i.d. Bernoulli with `q = (1-p)^(m-1)`, the *same* `q` that the verified exponential-moment
  layer `areas/marks` takes as a parameter. Finite families of marks factorise.

Everything is proved; see `ConcreteMarkAudit.lean` for the axiom audit.
-/
import Swarm.Trajectory

namespace Swarming.Marks

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped BigOperators

variable {N : ℕ}

/-! ## 1. The paper's site mark -/

/-- **The paper's mark.**  Site `x` is marked for walker `i` when the first `m - 1` uniform
variables governing its jumps from `x` all exceed `p`.  Visit numbers run from `1` (the
`k`-th departure from a site uses array coordinate `(i, x, k)`), so the condition is on the
coordinates `k = 1, ..., m-1`. -/
def SiteMark (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (x : ℤ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 → p < U (i, x, k)

variable {p : ℝ} {m : ℕ} {U : Array N} {i j : Fin N} {x : ℤ}

/-! ## 2. The one-step consequence of a mark

At a marked site and while the walker has made at most `m-1` departures from it, the jump is
to the left.  This is the paper's "such a walker must make at least `m` visits before its
first right jump". -/

/-- The jump of the trajectory is `+1` or `-1`. -/
theorem pos_step_cases (U : Array N) (p : ℝ) (m : ℕ) (t : ℕ) (i : Fin N) :
    (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 ∨
      (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  unfold drivenStep
  split_ifs
  · left; ring
  · right; ring

/-- A walker standing at `x` has made at least one visit to `x`. -/
lemma one_le_ell_of_pos {t : ℕ} (hpos : (trajectory p m U t).pos i = x) :
    1 ≤ (trajectory p m U t).ell i x := by
  have hloc : (trajectory p m U t).ell i x
      = localTime (fun s => (trajectory p m U s).pos i) t x := ell_eq_localTime p m U t i x
  have hpos' := localTime_pos_iff (fun s => (trajectory p m U s).pos i) t x |>.mpr
    ⟨t, le_rfl, hpos⟩
  omega

/-- **At a marked site, a departure among the first `m-1` from that site is to the left.** -/
theorem step_left_of_mark (hp : 1 / 2 ≤ p) (hmark : SiteMark p m U i x) {t : ℕ}
    (hpos : (trajectory p m U t).pos i = x)
    (hell : (trajectory p m U t).ell i x ≤ m - 1) :
    (trajectory p m U (t + 1)).pos i = x - 1 := by
  have hellpos : 1 ≤ (trajectory p m U t).ell i x := one_le_ell_of_pos hpos
  have hU : p < U (i, x, (trajectory p m U t).ell i x) := hmark _ hellpos hell
  have hrp : rightProbability p m (trajectory p m U t).ell i x ≤ p :=
    rightProbability_le_p hp m _ i x
  have hnot : ¬ (U (i, x, (trajectory p m U t).ell i x)
      ≤ rightProbability p m (trajectory p m U t).ell i x) := not_le.mpr (lt_of_le_of_lt hrp hU)
  rw [trajectory_succ, nextWalkState_pos, nextPos, hpos]
  simp only [drivenStep, hnot, if_false]
  ring

/-! ## 3. The geometric core: a marked site below the running maximum is visited `m` times -/

/-- **Deterministic intermediate-value statement.**  If walker `i` has made at most `m-1`
visits to a marked site `x >= 0` by time `n`, then it has not been strictly above `x` by time
`n`: every departure from `x` so far is to the left, and any crossing of `x` from below needs a
right departure from `x`. -/
theorem pos_le_of_mark_hell (hp : 1 / 2 ≤ p) (hx0 : 0 ≤ x) (hmark : SiteMark p m U i x)
    {n : ℕ} (hL : (trajectory p m U n).ell i x ≤ m - 1) :
    ∀ t, t ≤ n → (trajectory p m U t).pos i ≤ x := by
  intro t
  induction t with
  | zero =>
      intro _
      rw [trajectory_zero]
      simpa using hx0
  | succ t ih =>
      intro ht
      have hprev : (trajectory p m U t).pos i ≤ x := ih (by omega)
      rcases lt_or_eq_of_le hprev with hlt | heq
      · have hstep := pos_step_cases U p m t i
        omega
      · have hell : (trajectory p m U t).ell i x ≤ m - 1 := by
          have hmono : (trajectory p m U t).ell i x
              = localTime (fun s => (trajectory p m U s).pos i) t x :=
            ell_eq_localTime p m U t i x
          have hmono' : localTime (fun s => (trajectory p m U s).pos i) t x
              ≤ localTime (fun s => (trajectory p m U s).pos i) n x :=
            localTime_mono _ (by omega) x
          have hn : (trajectory p m U n).ell i x
              = localTime (fun s => (trajectory p m U s).pos i) n x :=
            ell_eq_localTime p m U n i x
          omega
        have hleft := step_left_of_mark hp hmark heq hell
        omega

/-- **The paper's claim.**  A marked site `x >= 0` strictly below walker `i`'s running maximum
(at some time `t <= n`) has been visited by walker `i` at least `m` times by time `n`. -/
theorem localTime_ge_of_mark (hp : 1 / 2 ≤ p) (hx0 : 0 ≤ x) (hmark : SiteMark p m U i x)
    {n : ℕ} (hreach : ∃ t, t ≤ n ∧ x < (trajectory p m U t).pos i) :
    m ≤ localTime (fun s => (trajectory p m U s).pos i) n x := by
  by_contra hcon
  push Not at hcon
  have hL : (trajectory p m U n).ell i x ≤ m - 1 := by
    have hn : (trajectory p m U n).ell i x
        = localTime (fun s => (trajectory p m U s).pos i) n x := ell_eq_localTime p m U n i x
    omega
  obtain ⟨t, ht, hgt⟩ := hreach
  have := pos_le_of_mark_hell hp hx0 hmark hL t ht
  omega

/-! ## 4. Excitation of the *other* walkers at a marked site -/

/-- **Every nonnegative marked site below the running maximum is excited for every other
walker** (paper §1 strategy, the step that converts the mark layer into the occupation bound).
At any time `n` at which walker `j != i` sits at such a site, walker `j` is excited there. -/
theorem excited_of_mark (hp : 1 / 2 ≤ p) (hij : j ≠ i) {n : ℕ}
    (hx0 : 0 ≤ (trajectory p m U n).pos j)
    (hmark : SiteMark p m U i ((trajectory p m U n).pos j))
    (hreach : ∃ t, t ≤ n ∧ (trajectory p m U n).pos j < (trajectory p m U t).pos i) :
    Excited m (trajectory p m U n).ell j ((trajectory p m U n).pos j) := by
  have hvisit : m ≤ (trajectory p m U n).ell i ((trajectory p m U n).pos j) := by
    rw [ell_eq_localTime p m U n i ((trajectory p m U n).pos j)]
    exact localTime_ge_of_mark hp hx0 hmark hreach
  unfold Excited otherVisits
  refine le_trans hvisit ?_
  have hsingle := Finset.single_le_sum
    (f := fun j' : Fin N => if j' = j then 0 else (trajectory p m U n).ell j' ((trajectory p m U n).pos j))
    (fun j' _ => Nat.zero_le _) (Finset.mem_univ i)
  rwa [if_neg (Ne.symm hij)] at hsingle

/-- The array coordinates read by the mark of walker `i` at site `x`. -/
def markCoords (m : ℕ) (i : Fin N) (x : ℤ) : Finset (Fin N × ℤ × ℕ) :=
  (Finset.range (m - 1)).image (fun k => (i, x, k + 1))

/-- The cylinder set "every coordinate in `S` exceeds `p`". -/
def coordsCyl (p : ℝ) (S : Finset (Fin N × ℤ × ℕ)) : Set (Array N) :=
  {U | ∀ c ∈ S, p < U c}

lemma markCoords_card (m : ℕ) (i : Fin N) (x : ℤ) :
    (markCoords (N := N) m i x).card = m - 1 := by
  rw [markCoords, Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro a _ b _ hab
    have h := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
    simp only at h
    omega

lemma mem_markCoords {c : Fin N × ℤ × ℕ} {m : ℕ} {i : Fin N} {x : ℤ} :
    c ∈ markCoords (N := N) m i x ↔ ∃ k ∈ Finset.range (m - 1), c = (i, x, k + 1) := by
  simp only [markCoords, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, hkc⟩
    exact ⟨k, hk, hkc.symm⟩
  · rintro ⟨k, hk, hck⟩
    exact ⟨k, hk, hck.symm⟩

lemma markCoords_disjoint {m : ℕ} {i i' : Fin N} {x x' : ℤ} (h : (i, x) ≠ (i', x')) :
    Disjoint (markCoords (N := N) m i x) (markCoords m i' x') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  rw [mem_markCoords] at hc hc'
  obtain ⟨k, -, rfl⟩ := hc
  obtain ⟨k', -, hk'⟩ := hc'
  simp only [Prod.mk.injEq] at hk'
  refine h ?_
  rw [hk'.1, hk'.2.1]

/-- `SiteMark` is the cylinder set of its own coordinates. -/
lemma siteMark_eq_coordsCyl (m : ℕ) (i : Fin N) (x : ℤ) :
    {U : Array N | SiteMark p m U i x} = coordsCyl p (markCoords m i x) := by
  ext U
  simp only [Set.mem_setOf_eq, coordsCyl]
  constructor
  · intro hU c hc
    rw [mem_markCoords] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact hU (k + 1) (by omega) (by simpa using Finset.mem_range.mp hk)
  · intro hU k hk1 hkm
    exact hU (i, x, k) (by
      rw [mem_markCoords]
      exact ⟨k - 1, Finset.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel hk1]⟩)

/-- Membership in a finite cylinder. -/
lemma mem_coordsCyl_iff (S : Finset (Fin N × ℤ × ℕ)) :
    coordsCyl (N := N) p S = ⋂ c ∈ S, (fun U : Array N => U c) ⁻¹' Set.Ioi p := by
  ext U
  simp only [coordsCyl, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]

/-- Finite cylinders of the uniform array, `Ioi` form. -/
theorem arrayMeasure_coordsCyl (hp0 : 0 < p) (hp1 : p < 1) (S : Finset (Fin N × ℤ × ℕ)) :
    arrayMeasure N (coordsCyl (N := N) p S) = (ENNReal.ofReal (1 - p)) ^ S.card := by
  have h := (array_independent N).measure_inter_preimage_eq_mul (S := S)
    (sets := fun (_ : Fin N × ℤ × ℕ) => Set.Ioi p) (fun _ _ => measurableSet_Ioi)
  rw [mem_coordsCyl_iff, h]
  have hfac : ∀ c : Fin N × ℤ × ℕ,
      arrayMeasure N ((fun U : Array N => U c) ⁻¹' Set.Ioi p)
        = ENNReal.ofReal (1 - p) := by
    intro c
    rw [arrayMeasure_preimage_set N c (Set.Ioi p) measurableSet_Ioi, uniform01_Ioi hp0 hp1]
  rw [Finset.prod_congr rfl (fun c _ => hfac c), Finset.prod_const]

/-- **`P(mark of walker i at site x) = (1-p)^(m-1)`.** -/
theorem arrayMeasure_siteMark (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) (i : Fin N) (x : ℤ) :
    arrayMeasure N {U : Array N | SiteMark p m U i x}
      = (ENNReal.ofReal (1 - p)) ^ (m - 1) := by
  rw [siteMark_eq_coordsCyl, arrayMeasure_coordsCyl hp0 hp1, markCoords_card]

/-- The joint mark event of a finite family of (walker, site) pairs. -/
def familyMark (p : ℝ) (m : ℕ) {ι : Type*} (s : Finset ι) (w : ι → Fin N × ℤ) : Set (Array N) :=
  {U | ∀ a ∈ s, SiteMark p m U (w a).1 (w a).2}

lemma familyMark_eq (m : ℕ) {ι : Type*} (s : Finset ι) (w : ι → Fin N × ℤ) :
    familyMark (N := N) p m s w
      = coordsCyl p (s.biUnion (fun a => markCoords (N := N) m (w a).1 (w a).2)) := by
  ext U
  simp only [familyMark, coordsCyl, Set.mem_setOf_eq]
  constructor
  · intro hU c hc
    obtain ⟨a, ha, hca⟩ := Finset.mem_biUnion.mp hc
    rw [mem_markCoords] at hca
    obtain ⟨k, hk, rfl⟩ := hca
    exact hU a ha (k + 1) (by omega) (by simpa using Finset.mem_range.mp hk)
  · intro hU a ha k hk1 hkm
    refine hU ((w a).1, (w a).2, k) (Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩)
    rw [mem_markCoords]
    exact ⟨k - 1, Finset.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel hk1]⟩

/-- **The joint law of a finite family of marks.**  Distinct sites give independent marks, so a
finite family factorises with the product of `q = (1-p)^(m-1)`. -/
theorem arrayMeasure_marks_family (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {ι : Type*}
    (s : Finset ι) (w : ι → Fin N × ℤ) (hw : ∀ a ∈ s, ∀ b ∈ s, w a = w b → a = b) :
    arrayMeasure N (familyMark (N := N) p m s w)
      = (ENNReal.ofReal (1 - p)) ^ (s.card * (m - 1)) := by
  classical
  rw [familyMark_eq, arrayMeasure_coordsCyl hp0 hp1]
  have hdisj : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      Disjoint (markCoords (N := N) m (w a).1 (w a).2) (markCoords m (w b).1 (w b).2) := by
    intro a ha b hb hab
    exact markCoords_disjoint (i := (w a).1) (x := (w a).2) (i' := (w b).1) (x' := (w b).2)
      (fun hcon => hab (hw a ha b hb hcon))
  rw [Finset.card_biUnion hdisj]
  simp only [markCoords_card]
  rw [Finset.sum_const, smul_eq_mul]

end Swarming.Marks


