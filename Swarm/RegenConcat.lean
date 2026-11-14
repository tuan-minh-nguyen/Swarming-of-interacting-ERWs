/-
# The record-segment concatenation and the paper's regeneration distance

Source: `main_1d_revised.tex`, §3.2 (proof of Proposition `regen`), the paragraph

> "Conditionally on `Y_0`, the future states and segments have the same joint law as the forward
>  evolution from `Y_0`.  We concatenate the future segments, translating the segment at index
>  `k ≥ 0` by `k`, and denote the resulting path by `X`, with coordinates `X_n^i`. …
>  For `k ≥ 1`, on `A`, we have `θ^k ω ∈ A` if and only if `τ_k` is a regeneration time of the
>  concatenated path.  We therefore have `D = inf{k ≥ 1 : θ^k ω ∈ A}` on `A`."

The Kac layer (`Swarm/KacDisjoint.lean`, `KacTransfer.lean`, `KacED.lean`,
`Swarm/KacBridge.lean`) is proved for an *abstract* measure-preserving map `θ`, a set `A`
and the return time `retTime θ A`.  `KacBridge.record_ED_of_invariant_mass` carries the link back
to the paper as the explicit hypothesis

  `hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞)`

i.e. *the abstract return time is the paper's regeneration distance read off the block content*.
No file constructs that link.  This file does, unconditionally and without probability theory:

* `SwarmConcat.Seg` is one record-to-record segment of the record chain at level `k`: its finite
  duration `≥ 1`, the relative position array `p` (position minus level), the record conditions at
  the two ends, the nearest-neighbour jump law, and the first-passage condition "no walker
  reaches the next level before the segment ends";
* `SwarmConcat.Chain` is a level-indexed segment sequence with the boundary compatibility that
  makes the segments the steps of one path;
* `Chain.cum`, `Chain.blk`, `Chain.X` are the cumulative record times, the segment index of a
  time, and the concatenated path `X`, defined exactly as the paper's "translating the segment at
  index `k` by `k`";
* `Chain.X_record`, `Chain.X_cum_add`, `Chain.X_block` identify `X` at and inside every record
  segment; `Chain.X_step` proves the concatenated path is a nearest-neighbour trajectory;
  `Chain.X_le_record` proves that `cum k` is the **first** time any walker reaches level `k`;
* `Chain.regen_iff`: level `k` is a regeneration level of `X` (paper: `X_{τ_k}^i = k` for all `i`
  and `X_n^i > k` for all `n > τ_k`) **iff** the segment sequence from index `k` on sits in the
  paper's event `A` — in the path form or in the block form;
* `Chain.mem_A_iterate_iff`: hence `θ^k ω ∈ A` iff `τ_k` is a regeneration time;
* `Chain.paperD_eq`: hence the paper's `D = inf{k ≥ 1 : θ^k ω ∈ A}` is the first `k` with
  `θ^k ω ∈ A`, which is literally `KacFormula.retTime`.

Nothing here asserts that a regeneration exists, that `A` has positive mass, or that a stationary
segment law exists.  It is the missing semantic link between the Kac/return-time layer and the
path statistic.
-/
import Swarm.KacMP

set_option linter.unusedVariables false

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace SwarmConcat

variable {N : ℕ}

/-! ## 1. Segments and segment sequences -/

/-- One record-to-record step of the stopped record chain, taken at record level `k`.

`p n i` is the position of walker `i` at time `start + n` minus the level `k`; so `p n i = 0`
means "walker `i` is at the record level" and `p n i = 1` means "walker `i` is at level `k+1`",
which is the next record. -/
structure Seg (N : ℕ) where
  /-- duration of the segment (into the next record) -/
  dur : ℕ
  dur_pos : 0 < dur
  /-- relative position array -/
  p : ℕ → Fin N → ℤ
  /-- at the record time every walker is at or below the record level -/
  start_le : ∀ i, p 0 i ≤ 0
  /-- at least one walker is at the record level -/
  start_min : ∃ i, p 0 i = 0
  /-- no walker reaches the next record level before the segment ends -/
  lt_one : ∀ n, n < dur → ∀ i, p n i < 1
  /-- every step is a nearest-neighbour step -/
  step : ∀ n, n < dur → ∀ i, p (n+1) i = p n i + 1 ∨ p (n+1) i = p n i - 1

/-- A record-segment sequence indexed by the record level, with the compatibility that
consecutive segments describe one path: the end of segment `k` and the start of segment `k+1`
are the same configuration, one level apart. -/
structure Chain (N : ℕ) where
  seg : ℕ → Seg N
  compat : ∀ (k : ℕ) (i : Fin N),
    (k : ℤ) + (seg k).p (seg k).dur i = ((k+1 : ℕ) : ℤ) + (seg (k+1)).p 0 i

namespace Chain

variable (c : Chain N)

/-! ## 2. Cumulative record times -/

/-- `cum k` is the time of the record at level `k` — the sum of the durations of the segments
`0, …, k-1`.  This is the paper's `τ_k`. -/
def cum : ℕ → ℕ
  | 0 => 0
  | (k+1) => cum k + (c.seg k).dur

@[simp] theorem cum_zero : c.cum 0 = 0 := rfl

theorem cum_succ (k : ℕ) : c.cum (k+1) = c.cum k + (c.seg k).dur := rfl

theorem cum_lt_succ (k : ℕ) : c.cum k < c.cum (k+1) := by
  rw [cum_succ]; have := (c.seg k).dur_pos; omega

theorem cum_strictMono : StrictMono c.cum := strictMono_nat_of_lt_succ c.cum_lt_succ

theorem le_cum (k : ℕ) : k ≤ c.cum k := by
  induction k with
  | zero => simp
  | succ k ih => rw [cum_succ]; have := (c.seg k).dur_pos; omega

/-- The end of segment `k` is at or below the next record level (derived, not assumed). -/
theorem end_le (k : ℕ) (i : Fin N) : (c.seg k).p (c.seg k).dur i ≤ 1 := by
  have hc := c.compat k i
  have hs := (c.seg (k+1)).start_le i
  have h1 : (k : ℤ) + (c.seg k).p (c.seg k).dur i ≤ (k : ℤ) + 1 := by
    rw [hc]; push_cast; omega
  omega

/-! ## 3. The segment index of a time and the concatenated path -/

theorem exists_cum_gt (n : ℕ) : ∃ k, n < c.cum (k+1) :=
  ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (le_cum c (n+1))⟩

/-- The index of the segment containing time `n`. -/
noncomputable def blk (n : ℕ) : ℕ := Nat.find (exists_cum_gt c n)

theorem blk_spec (n : ℕ) : n < c.cum (c.blk n + 1) := Nat.find_spec (exists_cum_gt c n)

theorem blk_le {n k : ℕ} (h : n < c.cum (k+1)) : c.blk n ≤ k :=
  Nat.find_min' (exists_cum_gt c n) h

theorem cum_blk_le (n : ℕ) : c.cum (c.blk n) ≤ n := by
  rcases Nat.eq_zero_or_pos (c.blk n) with h | h
  · rw [h]; exact Nat.zero_le n
  · obtain ⟨k, hk⟩ : ∃ k, c.blk n = k + 1 := ⟨c.blk n - 1, by omega⟩
    by_contra hcon
    have hlt : n < c.cum (k+1) := by rw [← hk]; omega
    have := c.blk_le hlt
    omega

theorem blk_record (k : ℕ) : c.blk (c.cum k) = k := by
  refine le_antisymm ?_ ?_
  · refine c.blk_le ?_
    rw [cum_succ]; have := (c.seg k).dur_pos; omega
  · by_contra hcon
    push Not at hcon
    have h1 : c.cum k < c.cum (c.blk (c.cum k) + 1) := c.blk_spec (c.cum k)
    have hle := c.le_cum k
    have hle := c.le_cum k
    have h2 : c.cum (c.blk (c.cum k) + 1) ≤ c.cum k :=
      c.cum_strictMono.monotone (by omega)
    omega

/-- The concatenated path: at time `n` in segment `k`, walker `i` is at level `k` plus the
relative position.  This is the paper's "concatenate the future segments, translating the
segment at index `k` by `k`". -/
noncomputable def X (n : ℕ) (i : Fin N) : ℤ :=
  (c.blk n : ℤ) + (c.seg (c.blk n)).p (n - c.cum (c.blk n)) i

/-- Inside a segment, the concatenated path is the segment's relative array plus the level. -/
theorem X_block {n k : ℕ} (h1 : c.cum k ≤ n) (h2 : n < c.cum (k+1)) (i : Fin N) :
    c.X n i = (k : ℤ) + (c.seg k).p (n - c.cum k) i := by
  have hbk : c.blk n = k := by
    refine le_antisymm (c.blk_le h2) ?_
    by_contra hcon
    push Not at hcon
    have hmono : c.cum (c.blk n + 1) ≤ c.cum k := c.cum_strictMono.monotone (by omega)
    have hspec := c.blk_spec n
    omega
  show (c.blk n : ℤ) + (c.seg (c.blk n)).p (n - c.cum (c.blk n)) i = _
  rw [hbk]

/-- **At the record time of level `k`.** -/
theorem X_record (k : ℕ) (i : Fin N) :
    c.X (c.cum k) i = (k : ℤ) + (c.seg k).p 0 i := by
  have h := X_block c (le_refl (c.cum k)) (c.cum_lt_succ k) i
  simpa using h

/-- At the record time of level `k` some walker is exactly at level `k`. -/
theorem X_record_max (k : ℕ) : ∃ i, c.X (c.cum k) i = (k : ℤ) := by
  obtain ⟨i, hi⟩ := (c.seg k).start_min
  exact ⟨i, by rw [X_record, hi]; ring⟩

/-- At the record time of level `k`, every walker is at or below level `k`. -/
theorem X_record_le (k : ℕ) (i : Fin N) : c.X (c.cum k) i ≤ (k : ℤ) := by
  rw [X_record]
  have hs := (c.seg k).start_le i
  omega

/-- `cum (k+1)` is the **first** time any walker reaches level `k+1`. -/
theorem X_le_record {n k : ℕ} (h : n < c.cum (k+1)) (i : Fin N) : c.X n i ≤ (k : ℤ) := by
  have h1 : c.cum (c.blk n) ≤ n := c.cum_blk_le n
  have h2 : n < c.cum (c.blk n + 1) := c.blk_spec n
  have hbk : c.blk n ≤ k := c.blk_le h
  rw [X_block c h1 h2]
  have hmd : n - c.cum (c.blk n) < (c.seg (c.blk n)).dur := by
    have := cum_succ c (c.blk n)
    omega
  have hlt := (c.seg (c.blk n)).lt_one _ hmd i
  have hbkz : ((c.blk n : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hbk
  omega

/-- **Inside a segment, at local time `m`.**  `m` may be `0` (the record itself) or `dur`
(the next record); both boundaries are included, using the compatibility. -/
theorem X_cum_add {j m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ (c.seg j).dur) (i : Fin N) :
    c.X (c.cum j + m) i = (j : ℤ) + (c.seg j).p m i := by
  rcases lt_or_eq_of_le hmd with h | h
  · have h2 : c.cum j + m < c.cum (j+1) := by rw [cum_succ]; omega
    rw [X_block c (Nat.le_add_right _ _) h2, Nat.add_sub_cancel_left]
  · rw [h]
    rw [show c.cum j + (c.seg j).dur = c.cum (j+1) from (cum_succ c j).symm, X_record]
    exact (c.compat j i).symm

/-- The value of `X` at the record time of level `j+1`, in segment `j`'s coordinates. -/
theorem X_cum_succ (j : ℕ) (i : Fin N) :
    c.X (c.cum (j+1)) i = (j : ℤ) + (c.seg j).p (c.seg j).dur i := by
  have h := c.X_cum_add (j := j) (m := (c.seg j).dur)
    (show 1 ≤ (c.seg j).dur from (c.seg j).dur_pos) le_rfl i
  rw [cum_succ]
  exact h

/-- The concatenated path makes nearest-neighbour steps. -/
theorem X_step (n : ℕ) (i : Fin N) :
    c.X (n+1) i = c.X n i + 1 ∨ c.X (n+1) i = c.X n i - 1 := by
  have h1 : c.cum (c.blk n) ≤ n := c.cum_blk_le n
  have h2 : n < c.cum (c.blk n + 1) := c.blk_spec n
  have hmd : n - c.cum (c.blk n) < (c.seg (c.blk n)).dur := by
    have := cum_succ c (c.blk n); omega
  have e1 : c.X n i = (c.blk n : ℤ) + (c.seg (c.blk n)).p (n - c.cum (c.blk n)) i :=
    X_block c h1 h2 i
  by_cases hlast : n + 1 < c.cum (c.blk n + 1)
  · have e2 : c.X (n+1) i =
        (c.blk n : ℤ) + (c.seg (c.blk n)).p (n+1 - c.cum (c.blk n)) i :=
      X_block c (by omega) hlast i
    have he : n + 1 - c.cum (c.blk n) = (n - c.cum (c.blk n)) + 1 := by omega
    rw [e1, e2, he]
    rcases (c.seg (c.blk n)).step (n - c.cum (c.blk n)) hmd i with hs | hs
    · left; rw [hs]; ring
    · right; rw [hs]; ring
  · have hlast' : n + 1 = c.cum (c.blk n + 1) := by omega
    have e2 : c.X (n+1) i =
        ((c.blk n + 1 : ℕ) : ℤ) + (c.seg (c.blk n + 1)).p 0 i := by
      rw [hlast']; exact X_record c (c.blk n + 1) i
    have hmeq : n - c.cum (c.blk n) + 1 = (c.seg (c.blk n)).dur := by
      rw [cum_succ] at hlast'; omega
    have hstep := (c.seg (c.blk n)).step (n - c.cum (c.blk n)) hmd i
    have hstep' : (c.seg (c.blk n)).p (c.seg (c.blk n)).dur i =
          (c.seg (c.blk n)).p (n - c.cum (c.blk n)) i + 1 ∨
        (c.seg (c.blk n)).p (c.seg (c.blk n)).dur i =
          (c.seg (c.blk n)).p (n - c.cum (c.blk n)) i - 1 := by
      rw [← hmeq]; exact hstep
    have hc := c.compat (c.blk n) i
    rw [e1, e2]
    rcases hstep' with hs | hs <;> [left; right]
    · push_cast at hc ⊢; omega
    · push_cast at hc ⊢; omega

/-! ## 4. Regeneration levels of the concatenated path -/

/-- **Block form** of "level `k` is a regeneration level": at the level-`k` record every walker
sits exactly at level `k`, and from then on, in every segment `j ≥ k` and at every positive local
time, every walker is strictly above level `k`. -/
def Regen (k : ℕ) : Prop :=
  (∀ i, (c.seg k).p 0 i = 0) ∧
    ∀ (j : ℕ), k ≤ j → ∀ m : ℕ, 1 ≤ m → m ≤ (c.seg j).dur → ∀ i,
      (k : ℤ) < (j : ℤ) + (c.seg j).p m i

/-- **Path form** of "level `k` is a regeneration level" — the paper's `τ_k` is a regeneration
time: at time `τ_k = cum k` every walker is at level `k`, and at every later time every walker is
strictly above level `k`. -/
def RegenPath (k : ℕ) : Prop :=
  (∀ i, c.X (c.cum k) i = (k : ℤ)) ∧ ∀ n : ℕ, c.cum k < n → ∀ i, (k : ℤ) < c.X n i

/-- **The block and path forms agree.**  This is the content of "no walker returns to or below
level `k` after `τ_k`", read through the concatenation. -/
theorem regen_iff (k : ℕ) : c.Regen k ↔ c.RegenPath k := by
  constructor
  · rintro ⟨h0, hnr⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [X_record, h0 i]; ring
    · intro n hn i
      have h1 : c.cum (c.blk n) ≤ n := c.cum_blk_le n
      have h2 : n < c.cum (c.blk n + 1) := c.blk_spec n
      have hjk : k ≤ c.blk n := by
        by_contra hcon
        push Not at hcon
        have hmono : c.cum (c.blk n + 1) ≤ c.cum k := c.cum_strictMono.monotone (by omega)
        omega
      rcases Nat.eq_zero_or_pos (n - c.cum (c.blk n)) with hm | hm
      · have hnj : n = c.cum (c.blk n) := by omega
        have hk1 : k + 1 ≤ c.blk n := by
          by_contra hcon
          push Not at hcon
          have hmono : c.cum (c.blk n) ≤ c.cum k := c.cum_strictMono.monotone (by omega)
          omega
        obtain ⟨j', hj'⟩ : ∃ j', c.blk n = j' + 1 := ⟨c.blk n - 1, by omega⟩
        have hjk' : k ≤ j' := by omega
        have hd := (c.seg j').dur_pos
        have hX : c.X n i = (j' : ℤ) + (c.seg j').p (c.seg j').dur i := by
          rw [hnj, hj']
          exact X_cum_succ c j' i
        rw [hX]
        exact hnr j' hjk' _ hd le_rfl i
      · have hX : c.X n i = (c.blk n : ℤ) + (c.seg (c.blk n)).p (n - c.cum (c.blk n)) i :=
          X_block c h1 h2 i
        rw [hX]
        exact hnr _ hjk _ hm (by have := cum_succ c (c.blk n); omega) i
  · rintro ⟨h0, hpath⟩
    refine ⟨fun i => ?_, ?_⟩
    · have h := h0 i
      rw [X_record] at h
      omega
    · intro j hj m hm hmd i
      have hle : c.cum k ≤ c.cum j := c.cum_strictMono.monotone hj
      have := hpath (c.cum j + m) (by omega) i
      rwa [X_cum_add c hm hmd i] at this

/-- **`Regen` genuinely excludes returns**: a single visit to level `k` or below at a positive
time of a segment `j ≥ k` refutes regeneration at level `k`.  So `A` is not the whole space, and
the no-return clause is not vacuous. -/
theorem not_regen_of_return {k j m : ℕ} (hjk : k ≤ j) (hm : 1 ≤ m) (hmd : m ≤ (c.seg j).dur)
    (i : Fin N) (hret : (j : ℤ) + (c.seg j).p m i ≤ (k : ℤ)) : ¬ c.Regen k := by
  intro h
  exact absurd (h.2 j hjk m hm hmd i) (not_lt.mpr hret)

/-! ## 5. Shifting the record index: the paper's `θ^k ω ∈ A`

`A` is the index-`0` regeneration event of a segment sequence:
`A = {Y_0 ∈ F, X_n^i > 0 for every i and every n ≥ 1}`.  Advancing to the next record is the
left shift of the segment sequence. -/

/-- The left shift of a segment sequence: drop the level-`0` segment. -/
def shift (c : Chain N) : Chain N where
  seg := fun j => c.seg (j+1)
  compat := fun k i => by
    have h := c.compat (k+1) i
    push_cast at h ⊢
    omega

@[simp] theorem shift_seg (j : ℕ) : c.shift.seg j = c.seg (j+1) := rfl

/-- **The paper's `A`**: at the current record every walker is exactly at the record level, and
afterwards every walker stays strictly above it. -/
def A : Set (Chain N) := {d | d.Regen 0}

theorem mem_A_iff (d : Chain N) : d ∈ A ↔ d.Regen 0 := Iff.rfl

/-- Shifting the record index by one shifts the regeneration level by one. -/
theorem regen_shift (k : ℕ) : c.shift.Regen k ↔ c.Regen (k+1) := by
  unfold Regen
  constructor
  · rintro ⟨h0, hnr⟩
    refine ⟨by simpa using h0, ?_⟩
    intro j hj m hm hmd i
    have hj1 : 1 ≤ j := by omega
    have hjd : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1).symm
    have hmd' : m ≤ (c.shift.seg (j-1)).dur := by
      rw [hjd] at hmd ⊢
      exact hmd
    have h := hnr (j-1) (by omega) m hm hmd' i
    rw [hjd]
    simp only [shift_seg] at h ⊢
    push_cast at h ⊢
    omega
  · rintro ⟨h0, hnr⟩
    refine ⟨by simpa using h0, ?_⟩
    intro j hj m hm hmd i
    have hmd' : m ≤ (c.seg (j+1)).dur := by simpa using hmd
    have h := hnr (j+1) (by omega) m hm hmd' i
    simp only [shift_seg]
    push_cast at h ⊢
    omega

/-- **The paper's "`θ^k ω ∈ A` iff `τ_k` is a regeneration time".** -/
theorem mem_A_iterate_iff (k : ℕ) :
    (fun d : Chain N => d.shift)^[k] c ∈ A ↔ c.Regen k := by
  induction k generalizing c with
  | zero => exact mem_A_iff c
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (c := c.shift), regen_shift c k]

/-- The same statement in the paper's path form. -/
theorem mem_A_iterate_iff_path (k : ℕ) :
    (fun d : Chain N => d.shift)^[k] c ∈ A ↔ c.RegenPath k := by
  rw [mem_A_iterate_iff, regen_iff]

/-- **The paper's `D` is the first positive return time to `A`.** -/
theorem paperD_eq (k : ℕ) (hk : 0 < k) (hreg : c.RegenPath k)
    (hleast : ∀ j, 0 < j → j < k → ¬ c.RegenPath j) :
    KacFormula.retTime (fun d : Chain N => d.shift) A c = (k : ℕ∞) := by
  rw [KacFormula.retTime]
  have hk' : (fun d : Chain N => d.shift)^[k] c ∈ A :=
    (mem_A_iterate_iff c k).mpr ((regen_iff c k).mpr hreg)
  have hex : ∃ j : ℕ, 0 < j ∧ (fun d : Chain N => d.shift)^[j] c ∈ A := ⟨k, hk, hk'⟩
  rw [dif_pos hex]
  have hfind : Nat.find hex = k := by
    refine (Nat.find_eq_iff hex).mpr ⟨⟨hk, hk'⟩, ?_⟩
    intro m hm hmem
    exact hleast m hmem.1 (Nat.lt_of_succ_le hm)
      ((regen_iff c m).mp ((mem_A_iterate_iff c m).mp hmem.2))
  rw [hfind]

/-- The least-element form: if `k` is the least positive regeneration level then the return time
is `k`.  This is the shape required by `KacBridge`'s hypothesis `hD`. -/
theorem retTime_eq_of_isLeast (k : ℕ)
    (his : IsLeast {j : ℕ | 0 < j ∧ c.RegenPath j} k) :
    KacFormula.retTime (fun d : Chain N => d.shift) A c = (k : ℕ∞) := by
  obtain ⟨⟨hk, hreg⟩, hmin⟩ := his
  refine paperD_eq c k hk hreg ?_
  intro j hj hjk hjreg
  have := hmin ⟨hj, hjreg⟩
  omega

end Chain

end SwarmConcat

namespace SwarmConcat

/-! ## 6. `D = ⊤` and non-vacuity of the whole construction -/

namespace Chain

variable (c : Chain N)

/-- The return time is `⊤` exactly when no positive level is a regeneration level. -/
theorem retTime_eq_top_iff :
    KacFormula.retTime (fun d : Chain N => d.shift) A c = ⊤ ↔
      ¬ ∃ k : ℕ, 0 < k ∧ c.RegenPath k := by
  rw [KacFormula.retTime]
  by_cases hex : ∃ j : ℕ, 0 < j ∧ (fun d : Chain N => d.shift)^[j] c ∈ A
  · rw [dif_pos hex]
    constructor
    · intro h
      exact absurd h (by simp)
    · intro h
      exact absurd ⟨Nat.find hex, (Nat.find_spec hex).1,
        (mem_A_iterate_iff_path c (Nat.find hex)).mp (Nat.find_spec hex).2⟩ h
  · rw [dif_neg hex]
    constructor
    · intro _
      rintro ⟨k, hk, hreg⟩
      exact hex ⟨k, hk, (mem_A_iterate_iff_path c k).mpr hreg⟩
    · intro _
      rfl

end Chain

/-! ### The "every walker always steps right" chain

This is the degenerate interacting system in which every walker moves right at every step, written
as a segment sequence.  It shows that `Seg`/`Chain` are inhabited, that the concatenation returns
the actual trajectory `X n = n`, that every level is a regeneration level, and that the abstract
Kac return time then takes the value `1` — i.e. the paper's `D` for this system. -/

/-- The one-step segment in which every walker moves right. -/
def rightSeg (N : ℕ) : Seg (N+1) where
  dur := 1
  dur_pos := Nat.one_pos
  p := fun n _ => (n : ℤ)
  start_le := by intro i; simp
  start_min := ⟨⟨0, Nat.succ_pos N⟩, by simp⟩
  lt_one := by
    intro n hn i
    have h : n = 0 := by omega
    simp [h]
  step := by intro n hn i; left; simp

/-- The always-right chain. -/
def rightChain (N : ℕ) : Chain (N+1) where
  seg := fun _ => rightSeg N
  compat := by
    intro k i
    show (k : ℤ) + ((1 : ℕ) : ℤ) = ((k+1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)
    push_cast
    ring

theorem rightChain_cum (N k : ℕ) : (rightChain N).cum k = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Chain.cum_succ, ih]
    rfl

theorem rightChain_X (N n : ℕ) (i : Fin (N+1)) : (rightChain N).X n i = (n : ℤ) := by
  have hcum : ∀ k, (rightChain N).cum k = k := rightChain_cum N
  have hblk : (rightChain N).blk n = n := by
    have h := Chain.blk_record (rightChain N) n
    rwa [hcum] at h
  show ((rightChain N).blk n : ℤ) + ((rightChain N).seg ((rightChain N).blk n)).p
      (n - (rightChain N).cum ((rightChain N).blk n)) i = (n : ℤ)
  rw [hblk, hcum]
  simp [rightChain, rightSeg]

/-- Every level is a regeneration level of the always-right chain. -/
theorem rightChain_regen (N k : ℕ) : (rightChain N).Regen k := by
  refine ⟨fun i => by simp [rightChain, rightSeg], ?_⟩
  intro j hj m hm hmd i
  show (k : ℤ) < (j : ℤ) + ((rightChain N).seg j).p m i
  simp only [rightChain, rightSeg]
  have hjz : (k : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hmz : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  omega

/-- **The paper's `D` computed on a concrete system.**  Under the segment law of the always-right
chain, the first positive regeneration level is `1`, so the abstract Kac return time to `A` is
`1`. -/
theorem rightChain_retTime (N : ℕ) :
    KacFormula.retTime (fun d : Chain (N+1) => d.shift) Chain.A (rightChain N) = (1 : ℕ∞) := by
  refine Chain.retTime_eq_of_isLeast (rightChain N) 1 ?_
  constructor
  · exact ⟨Nat.one_pos, (Chain.regen_iff (rightChain N) 1).mp (rightChain_regen N 1)⟩
  · rintro j ⟨hj, _⟩
    omega

end SwarmConcat


/-! ## 7. The measurable structure of the segment space and the Kac statements

The paper's Kac step needs the regeneration event `A` to be measurable and the record shift to
preserve the stationary law `P_π`.  Preservation is a genuine hypothesis — it is the paper's
stationarity of the two-sided record law.  Measurability of `A` is elementary, and it is what the
Kac layer consumes, so it is proved here rather than assumed: `Seg` and `Chain` carry the
σ-algebra generated by their coordinate data `(dur, p)` and `seg`, and `A` is a countable boolean
combination of coordinate evaluations. -/

namespace SwarmConcat

instance instMeasurableSpaceSeg (N : ℕ) : MeasurableSpace (Seg N) :=
  MeasurableSpace.comap (fun s : Seg N => (s.dur, s.p)) inferInstance

instance instMeasurableSpaceChain (N : ℕ) : MeasurableSpace (Chain N) :=
  MeasurableSpace.comap (fun c : Chain N => c.seg) inferInstance

theorem measurable_seg_dur {N : ℕ} : Measurable (fun s : Seg N => s.dur) := by
  have h1 : Measurable (fun s : Seg N => (s.dur, s.p)) := measurable_iff_comap_le.mpr le_rfl
  exact measurable_fst.comp h1

theorem measurable_seg_p {N : ℕ} (n : ℕ) (i : Fin N) :
    Measurable (fun s : Seg N => s.p n i) := by
  have h1 : Measurable (fun s : Seg N => (s.dur, s.p)) := measurable_iff_comap_le.mpr le_rfl
  have h2 : Measurable (fun q : ℕ → Fin N → ℤ => q n i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply n)
  exact h2.comp (measurable_snd.comp h1)

theorem measurable_chain_seg {N : ℕ} (j : ℕ) :
    Measurable (fun c : Chain N => c.seg j) := by
  have h1 : Measurable (fun c : Chain N => c.seg) := measurable_iff_comap_le.mpr le_rfl
  exact (measurable_pi_apply j).comp h1

theorem measurable_chain_dur {N : ℕ} (j : ℕ) :
    Measurable (fun c : Chain N => (c.seg j).dur) :=
  measurable_seg_dur.comp (measurable_chain_seg j)

theorem measurable_chain_p {N : ℕ} (j m : ℕ) (i : Fin N) :
    Measurable (fun c : Chain N => (c.seg j).p m i) :=
  (measurable_seg_p m i).comp (measurable_chain_seg j)

namespace Chain

/-- `A` as a countable boolean combination of coordinate evaluations. -/
theorem A_eq_iInter {N : ℕ} :
    (A : Set (Chain N)) =
      {c | ∀ i, (c.seg 0).p 0 i = 0} ∩
        ⋂ (j : ℕ), ⋂ (m : ℕ), ⋂ (i : Fin N),
          ({c | ¬(1 ≤ m ∧ m ≤ (c.seg j).dur)} ∪
            {c | (0 : ℤ) < (j : ℤ) + (c.seg j).p m i}) := by
  ext c
  simp only [A, Regen, mem_inter_iff, mem_setOf_eq, mem_iInter, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun j m i => ?_⟩
    by_cases hm : 1 ≤ m ∧ m ≤ (c.seg j).dur
    · exact Or.inr (h1 j (Nat.zero_le j) m hm.1 hm.2 i)
    · exact Or.inl hm
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun j _ m hm hmd i => ?_⟩
    rcases h1 j m i with h | h
    · exact absurd ⟨hm, hmd⟩ h
    · exact h

/-- **The paper's regeneration event `A` is measurable.** -/
theorem measurableSet_A {N : ℕ} : MeasurableSet (A : Set (Chain N)) := by
  rw [A_eq_iInter]
  refine MeasurableSet.inter ?_ ?_
  · have hset : {c : Chain N | ∀ i, (c.seg 0).p 0 i = 0}
        = ⋂ i, (fun c : Chain N => (c.seg 0).p 0 i) ⁻¹' {0} := by
      ext c
      simp
    rw [hset]
    exact MeasurableSet.iInter fun i =>
      MeasurableSet.preimage (measurableSet_singleton (0 : ℤ)) (measurable_chain_p 0 0 i)
  · refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun m =>
      MeasurableSet.iInter fun i => MeasurableSet.union ?_ ?_
    · by_cases hm : 1 ≤ m
      · have hset : {c : Chain N | ¬(1 ≤ m ∧ m ≤ (c.seg j).dur)}
            = (fun c : Chain N => (c.seg j).dur) ⁻¹' (Set.Ici m)ᶜ := by
          ext c
          simp [hm]
        rw [hset]
        exact MeasurableSet.preimage measurableSet_Ici.compl (measurable_chain_dur j)
      · have hset : {c : Chain N | ¬(1 ≤ m ∧ m ≤ (c.seg j).dur)} = univ := by
          ext c
          simp [hm]
        rw [hset]
        exact MeasurableSet.univ
    · exact MeasurableSet.preimage measurableSet_Ioi
        ((measurable_chain_p j m i).const_add (j : ℤ))

/-- The record shift is measurable for the coordinate σ-algebra. -/
theorem measurable_shift {N : ℕ} : Measurable (fun c : Chain N => c.shift) := by
  rw [measurable_iff_comap_le]
  have hcomp : MeasurableSpace.comap (fun c : Chain N => c.shift)
        (inferInstance : MeasurableSpace (Chain N))
      = MeasurableSpace.comap (fun c : Chain N => fun j => c.seg (j+1))
        (inferInstance : MeasurableSpace (ℕ → Seg N)) := by
    rw [show (inferInstance : MeasurableSpace (Chain N))
        = MeasurableSpace.comap (fun c : Chain N => c.seg)
          (inferInstance : MeasurableSpace (ℕ → Seg N)) from rfl]
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [hcomp]
  exact Measurable.comap_le (measurable_pi_iff.mpr fun j => measurable_chain_seg (j+1))

end Chain

/-! ### The paper's Kac displays for the concrete regeneration event -/

/-- **The paper's `Σ_k P_π(A ∩ {D > k}) ≤ 1`** for the concrete regeneration event `A` and the
record shift, from stationarity of the segment law alone. -/
theorem kac_tsum_regeneration {N : ℕ} (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    (∑' k : ℕ, μ (Chain.A ∩ KacFormula.noReturn (fun c : Chain N => c.shift) Chain.A k)) ≤ 1 :=
  SwarmKacMP.kac_mp_tsum_le_one hmp Chain.A Chain.measurableSet_A

/-- **The paper's `∫_A D dP_π ≤ 1`**, where `D` is the return time to the concrete regeneration
event `A` — the paper's regeneration distance by `Chain.paperD_eq`. -/
theorem kac_lintegral_regeneration {N : ℕ} (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    ∫⁻ c in Chain.A,
      (KacFormula.retTime (fun c : Chain N => c.shift) Chain.A c : ℝ≥0∞) ∂μ ≤ 1 :=
  SwarmKacMP.kac_mp_lintegral_le_one hmp Chain.A Chain.measurableSet_A

/-- **Poincaré recurrence on `A`**: the regeneration distance is almost surely finite under
`P_π(· | A)`. -/
theorem ae_regeneration_distance_lt_top {N : ℕ} (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    ∀ᵐ c ∂(μ.restrict Chain.A),
      (KacFormula.retTime (fun c : Chain N => c.shift) Chain.A c : ℝ≥0∞) < ⊤ :=
  SwarmKacMP.kac_mp_ae_retTime_lt_top hmp Chain.A Chain.measurableSet_A

/-- The real-valued form `∫_A D dP_π ≤ 1`. -/
theorem kac_integral_regeneration {N : ℕ} (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    ∫ c in Chain.A,
      (KacFormula.retTime (fun c : Chain N => c.shift) Chain.A c : ℝ≥0∞).toReal ∂μ ≤ 1 :=
  SwarmKacMP.kac_mp_integral_toReal_le_one hmp Chain.A Chain.measurableSet_A

/-- **The paper's `E^*D ≤ 1/P_π(A)`** under the conditioned law `P_π(· | A)`, for the concrete
regeneration event `A` and the return time that `Chain.paperD_eq` identifies with the paper's
regeneration distance `D`. -/
theorem cond_mean_regeneration {N : ℕ} (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    ∫⁻ c, (KacFormula.retTime (fun c : Chain N => c.shift) Chain.A c : ℝ≥0∞)
        ∂((μ Chain.A)⁻¹ • μ.restrict Chain.A) ≤ (μ Chain.A)⁻¹ :=
  SwarmKacMP.kac_mp_cond_mean_le hmp Chain.A Chain.measurableSet_A

/-- **The paper's displayed bound `E^*D ≤ 1/(π(F)·P(V))`**, with the mass identity
`P_π(A) = π(F)·P(V)` supplied as `hmass` — the identity that `areas/kac/StationaryMass.lean`
derives from state-independence of the fresh future law.  This file does not reprove the mass
identity; it proves that, once it holds, the paper's numeric bound follows for the concrete `D`. -/
theorem cond_mean_regeneration_of_mass {N : ℕ} (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) (pf pv : ℝ≥0∞)
    (hmass : μ Chain.A = pf * pv) :
    ∫⁻ c, (KacFormula.retTime (fun c : Chain N => c.shift) Chain.A c : ℝ≥0∞)
        ∂((μ Chain.A)⁻¹ • μ.restrict Chain.A) ≤ (pf * pv)⁻¹ := by
  rw [← hmass]
  exact cond_mean_regeneration μ hmp

end SwarmConcat
