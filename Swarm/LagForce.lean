/-
# What the halving clause *forces*: two-sided record speed and the left-step ledger

The integrated tightness tree reduces the paper's block estimate to two clauses on the defect /
record-time sequence: `(time)` `τ (r+BL) ≤ τ r + T L` and `(half)` `2 d_{r+BL} ≤ L`
(`HblkTwo.BadTime`, `HblkTwo.BadHalf`).  Both are *upper* bounds on how badly the record can
behave.  This file proves the missing *lower* constraint and the exact bookkeeping behind it.

## 1. The halving clause forces the record to be slower than the bare minimum

`record_increment_lower`: on `{d r ≤ L}`, the halving `2 d_{r+BL} ≤ L` implies

   `2 (τ (r+BL) - τ r) + L ≥ 2 B L + 2 d r`,

i.e. `τ (r+BL) - τ r ≥ B L + d r - L/2`.  The bare geometric lower bound is `B L` (the record
level cannot advance by more than one per step).  So the good block event is contained in the
*interval*

   `B L + d r - L/2 ≤ τ (r+BL) - τ r ≤ T L`,

and on `{d r > L/2}` the record must be strictly slower than `B L`.  In particular no argument
deducing `(half)` from an upper bound on the record increment can work, and a proof of `(half)`
must exclude the "fast record" configurations — which the paper's `(time)` clause does not.
`witness_offset` shows the constraint is attained exactly: the constant-offset family
`X⁰ n = n`, `X¹ n = n - L` has `d r = L` and `τ (r+BL) - τ r = B L` at every level, so `(time)`
and `(diam)` hold while `(half)` fails and *no* good fluid time (`FluidBlock.GoodTime`) exists.

## 2. The failure is carried by the left steps of the bottom walker

`left_gt_of_half_fail`: if the halving fails, then the walker that is lowest at time
`τ (r+BL)` has made more than `(T' - B L - L/2)/2` *left* steps during the block, where
`T' = τ (r+BL) - τ r`.  The proof is the exact displacement identity
`X i e - X i s = #right - #left` (`displacement_eq`) together with `X i (τ r) ≥ r - L`.

This is where the interaction has to enter: a left step happens with conditional probability at
most `1/2`, and the residual stochastic input for `(half)` is therefore a per-walker left-step
(fair-coin) tail over the adaptive window — not a coalescence statement about the pack.

## 3. A sufficient criterion without the fluid compactness step

`quarterGood_goodTime`: `{d r ≤ L} ∧ (time) ∧ 4 d_{r+BL} ≤ L` already produces a
`FluidBlock.GoodTime` (take `n = τ (r+BL)`), hence (with the proved transfers) neither `BadTime`
nor `BadHalf`.  So the paper's coalescence clause costs only a factor `2` in the halving
constant; the residual target is exactly a two-clause defect-sequence tail.
`record_tightness_of_quarterHalf` transfers this to the canonical stopped-record path law through
`FluidWiring.record_tightness_of_goodTime`.

No `sorry`, no custom axiom, no probability beyond `measure_mono`; no statement about
`MainClaim`, ballisticity or regeneration.
-/
import Swarm.FluidWiring

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

namespace LagForce

open RecordDefect RecordoSupply SwarmM4C.LawBridge HblkTwo HblkFinal FluidBlock
  SwarmRecordMeas SwarmRecordMeas.Actual FluidWiring

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-! ## 0. A unit step is a right step or a left step -/

theorem step_cases {a b : ℤ} (h : |a - b| = 1) : a = b + 1 ∨ a = b - 1 := by
  have h1 : a - b ≤ 1 := (abs_le.1 (le_of_eq h)).2
  have h2 : -1 ≤ a - b := (abs_le.1 (le_of_eq h)).1
  have h0 : a - b ≠ 0 := by
    intro hc
    rw [hc, abs_zero] at h
    exact zero_ne_one h
  omega

/-! ## 1. The step ledger of a single unit-step walker -/

/-- Number of *right* steps of walker `i` at times `< e` that are `≥ s`. -/
def rCount (X : ι → ℕ → ℤ) (i : ι) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => rCount X i s n + (if s ≤ n ∧ X i (n + 1) = X i n + 1 then 1 else 0)

/-- Number of *left* steps of walker `i` at times `< e` that are `≥ s`. -/
def lCount (X : ι → ℕ → ℤ) (i : ι) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => lCount X i s n + (if s ≤ n ∧ X i (n + 1) = X i n - 1 then 1 else 0)

/-- Below the window the ledger is empty. -/
theorem rCount_of_le {X : ι → ℕ → ℤ} {i : ι} {s : ℕ} :
    ∀ {e : ℕ}, e ≤ s → rCount X i s e = 0
  | 0, _ => rfl
  | (n + 1), h => by
      have hn : n ≤ s := le_trans (Nat.le_succ n) h
      have hnot : ¬ s ≤ n := not_le.2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h)
      simp only [rCount, rCount_of_le hn]
      simp [hnot]

theorem lCount_of_le {X : ι → ℕ → ℤ} {i : ι} {s : ℕ} :
    ∀ {e : ℕ}, e ≤ s → lCount X i s e = 0
  | 0, _ => rfl
  | (n + 1), h => by
      have hn : n ≤ s := le_trans (Nat.le_succ n) h
      have hnot : ¬ s ≤ n := not_le.2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h)
      simp only [lCount, lCount_of_le hn]
      simp [hnot]

/-- **The ledger identity**: over a unit-step window the two counts exhaust the window. -/
theorem rCount_add_lCount (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (i : ι)
    {s e : ℕ} (hse : s ≤ e) : rCount X i s e + lCount X i s e = e - s := by
  induction e with
  | zero =>
      have hs0 : s = 0 := Nat.le_zero.mp hse
      subst hs0
      simp [rCount, lCount]
  | succ k ih =>
      rcases Nat.lt_or_ge s (k + 1) with hlt | hge
      · have hsk : s ≤ k := by omega
        have ihk := ih hsk
        rcases step_cases (hne i k) with hc | hc
        · have h1 : (if s ≤ k ∧ X i (k + 1) = X i k + 1 then 1 else 0) = 1 := by
            simp [hsk, hc]
          have h2 : (if s ≤ k ∧ X i (k + 1) = X i k - 1 then 1 else 0) = 0 := by
            have hnn : ¬ (X i (k + 1) = X i k - 1) := by omega
            simp [hsk, hnn]
          rw [rCount, lCount, h1, h2]
          omega
        · have h1 : (if s ≤ k ∧ X i (k + 1) = X i k + 1 then 1 else 0) = 0 := by
            have hnn : ¬ (X i (k + 1) = X i k + 1) := by omega
            simp [hsk, hnn]
          have h2 : (if s ≤ k ∧ X i (k + 1) = X i k - 1 then 1 else 0) = 1 := by
            simp [hsk, hc]
          rw [rCount, lCount, h1, h2]
          omega
      · have hsk : s = k + 1 := by omega
        have h1 : rCount X i s (k + 1) = 0 := rCount_of_le (by omega)
        have h2 : lCount X i s (k + 1) = 0 := lCount_of_le (by omega)
        rw [h1, h2]
        omega

/-- **The displacement identity**: the net displacement of a unit-step walker over a window is
`#right - #left`. -/
theorem displacement_eq (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (i : ι)
    {s e : ℕ} (hse : s ≤ e) :
    X i e - X i s = ((rCount X i s e : ℕ) : ℤ) - ((lCount X i s e : ℕ) : ℤ) := by
  induction e with
  | zero =>
      have hs0 : s = 0 := Nat.le_zero.mp hse
      subst hs0
      simp [rCount, lCount]
  | succ k ih =>
      rcases Nat.lt_or_ge s (k + 1) with hlt | hge
      · have hsk : s ≤ k := by omega
        have ihk := ih hsk
        rcases step_cases (hne i k) with hc | hc
        · have h1 : (if s ≤ k ∧ X i (k + 1) = X i k + 1 then 1 else 0) = 1 := by
            simp [hsk, hc]
          have h2 : (if s ≤ k ∧ X i (k + 1) = X i k - 1 then 1 else 0) = 0 := by
            have hnn : ¬ (X i (k + 1) = X i k - 1) := by omega
            simp [hsk, hnn]
          rw [rCount, lCount, h1, h2]
          push_cast
          rw [hc]
          linarith
        · have h1 : (if s ≤ k ∧ X i (k + 1) = X i k + 1 then 1 else 0) = 0 := by
            have hnn : ¬ (X i (k + 1) = X i k + 1) := by omega
            simp [hsk, hnn]
          have h2 : (if s ≤ k ∧ X i (k + 1) = X i k - 1 then 1 else 0) = 1 := by
            simp [hsk, hc]
          rw [rCount, lCount, h1, h2]
          push_cast
          rw [hc]
          linarith
      · have hsk : s = k + 1 := by omega
        subst hsk
        have h1 : rCount X i (k + 1) (k + 1) = 0 := rCount_of_le le_rfl
        have h2 : lCount X i (k + 1) (k + 1) = 0 := lCount_of_le le_rfl
        rw [h1, h2]
        simp

/-! ## 2. The halving clause forces the record to be slower than `B L` -/

/-- **The halving clause forces a lower bound on the record increment.**

On `{d r ≤ L}`-style data (the defect at `r` enters explicitly), `2 d_{r+BL} ≤ L` implies

  `τ (r+BL) - τ r ≥ B L + d r - L/2`,

i.e. twice the record increment plus `L` dominates `2 B L + 2 d r`.

The proof: let `i` sit at the minimum at time `τ r`, so `X i (τ r) = r - d r`.  The halving puts
`i` at or above the level `r + B L - L/2` at time `τ (r+BL)`, and a unit-step walker gains at most
one unit per step, so the elapsed time pays for the level gain `B L` plus the deficit `d r` minus
`L/2` that the halving itself allows. -/
theorem record_increment_lower (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r B L : ℕ} (hhalf : 2 * defect X τ (r + B * L) ≤ (L : ℤ)) :
    2 * ((τ (r + B * L) : ℤ) - (τ r : ℤ)) + (L : ℤ)
      ≥ 2 * ((B * L : ℕ) : ℤ) + 2 * defect X τ r := by
  obtain ⟨i, -, hival⟩ :
      ∃ a ∈ (Finset.univ : Finset ι), runMin X (τ r) = X a (τ r) :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty (fun i => X i (τ r))
  have hdefr : defect X τ r = (r : ℤ) - X i (τ r) := by
    rw [defect, hival]
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have hgain := step_le_add (X := X) hne i hmono
  have hminle : runMin X (τ (r + B * L)) ≤ X i (τ (r + B * L)) := runMin_le _ _
  have hhalf' : 2 * (((r + B * L : ℕ) : ℤ) - runMin X (τ (r + B * L))) ≤ (L : ℤ) := by
    rw [defect] at hhalf
    exact hhalf
  have hcast : (((τ (r + B * L) - τ r : ℕ)) : ℤ) = (τ (r + B * L) : ℤ) - (τ r : ℤ) := by
    push_cast [hmono]; ring
  have hcastB : (((r + B * L : ℕ)) : ℤ) - ((r : ℕ) : ℤ) = ((B * L : ℕ) : ℤ) := by
    push_cast; ring
  linarith

/-! ## 3. The halving failure is carried by the left steps of the bottom walker -/

/-- **A laggard must have walked left.**  If the halving fails at `r + B L` and `i` is a lowest
walker there, then over the block `[τ r, τ (r+BL))` walker `i` makes more than
`(T' - B L - L/2)/2` left steps, `T'` being the record increment.

Equivalently: `4 · #left + 2 B L + L > 2 T'`. -/
theorem left_gt_of_half_fail (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r B L : ℕ} (hbase : defect X τ r ≤ (L : ℤ))
    {i : ι} (hmin : X i (τ (r + B * L)) = runMin X (τ (r + B * L)))
    (hbad : (L : ℤ) < 2 * defect X τ (r + B * L)) :
    4 * ((lCount X i (τ r) (τ (r + B * L)) : ℕ) : ℤ) + 2 * ((B * L : ℕ) : ℤ) + (L : ℤ)
      > 2 * ((τ (r + B * L) : ℤ) - (τ r : ℤ)) := by
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have hdisp := displacement_eq (X := X) hne i hmono
  have hledger := rCount_add_lCount (X := X) hne i hmono
  -- the bottom walker at time `τ r` is at least `r - L`
  have hXs : (r : ℤ) - (L : ℤ) ≤ X i (τ r) := by
    have hd : defect X τ r = (r : ℤ) - runMin X (τ r) := rfl
    have hle : runMin X (τ r) ≤ X i (τ r) := runMin_le _ _
    linarith
  -- the halving failure puts it below `r + B L - L/2`
  have hXe : 2 * X i (τ (r + B * L)) < 2 * (((r + B * L : ℕ)) : ℤ) - (L : ℤ) := by
    have hd : defect X τ (r + B * L)
        = (((r + B * L : ℕ)) : ℤ) - runMin X (τ (r + B * L)) := rfl
    rw [← hmin] at hd
    linarith
  have hcast : (((τ (r + B * L) - τ r : ℕ)) : ℤ) = (τ (r + B * L) : ℤ) - (τ r : ℤ) :=
    Nat.cast_sub hmono
  have hcastB : (((r + B * L : ℕ)) : ℤ) - ((r : ℕ) : ℤ) = ((B * L : ℕ) : ℤ) := by
    push_cast; ring
  have hledger' : ((rCount X i (τ r) (τ (r + B * L)) : ℕ) : ℤ)
      = ((τ (r + B * L) : ℤ) - (τ r : ℤ))
        - ((lCount X i (τ r) (τ (r + B * L)) : ℕ) : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hledger
    push_cast at h
    rw [hcast] at h
    linarith
  linarith

/-! ## 4. The constant-offset witness: the geometry does not imply the halving -/

/-- Walker `false` is the constant-offset laggard `n ↦ n - L`; walker `true` is `n ↦ n`. -/
def Xoff (L : ℕ) : Bool → ℕ → ℤ := fun i n => (n : ℤ) + (if i then 0 else -(L : ℤ))

theorem Xoff_runMax (L n : ℕ) : runMax (Xoff L) n = (n : ℤ) := by
  refine le_antisymm (Finset.sup'_le _ _ ?_) ?_
  · intro i _
    cases i with
    | false => simp only [Xoff, Bool.false_eq_true, if_false]; linarith
    | true => simp only [Xoff, if_true]; linarith
  · have h := le_runMax (X := Xoff L) n true
    simpa [Xoff] using h

theorem Xoff_runMin (L n : ℕ) : runMin (Xoff L) n = (n : ℤ) - (L : ℤ) := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ ?_)
  · have h := runMin_le (X := Xoff L) n false
    simp only [Xoff, Bool.false_eq_true, if_false] at h
    linarith
  · intro i _
    cases i with
    | false => simp only [Xoff, Bool.false_eq_true, if_false]; linarith
    | true => simp only [Xoff, if_true]; linarith

theorem Xoff_isRecord (L : ℕ) : IsRecord (Xoff L) id := by
  intro r
  constructor
  · intro n hn
    rw [Xoff_runMax]
    exact_mod_cast hn
  · show runMax (Xoff L) r = (r : ℤ)
    rw [Xoff_runMax]

theorem Xoff_step (L : ℕ) (i : Bool) (n : ℕ) : |Xoff L i (n + 1) - Xoff L i n| = 1 := by
  have h : Xoff L i (n + 1) - Xoff L i n = 1 := by
    cases i <;> simp only [Xoff, Bool.false_eq_true, if_false, if_true] <;> push_cast <;> ring
  rw [h]
  norm_num

theorem Xoff_defect (L r : ℕ) : defect (Xoff L) id r = (L : ℤ) := by
  show ((r : ℕ) : ℤ) - runMin (Xoff L) r = (L : ℤ)
  rw [Xoff_runMin]
  ring

/-- **Sharpness of the record-speed constraint.**  For the constant-offset family the block data at
*every* level is: `d r = L ≤ L`, the record increment is the minimal `B L` (so `(time)` holds for
any `T ≥ B`), and `(diam)` holds — yet the halving fails, `BadHalf` holds, and no single good fluid
time exists.  Hence neither `(half)` nor the `GoodTime` criterion follows from the geometry or from
`(time)`; both need the interaction. -/
theorem witness_offset (B T L r : ℕ) (hL : 1 ≤ L) (hBT : B ≤ T) :
    defect (Xoff L) id r ≤ (L : ℤ) ∧
      (id (r + B * L) - id r ≤ T * L) ∧
      ¬ (2 * defect (Xoff L) id (r + B * L) ≤ (L : ℤ)) ∧
      ¬ (∃ n, GoodTime (Xoff L) id B T r L n) ∧
      BadHalf B (fun u => (defect (Xoff L) id u).toNat, id) r L ∧
      ¬ BadTime B T (fun u => (defect (Xoff L) id u).toNat, id) r L := by
  have hd : defect (Xoff L) id r = (L : ℤ) := Xoff_defect L r
  have hnat : ∀ u : ℕ, (defect (Xoff L) id u).toNat = L := by
    intro u
    rw [Xoff_defect]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
  · show r + B * L - r ≤ T * L
    rw [Nat.add_sub_cancel_left]
    exact Nat.mul_le_mul_right L hBT
  · rw [Xoff_defect]
    omega
  · rintro ⟨n, hn⟩
    have h4 : 4 * e (Xoff L) n ≤ (L : ℤ) := hn.2.2.2.1
    have hge : (L : ℤ) ≤ e (Xoff L) n := by
      have h1 : runMax (Xoff L) n ≤ rho (Xoff L) n := le_rho _ le_rfl
      rw [Xoff_runMax] at h1
      have h2 : runMin (Xoff L) n = (n : ℤ) - (L : ℤ) := Xoff_runMin L n
      simp only [e]
      linarith
    omega
  · refine ⟨?_, ?_⟩
    · change (defect (Xoff L) id r).toNat ≤ L
      rw [hnat]
    · change L / 2 < (defect (Xoff L) id (r + B * L)).toNat
      rw [hnat]
      omega
  · rintro ⟨-, hlt⟩
    simp only [id] at hlt
    have h : T * L < B * L := by omega
    have : T < B := by
      rcases Nat.lt_or_ge T B with h' | h'
      · exact h'
      · exact absurd (Nat.mul_le_mul_right L h') (not_le.2 h)
    omega

/-! ## 4b. A faithful witness: nonnegative leader, common start at `0`, unit steps -/

/-- The "V-shaped laggard": walker `true` is the leader `n ↦ n`; walker `false` walks left for
`L/2` steps and then right forever, so for even `L` it is exactly `L` behind at every time
`n ≥ L`.  Both walkers start at `0` and every step is a unit step. -/


def Xv (L : ℕ) : Bool → ℕ → ℤ := fun i n =>
  if i then (n : ℤ) else if n ≤ L / 2 then -(n : ℤ) else (n : ℤ) - (L : ℤ)

theorem Xv_zero (L : ℕ) (i : Bool) : Xv L i 0 = 0 := by
  cases i with
  | true => rfl
  | false => simp [Xv]

theorem Xv_step (L : ℕ) (hL : L % 2 = 0) (i : Bool) (n : ℕ) :
    |Xv L i (n + 1) - Xv L i n| = 1 := by
  have hL2 : L = 2 * (L / 2) := by omega
  cases i with
  | true =>
      have h : Xv L true (n + 1) - Xv L true n = 1 := by
        simp only [Xv, if_true]; push_cast; ring
      rw [h]; exact abs_one
  | false =>
      simp only [Xv, Bool.false_eq_true, if_false]
      rcases lt_or_ge n (L / 2) with hn | hn
      · rw [if_pos (by omega : n ≤ L / 2), if_pos (by omega : n + 1 ≤ L / 2)]
        have h : (-(((n + 1 : ℕ)) : ℤ)) - (-((n : ℕ) : ℤ)) = -1 := by push_cast; ring
        rw [h]; norm_num
      · rcases eq_or_lt_of_le hn with heq | hgt
        · subst heq
          rw [if_pos (le_refl (L / 2)), if_neg (by omega : ¬ L / 2 + 1 ≤ L / 2)]
          have hL2' : ((L : ℤ)) = 2 * (((L / 2 : ℕ)) : ℤ) := by
            have hh : ((L : ℕ) : ℤ) = ((2 * (L / 2) : ℕ) : ℤ) := by
              conv_lhs => rw [hL2]
            rw [hh, Nat.cast_mul]
            norm_num
          have h : (((L / 2 + 1 : ℕ)) : ℤ) - (L : ℤ) - (-(((L / 2 : ℕ)) : ℤ)) = 1 := by
            push_cast
            linarith
          rw [h]; norm_num
        · rw [if_neg (by omega : ¬ n ≤ L / 2), if_neg (by omega : ¬ n + 1 ≤ L / 2)]
          have h : (((n + 1 : ℕ)) : ℤ) - (L : ℤ) - ((((n : ℕ)) : ℤ) - (L : ℤ)) = 1 := by
            push_cast; ring
          rw [h]; norm_num

theorem Xv_runMax (L n : ℕ) : runMax (Xv L) n = (n : ℤ) := by
  refine le_antisymm (Finset.sup'_le _ _ ?_) ?_
  · intro i _
    cases i with
    | true => simp [Xv]
    | false =>
        simp only [Xv, Bool.false_eq_true, if_false]
        split_ifs with h
        · linarith [Nat.cast_nonneg (α := ℤ) n]
        · linarith [Nat.cast_nonneg (α := ℤ) L]
  · have h := le_runMax (X := Xv L) n true
    simpa [Xv] using h

theorem Xv_isRecord (L : ℕ) : IsRecord (Xv L) id := by
  intro r
  constructor
  · intro n hn
    rw [Xv_runMax]
    exact_mod_cast hn
  · show runMax (Xv L) r = (r : ℤ)
    rw [Xv_runMax]

theorem Xv_runMin (L n : ℕ) (hLpos : 0 < L) (hLn : L ≤ n) :
    runMin (Xv L) n = (n : ℤ) - (L : ℤ) := by
  have hhalf : L / 2 < L := Nat.div_lt_self hLpos (by norm_num)
  have hval : Xv L false n = (n : ℤ) - (L : ℤ) := by
    simp only [Xv, Bool.false_eq_true, if_false]
    rw [if_neg (by omega : ¬ n ≤ L / 2)]
  refine le_antisymm ?_ (Finset.le_inf' _ _ ?_)
  · have h := runMin_le (X := Xv L) n false
    linarith
  · intro i _
    cases i with
    | true => simp only [Xv, if_true]; linarith
    | false => linarith

theorem Xv_rho_le (L n : ℕ) : rho (Xv L) n ≤ (n : ℤ) := by
  induction n with
  | zero => rw [rho_zero, Xv_runMax]
  | succ k ih =>
      rw [rho_succ, Xv_runMax]
      refine max_le (le_trans ih ?_) le_rfl
      push_cast
      omega

theorem Xv_defect (L n : ℕ) (hLpos : 0 < L) (hLn : L ≤ n) : defect (Xv L) id n = (L : ℤ) := by
  show (n : ℤ) - runMin (Xv L) n = (L : ℤ)
  rw [Xv_runMin L n hLpos hLn]; ring


theorem witness_offset_faithful (B T L r : ℕ) (hL2 : 2 ≤ L) (hLeven : L % 2 = 0) (hLr : L ≤ r)
    (hBT : B ≤ T) :
    (∀ i, Xv L i 0 = 0) ∧
      (∀ i n, |Xv L i (n + 1) - Xv L i n| = 1) ∧
      (∀ n, 0 ≤ Xv L true n ∧ -(L : ℤ) ≤ Xv L false n) ∧
      defect (Xv L) id r ≤ (L : ℤ) ∧
      (id (r + B * L) - id r ≤ T * L) ∧
      ¬ (2 * defect (Xv L) id (r + B * L) ≤ (L : ℤ)) ∧
      ¬ (∃ n, GoodTime (Xv L) id B T r L n) ∧
      BadHalf B (fun u => (defect (Xv L) id u).toNat, id) r L ∧
      ¬ BadTime B T (fun u => (defect (Xv L) id u).toNat, id) r L := by
  have hLpos : 0 < L := by omega
  have hd : defect (Xv L) id r = (L : ℤ) := Xv_defect L r hLpos hLr
  have hdr' : L ≤ r + B * L := by omega
  have hdB : defect (Xv L) id (r + B * L) = (L : ℤ) := Xv_defect L (r + B * L) hLpos hdr'
  have hnat : ∀ u : ℕ, L ≤ u → (defect (Xv L) id u).toNat = L := by
    intro u hu
    rw [Xv_defect L u hLpos hu]
    simp
  refine ⟨Xv_zero L, fun i n => Xv_step L hLeven i n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simp only [Xv, if_true]; exact_mod_cast Nat.zero_le n
    · simp only [Xv, Bool.false_eq_true, if_false]
      split_ifs with h
      · have h1 : n ≤ L := by omega
        have h2 : ((n : ℤ)) ≤ (L : ℤ) := by exact_mod_cast h1
        linarith
      · have : ((n : ℤ)) - (L : ℤ) ≥ -((L : ℤ)) := by linarith [Nat.cast_nonneg (α := ℤ) n]
        linarith
  · rw [hd]
  · show r + B * L - r ≤ T * L
    rw [Nat.add_sub_cancel_left]
    exact Nat.mul_le_mul_right L hBT
  · rw [hdB]; omega
  · rintro ⟨n, hn⟩
    have h4 : 4 * e (Xv L) n ≤ (L : ℤ) := hn.2.2.2.1
    have hadv : (((r + B * L : ℕ)) : ℤ) ≤ rho (Xv L) n := hn.2.2.1
    have hle := Xv_rho_le L n
    have hnL : L ≤ n := by
      have h2 : ((r + B * L : ℕ) : ℤ) ≤ (n : ℤ) := le_trans hadv hle
      have h3 : (L : ℤ) ≤ ((n : ℤ)) := by
        have h4 : (L : ℤ) ≤ ((r + B * L : ℕ) : ℤ) := by
          exact_mod_cast (by omega : L ≤ r + B * L)
        linarith
      exact_mod_cast h3
    have hge : (L : ℤ) ≤ e (Xv L) n := by
      have h1 : runMax (Xv L) n ≤ rho (Xv L) n := le_rho _ le_rfl
      rw [Xv_runMax] at h1
      have h2 := Xv_runMin L n hLpos hnL
      simp only [e]
      linarith
    omega
  · refine ⟨?_, ?_⟩
    · change (defect (Xv L) id r).toNat ≤ L
      rw [hnat r hLr]
    · change L / 2 < (defect (Xv L) id (r + B * L)).toNat
      rw [hnat (r + B * L) hdr']
      omega
  · rintro ⟨-, hlt⟩
    simp only [id] at hlt
    have h : T * L < B * L := by omega
    have hTB : T < B := by
      rcases Nat.lt_or_ge T B with h' | h'
      · exact h'
      · exact absurd (Nat.mul_le_mul_right L h') (not_le.2 h)
    omega


/-! ## 5. A sufficient criterion that avoids the fluid compactness step -/

/-- The defect-sequence event "the block closes with a quarter of the window to spare". -/
def QuarterGood (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (B T r L : ℕ) : Prop :=
  defect X τ r ≤ (L : ℤ) ∧ τ (r + B * L) - τ r ≤ T * L ∧
    4 * defect X τ (r + B * L) ≤ (L : ℤ)

/-- **`QuarterGood` produces a good fluid time**: take `n = τ (r + B L)`.  The record level held at
that time is exactly `r + B L`, the spread below it is the defect, and the record time of level
`r + B L` has no overshoot. -/
theorem goodTime_of_quarterGood (hτ : IsRecord X τ) {B T r L : ℕ}
    (h : QuarterGood X τ B T r L) : ∃ n, GoodTime X τ B T r L n := by
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  refine ⟨τ (r + B * L), h.1, ?_, ?_, ?_, ?_⟩
  · show τ (r + B * L) ≤ τ r + T * L
    have hsub := h.2.1
    rw [Nat.sub_le_iff_le_add] at hsub
    omega
  · show (((r + B * L : ℕ)) : ℤ) ≤ rho X (τ (r + B * L))
    rw [rho_tau hτ]
  · show 4 * e X (τ (r + B * L)) ≤ (L : ℤ)
    rw [e_tau hτ]
    exact h.2.2
  · show 4 * ((τ (r + B * L) : ℤ) - (τ (r + B * L) : ℤ)) ≤ (L : ℤ)
    have h0 : (τ (r + B * L) : ℤ) - (τ (r + B * L) : ℤ) = 0 := by ring
    rw [h0]
    exact_mod_cast Nat.zero_le L

/-- `QuarterGood` excludes both paper bad events. -/
theorem quarterGood_not_bad (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) (h : QuarterGood X τ B T r L) :
    ¬ BadTime B T (fun u => (defect X τ u).toNat, τ) r L ∧
      ¬ BadHalf B (fun u => (defect X τ u).toNat, τ) r L := by
  obtain ⟨n, hn⟩ := goodTime_of_quarterGood hτ h
  exact goodTime_imp_not_bad hτ hne h0 hC₀ hn

/-- **`QuarterGood` also forces the record to be slow**: the halving part is impossible on the fast
record configurations, so `QuarterGood` is *not* implied by `(time)` and `(diam)` alone. -/
theorem quarterGood_record_lower (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {B T r L : ℕ}
    (h : QuarterGood X τ B T r L) :
    2 * ((τ (r + B * L) : ℤ) - (τ r : ℤ)) + (L : ℤ)
      ≥ 2 * ((B * L : ℕ) : ℤ) + 2 * defect X τ r := by
  have hnn : (0 : ℤ) ≤ defect X τ (r + B * L) := defect_nonneg hτ _
  have hhalf : 2 * defect X τ (r + B * L) ≤ (L : ℤ) := by linarith [h.2.2]
  exact record_increment_lower hτ hne hhalf

/-- `QuarterGood` fails on every configuration whose record increment is fast relative to the
deficit `d r`. -/
theorem not_quarterGood_of_fast (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {B T r L : ℕ}
    (hfast : 2 * ((τ (r + B * L) : ℤ) - (τ r : ℤ)) + (L : ℤ)
      < 2 * ((B * L : ℕ) : ℤ) + 2 * defect X τ r) :
    ¬ QuarterGood X τ B T r L := by
  intro h
  have := quarterGood_record_lower hτ hne h
  linarith

/-! ## 6. Transfer to the actual array and to the stopped-record path law -/

theorem measure_noGoodTime_le_notQuarterGood {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ) (hτ : ∀ ω, IsRecord (X ω) (τ ω)) {B T r L : ℕ} :
    μ {ω | ¬ ∃ n, GoodTime (X ω) (τ ω) B T r L n}
      ≤ μ {ω | ¬ QuarterGood (X ω) (τ ω) B T r L} := by
  refine measure_mono ?_
  intro ω hno hq
  exact hno (goodTime_of_quarterGood (hτ ω) hq)

theorem measure_noGoodTime_le_notQuarterGood_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ) (hτ : ∀ᵐ ω ∂μ, IsRecord (X ω) (τ ω)) {B T r L : ℕ} :
    μ {ω | ¬ ∃ n, GoodTime (X ω) (τ ω) B T r L n}
      ≤ μ {ω | ¬ QuarterGood (X ω) (τ ω) B T r L} := by
  refine measure_mono_ae ?_
  filter_upwards [hτ] with ω hω
  intro hno hq
  exact hno (goodTime_of_quarterGood hω hq)

/-- On the actual array, the paper's second bad event is bounded by the `QuarterGood` failure. -/
theorem badHalf_le_notQuarterGood {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadHalf B (HblkFinal.arrQ p m U) r L} ≤
      (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          ¬ QuarterGood (actX p m U) (recTimeA p m U) B T r L} := by
  refine le_trans (badHalf_le_noGoodTime (N := N) hp0 hp1 hm hN hC₀) (measure_mono_ae ?_)
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hU
  intro hno hq
  exact hno (goodTime_of_quarterGood hU hq)

/-- On the actual array, the paper's first bad event is bounded by the `QuarterGood` failure. -/
theorem badTime_le_notQuarterGood {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadTime B T (HblkFinal.arrQ p m U) r L} ≤
      (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          ¬ QuarterGood (actX p m U) (recTimeA p m U) B T r L} := by
  refine le_trans (badTime_le_noGoodTime (N := N) hp0 hp1 hm hN hC₀) (measure_mono_ae ?_)
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hU
  intro hno hq
  exact hno (goodTime_of_quarterGood hU hq)

/-- **Record-defect tightness of the canonical stopped-record path law from a single profile on the
two-clause event `QuarterGood`.**  This is
`FluidWiring.record_tightness_of_goodTime` with the existential-over-`n` fluid condition replaced
by the defect-sequence conjunction `d r ≤ L ∧ τ (r+BL) - τ r ≤ T L ∧ 4 d_{r+BL} ≤ L`, i.e. by the
paper's two block clauses with the halving constant doubled. -/
theorem record_tightness_of_quarterHalf {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (P : ℕ → ℝ≥0∞),
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N |
            ¬ QuarterGood (actX p m U) (recTimeA p m U) B (⌈2 * (B : ℝ) / κ⌉₊ + 2) r ℓ} ≤ P ℓ) →
      ∀ (k : ℕ), 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ 2 ^ k →
        (∑' r : ℕ, P (2 ^ HdefDefect.g k r)) ≠ ⊤ →
        (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * P ℓ) ≠ ⊤ →
        ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
          (SimJump.RecKernel.recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
            (Measure.dirac (StartLaw.zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
            {ω | K < SimJump.RecKernel.dT ω u} ≤ ε := by
  obtain ⟨κ, hκ, H⟩ := record_tightness_of_goodTime (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun P hP => ?_⟩
  refine H P ?_
  intro ℓ hℓ r hr
  refine le_trans (measure_noGoodTime_le_notQuarterGood_ae (ι := Fin N)
    (Swarming.Uniform.arrayMeasure N) (fun U => actX p m U) (fun U => recTimeA p m U) ?_) (hP ℓ hℓ r hr)
  exact ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN

/-! ## 7. The per-walker residual: a left-step profile suffices for `h₂` -/

/-- The per-walker event that carries the halving failure at the actual array: the block data,
the halving failure, `i` is a lowest walker at `τ (r+BL)`, and `i` walked left often enough. -/
def LeftW {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m B : ℕ) (i : Fin N)
    (U : Swarming.Uniform.Array N) (r L : ℕ) : Prop :=
  defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) ∧
    (L : ℤ) < 2 * defect (actX p m U) (recTimeA p m U) (r + B * L) ∧
    actX p m U i (recTimeA p m U (r + B * L))
      = runMin (actX p m U) (recTimeA p m U (r + B * L)) ∧
    4 * ((lCount (actX p m U) i (recTimeA p m U r) (recTimeA p m U (r + B * L)) : ℕ) : ℤ)
        + 2 * ((B * L : ℕ) : ℤ) + (L : ℤ)
      > 2 * ((recTimeA p m U (r + B * L) : ℤ) - (recTimeA p m U r : ℤ))

/-- **The halving failure is covered by the per-walker left-step events.** -/
theorem badHalf_subset_iUnion_leftW {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m B : ℕ}
    {U : Swarming.Uniform.Array N} (hτ : IsRecord (actX p m U) (recTimeA p m U)) {r L : ℕ}
    (h : BadHalf B (HblkFinal.arrQ p m U) r L) : ∃ i : Fin N, LeftW p m B i U r L := by
  obtain ⟨h1, h2⟩ := h
  have hd0 := defect_nonneg hτ r
  have hbase : defect (actX p m U) (recTimeA p m U) r ≤ (L : ℤ) := by
    have hc : ((defect (actX p m U) (recTimeA p m U) r).toNat : ℤ) ≤ (L : ℤ) := by
      exact_mod_cast h1
    rwa [Int.toNat_of_nonneg hd0] at hc
  have hd0' := defect_nonneg hτ (r + B * L)
  have hbad : (L : ℤ) < 2 * defect (actX p m U) (recTimeA p m U) (r + B * L) := by
    have hlt : (L / 2 : ℕ) < (defect (actX p m U) (recTimeA p m U) (r + B * L)).toNat := h2
    have hcast : ((defect (actX p m U) (recTimeA p m U) (r + B * L)).toNat : ℤ)
        = defect (actX p m U) (recTimeA p m U) (r + B * L) := Int.toNat_of_nonneg hd0'
    have hcast' : ((L / 2 : ℕ) : ℤ) < defect (actX p m U) (recTimeA p m U) (r + B * L) := by
      rw [← hcast]
      exact_mod_cast hlt
    omega
  obtain ⟨i, -, hval⟩ :
      ∃ a ∈ (Finset.univ : Finset (Fin N)), runMin (actX p m U) (recTimeA p m U (r + B * L))
        = actX p m U a (recTimeA p m U (r + B * L)) :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
      (fun i => actX p m U i (recTimeA p m U (r + B * L)))
  refine ⟨i, hbase, hbad, hval.symm, ?_⟩
  exact left_gt_of_half_fail hτ (actX_step p m U) hbase hval.symm hbad

/-- **`h₂` from a single-walker left-step profile.**  The measure of the paper's second bad event
is at most the sum of the per-walker profile bounds `q i` on the events `LeftW i`.  No
coalescence statement, no fluid limit and no independence over adaptive coordinates is used: the
deterministic content is `badHalf_subset_iUnion_leftW`, and the union bound over the `N` walkers
is the only loss. -/
theorem measure_badHalf_le_sum_leftW {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B r L : ℕ) (q : Fin N → ℝ≥0∞)
    (h : ∀ i : Fin N, (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | LeftW p m B i U r L} ≤ q i) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadHalf B (HblkFinal.arrQ p m U) r L}
      ≤ ∑ i : Fin N, q i := by
  have hrec := ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hsub : {U : Swarming.Uniform.Array N | BadHalf B (HblkFinal.arrQ p m U) r L}
      ≤ᵐ[Swarming.Uniform.arrayMeasure N]
        ⋃ i : Fin N, {U : Swarming.Uniform.Array N | LeftW p m B i U r L} := by
    filter_upwards [hrec] with U hU hb
    exact Set.mem_iUnion.2 (badHalf_subset_iUnion_leftW hU hb)
  calc (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadHalf B (HblkFinal.arrQ p m U) r L}
      ≤ (Swarming.Uniform.arrayMeasure N)
          (⋃ i : Fin N, {U : Swarming.Uniform.Array N | LeftW p m B i U r L}) :=
        measure_mono_ae hsub
    _ ≤ ∑ i : Fin N, (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | LeftW p m B i U r L} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin N, q i := Finset.sum_le_sum (fun i _ => h i)

/-- The fast-record configurations are a *subset* of the halving failure: any profile for
`BadHalf` must therefore dominate their probability. -/
theorem badHalf_of_fastRecord (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {B r L : ℕ}
    (hbase : defect X τ r ≤ (L : ℤ))
    (hfast : 2 * ((τ (r + B * L) : ℤ) - (τ r : ℤ)) + (L : ℤ)
      < 2 * ((B * L : ℕ) : ℤ) + 2 * defect X τ r) :
    BadHalf B (fun u => (defect X τ u).toNat, τ) r L := by
  have hnhalf : (L : ℤ) < 2 * defect X τ (r + B * L) := by
    by_contra hcon
    push Not at hcon
    have h1 := record_increment_lower hτ hne hcon
    linarith
  refine ⟨?_, ?_⟩
  · change (defect X τ r).toNat ≤ L
    have h0 := defect_nonneg hτ r
    have hcast : ((defect X τ r).toNat : ℤ) = defect X τ r := Int.toNat_of_nonneg h0
    have hle : ((defect X τ r).toNat : ℤ) ≤ (L : ℤ) := by rw [hcast]; exact hbase
    exact_mod_cast hle
  · change L / 2 < (defect X τ (r + B * L)).toNat
    have h0 := defect_nonneg hτ (r + B * L)
    have hcast : ((defect X τ (r + B * L)).toNat : ℤ) = defect X τ (r + B * L) :=
      Int.toNat_of_nonneg h0
    have hle : ((L / 2 : ℕ) : ℤ) < ((defect X τ (r + B * L)).toNat : ℤ) := by
      rw [hcast]
      have hmul : (L / 2 : ℕ) * 2 ≤ L := Nat.div_mul_le_self L 2
      have hmulZ : ((L / 2 : ℕ) : ℤ) * 2 ≤ (L : ℤ) := by exact_mod_cast hmul
      linarith
    exact_mod_cast hle

/-! ## 8. The time clause from a right-step count of the leader -/

/-- **The `(time)` clause from a one-sided right-step count.**  If the walker that is at the
maximum at time `τ r` takes at least `(T L + B L)/2` right steps during the deterministic window
`[τ r, τ r + T L]`, then the record reaches level `r + B L` by time `τ r + T L`.  Together with
`left_gt_of_half_fail` this reduces **both** paper block clauses to per-walker one-sided step
counts over windows of deterministic length, with no coalescence and no fluid limit in between. -/
theorem tau_le_of_rightSteps (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r B T L : ℕ} {i : ι} (hi : X i (τ r) = runMax X (τ r))
    (hR : ((T * L + B * L : ℕ) : ℤ)
      ≤ 2 * ((rCount X i (τ r) (τ r + T * L) : ℕ) : ℤ)) :
    τ (r + B * L) ≤ τ r + T * L := by
  by_contra hcon
  push Not at hcon
  have hlt := (hτ (r + B * L)).1 (τ r + T * L) hcon
  have hmono : τ r ≤ τ r + T * L := Nat.le_add_right _ _
  have hdisp := displacement_eq (X := X) hne i hmono
  have hledger : rCount X i (τ r) (τ r + T * L) + lCount X i (τ r) (τ r + T * L) = T * L := by
    rw [rCount_add_lCount (X := X) hne i hmono]
    omega
  have hZ : ((rCount X i (τ r) (τ r + T * L) : ℕ) : ℤ)
      + ((lCount X i (τ r) (τ r + T * L) : ℕ) : ℤ) = ((T * L : ℕ) : ℤ) := by
    exact_mod_cast hledger
  have hXi : X i (τ r) = (r : ℤ) := by rw [hi, (hτ r).2]
  have hbig : (((r + B * L : ℕ)) : ℤ) ≤ X i (τ r + T * L) := by
    have hcast : (((r + B * L : ℕ)) : ℤ) = (r : ℤ) + ((B * L : ℕ) : ℤ) := by push_cast; ring
    have hcs : ((T * L + B * L : ℕ) : ℤ) = ((T * L : ℕ) : ℤ) + ((B * L : ℕ) : ℤ) := by
      push_cast; ring
    linarith
  linarith [le_runMax (X := X) (τ r + T * L) i]

/-- The per-walker event carrying the time clause at the actual array. -/
def RightW {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m B T : ℕ) (i : Fin N)
    (U : Swarming.Uniform.Array N) (r L : ℕ) : Prop :=
  actX p m U i (recTimeA p m U r) = runMax (actX p m U) (recTimeA p m U r) ∧
    2 * ((rCount (actX p m U) i (recTimeA p m U r) (recTimeA p m U r + T * L) : ℕ) : ℤ)
      < ((T * L + B * L : ℕ) : ℤ)

theorem badTime_subset_iUnion_rightW {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m B T : ℕ}
    {U : Swarming.Uniform.Array N} (hτ : IsRecord (actX p m U) (recTimeA p m U)) {r L : ℕ}
    (h : BadTime B T (HblkFinal.arrQ p m U) r L) : ∃ i : Fin N, RightW p m B T i U r L := by
  obtain ⟨-, htime⟩ := h
  have htime' : recTimeA p m U r + T * L < recTimeA p m U (r + B * L) := htime
  by_contra hcon
  push Not at hcon
  obtain ⟨i, -, hival⟩ :
      ∃ a ∈ (Finset.univ : Finset (Fin N)), runMax (actX p m U) (recTimeA p m U r)
        = actX p m U a (recTimeA p m U r) :=
    Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
      (fun i => actX p m U i (recTimeA p m U r))
  have hi : actX p m U i (recTimeA p m U r) = runMax (actX p m U) (recTimeA p m U r) :=
    hival.symm
  have hR : ((T * L + B * L : ℕ) : ℤ)
      ≤ 2 * ((rCount (actX p m U) i (recTimeA p m U r)
        (recTimeA p m U r + T * L) : ℕ) : ℤ) := by
    have := hcon i
    unfold RightW at this
    push Not at this
    linarith [this hi]
  have hfin := tau_le_of_rightSteps hτ (actX_step p m U) hi hR
  omega

/-- **`h₁` from a single-walker right-step profile.** -/
theorem measure_badTime_le_sum_rightW {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B T r L : ℕ) (q : Fin N → ℝ≥0∞)
    (h : ∀ i : Fin N, (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | RightW p m B T i U r L} ≤ q i) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadTime B T (HblkFinal.arrQ p m U) r L}
      ≤ ∑ i : Fin N, q i := by
  have hrec := ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hsub : {U : Swarming.Uniform.Array N | BadTime B T (HblkFinal.arrQ p m U) r L}
      ≤ᵐ[Swarming.Uniform.arrayMeasure N]
        ⋃ i : Fin N, {U : Swarming.Uniform.Array N | RightW p m B T i U r L} := by
    filter_upwards [hrec] with U hU hb
    exact Set.mem_iUnion.2 (badTime_subset_iUnion_rightW hU hb)
  calc (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadTime B T (HblkFinal.arrQ p m U) r L}
      ≤ (Swarming.Uniform.arrayMeasure N)
          (⋃ i : Fin N, {U : Swarming.Uniform.Array N | RightW p m B T i U r L}) :=
        measure_mono_ae hsub
    _ ≤ ∑ i : Fin N, (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | RightW p m B T i U r L} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin N, q i := Finset.sum_le_sum (fun i _ => h i)

/-! ## 9. Capstone: the paper's `(blkprob)` from two per-walker step-count profiles -/

/-- **The paper's block estimate from per-walker step counts.**

`BadBlk` is the failure of the paper's three block inequalities on `{d r ≤ L}`.  Given only

* a right-step profile `qR i` for the leader at `τ r` over the deterministic window
  `[τ r, τ r + T L]` (event `RightW`), and
* a left-step profile `qL i` for the lowest walker at `τ (r+BL)` over the block window
  (event `LeftW`),

the failure probability of the whole block estimate is at most `∑ᵢ qR i + ∑ᵢ qL i`.  Everything
else — record geometry, the `(diam)` clause, the transfer of the two clauses to `BadBlk` — is
proved in the tree; no fluid limit, no coalescence statement and no independence of adaptive
coordinates is used here. -/
theorem measure_badBlk_le_sum_steps {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) (qR qL : Fin N → ℝ≥0∞)
    (hR : ∀ i : Fin N, (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | RightW p m B T i U r L} ≤ qR i)
    (hL : ∀ i : Fin N, (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | LeftW p m B i U r L} ≤ qL i) :
    (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}
      ≤ ∑ i : Fin N, qR i + ∑ i : Fin N, qL i := by
  have hrec := ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hsub : {U : Swarming.Uniform.Array N | BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}
      ≤ᵐ[Swarming.Uniform.arrayMeasure N]
        {U : Swarming.Uniform.Array N |
          BadTime B T (HblkFinal.arrQ p m U) r L ∨ BadHalf B (HblkFinal.arrQ p m U) r L} := by
    filter_upwards [hrec] with U hU hb
    have himpl : (HblkFinal.arrQ p m U).1 r ≤ L →
        (HblkFinal.arrQ p m U).2 (r + B * L) ≤ (HblkFinal.arrQ p m U).2 r + T * L →
        (HblkFinal.arrQ p m U).1 (r + B * L) ≤ L / 2 →
        GoodSeq B C₀ T (HblkFinal.arrQ p m U).1 (HblkFinal.arrQ p m U).2 r L :=
      fun hd ht hh => himpl_of_record hU (actX_step p m U) hC₀ hd ht hh
    rcases badBlk_subset himpl hb with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}
      ≤ (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N |
            BadTime B T (HblkFinal.arrQ p m U) r L ∨ BadHalf B (HblkFinal.arrQ p m U) r L} :=
        measure_mono_ae hsub
    _ = (Swarming.Uniform.arrayMeasure N)
          ({U : Swarming.Uniform.Array N | BadTime B T (HblkFinal.arrQ p m U) r L}
            ∪ {U : Swarming.Uniform.Array N | BadHalf B (HblkFinal.arrQ p m U) r L}) := by
        rw [Set.ofPred_or]
    _ ≤ (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | BadTime B T (HblkFinal.arrQ p m U) r L}
        + (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | BadHalf B (HblkFinal.arrQ p m U) r L} :=
        measure_union_le _ _
    _ ≤ ∑ i : Fin N, qR i + ∑ i : Fin N, qL i :=
        add_le_add (measure_badTime_le_sum_rightW hp0 hp1 hm hN B T r L qR hR)
          (measure_badHalf_le_sum_leftW hp0 hp1 hm hN B r L qL hL)

end LagForce

/-! ## Axiom audit -/


