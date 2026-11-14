/-
# The fluid single-time criterion for the paper's block estimate `(blkprob)`

`HblkTwo` reduces the paper's `(blkprob)` to the two bad events

* `BadTime` — `τ (r + B L) - τ r > T L`   (the fluid bound `R(T) > B + 2`),
* `BadHalf` — `2 d (r + B L) > L`         (the fluid contraction),

on `{d r ≤ L}`.  The paper proves both clauses *at one time*: on its local good set the rescaled
paths converge along `L → ∞` to a fluid path for which the record level is exactly `B` above `r`
and all walkers have coalesced at the fluid time `θ = lim (τ_{r+BL} - τ_r)/L ∈ [B, T]`.

This file isolates that step as **deterministic mathematics about one integer time** `n`, with no
probability, no compactness and no asymptotic argument:

* `rho X n` is the *record level held at time `n`* (the running maximum in time of the walker
  maximum), and `e X n = rho X n - runMin X n` is the **spread below the held record level**;
* `tau_le_iff_rho_le` — record duality: `τ y ≤ n ↔ y ≤ rho X n`.  In particular the paper's
  `(time)` clause is exactly "the record level advanced by time `n`";
* `defect_le_e_add` — **the transfer inequality**: for `τ y ≤ n`,
  `d y ≤ e n + (n - τ y)`.  This is the deterministic content of the paper's final step
  `d_{r+BL}/L = B - min_i x_i^{(L)}((τ_{r+BL}-τ_r)/L) → B - min_i x_i(θ) = 0`: the defect at
  level `y` is at most the spread at time `n` plus the time overshoot `n - τ_y`;
* `goodBlock_of_fluid` — if at **one** time `n`, with `n ≤ τ r + T L`,
  (i) the record level is at least `r + B L`, (ii) `4 e n ≤ L`, (iii) `4 (n - τ_{r+BL}) ≤ L`,
  then the three paper block inequalities hold at `(r, L)`.
  Consequently neither `BadTime` nor `BadHalf` occurs (`not_badTime_of_fluid`,
  `not_badHalf_of_fluid`), and the residual stochastic input is the single profile
  `μ {ω | no such n exists}` (`measure_badTime_le_compl`).

Sharpness: `advance_alone_insufficient` exhibits a nearest-neighbour family with
`X⁰_n = n`, `X¹_n = -n` where hypothesis (i) holds for every admissible `(r, L)` yet the block
estimate fails, so the coalescence hypotheses (ii)/(iii) cannot be dropped.  `fluid_nonvacuous`
checks the criterion is satisfiable.

No probability, no `sorry`, no custom axiom.  See `README.md` for what is *not* proved here.
-/
import Swarm.HblkTwo

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace FluidBlock

open RecordDefect RecordoSupply SwarmM4C.LawBridge HblkTwo

variable {ι : Type*} [Fintype ι] [Nonempty ι]

variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-! ### The record level held at time `n` -/

/-- The record level held at time `n`: the running maximum **in time** of the walker maximum.
(`RecordDefect.runMax X n` is the walker maximum at the single time `n`; it need not be
monotone, so the paper's `R_n^A` is this running maximum.) -/
noncomputable def rho (X : ι → ℕ → ℤ) : ℕ → ℤ
  | 0 => runMax X 0
  | n + 1 => max (rho X n) (runMax X (n + 1))

theorem rho_zero (X : ι → ℕ → ℤ) : rho X 0 = runMax X 0 := rfl

theorem rho_succ (X : ι → ℕ → ℤ) (n : ℕ) :
    rho X (n + 1) = max (rho X n) (runMax X (n + 1)) := rfl

/-- Every earlier walker maximum is at most the record level held now. -/
theorem le_rho (X : ι → ℕ → ℤ) {k n : ℕ} (hk : k ≤ n) : runMax X k ≤ rho X n := by
  induction n with
  | zero =>
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      exact le_of_eq (rho_zero X).symm
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hk with h | h
      · exact le_trans (ih (Nat.lt_succ_iff.mp h)) (le_max_left _ _)
      · subst h
        exact le_max_right _ _

/-- The record level is monotone in time. -/
theorem rho_mono (X : ι → ℕ → ℤ) : Monotone (rho X) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (le_max_left _ _)

/-- Before (and at) the record time of level `r` the walker maximum never exceeds `r`. -/
theorem runMax_le_of_le_tau (hτ : IsRecord X τ) {r k : ℕ} (hk : k ≤ τ r) :
    runMax X k ≤ (r : ℤ) := by
  rcases Nat.lt_or_eq_of_le hk with h | h
  · exact le_of_lt ((hτ r).1 k h)
  · rw [h]
    exact le_of_eq (hτ r).2

/-- Before the record time of level `r` the record level held is at most `r`. -/
theorem rho_le_of_le_tau (hτ : IsRecord X τ) {r n : ℕ} (hn : n ≤ τ r) :
    rho X n ≤ (r : ℤ) := by
  induction n with
  | zero =>
      rw [rho_zero]
      exact runMax_le_of_le_tau hτ hn
  | succ n ih =>
      rw [rho_succ]
      exact max_le (ih (le_trans (Nat.le_succ n) hn)) (runMax_le_of_le_tau hτ hn)

/-- **At the record time of level `r` the record level held is exactly `r`.** -/
theorem rho_tau (hτ : IsRecord X τ) (r : ℕ) : rho X (τ r) = (r : ℤ) := by
  refine le_antisymm (rho_le_of_le_tau hτ le_rfl) ?_
  rw [← (hτ r).2]
  exact le_rho X le_rfl

/-- The record level held dominates every level already reached. -/
theorem le_rho_of_tau_le (hτ : IsRecord X τ) {r n : ℕ} (h : τ r ≤ n) :
    (r : ℤ) ≤ rho X n := by
  rw [← (hτ r).2]
  exact le_rho X h

/-- A level at most the held record level is attained by some walker maximum at a time `k ≤ n`. -/
theorem exists_le_runMax_of_le_rho (X : ι → ℕ → ℤ) :
    ∀ {r n : ℕ}, (r : ℤ) ≤ rho X n → ∃ k ≤ n, (r : ℤ) ≤ runMax X k := by
  intro r n
  induction n with
  | zero =>
      intro h
      exact ⟨0, le_rfl, h⟩
  | succ n ih =>
      intro h
      rw [rho_succ] at h
      rcases le_max_iff.mp h with h' | h'
      · obtain ⟨k, hk, hkr⟩ := ih h'
        exact ⟨k, le_trans hk (Nat.le_succ n), hkr⟩
      · exact ⟨n + 1, le_rfl, h'⟩

/-- **Record duality.**  The record time of level `r` is at most `n` exactly when the record level
held at time `n` has reached `r`. -/
theorem tau_le_iff_rho_le (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) {r n : ℕ} : τ r ≤ n ↔ (r : ℤ) ≤ rho X n := by
  refine ⟨le_rho_of_tau_le hτ, fun h => ?_⟩
  obtain ⟨k, hk, hkr⟩ := exists_le_runMax_of_le_rho X h
  obtain ⟨m, hm, hmval⟩ := exists_runMax_eq X hne h0 hkr
  have hτm : τ r ≤ m := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt := (hτ r).1 m hcon
    rw [hmval] at hlt
    linarith
  exact le_trans hτm (le_trans hm hk)

/-! ### The spread below the held record level -/

/-- The spread below the record level currently held. -/
noncomputable def e (X : ι → ℕ → ℤ) (n : ℕ) : ℤ := rho X n - runMin X n

/-- At a record time the spread below the held record level **is** the paper's defect. -/
theorem e_tau (hτ : IsRecord X τ) (r : ℕ) : e X (τ r) = defect X τ r := by
  rw [e, rho_tau hτ, defect]

/-- Nearest-neighbour walkers move by at most the elapsed number of steps (later position from
the earlier one). -/
theorem step_le_add (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (i : ι) :
    ∀ {m k : ℕ}, m ≤ k → X i k ≤ X i m + (((k - m : ℕ)) : ℤ) := by
  intro m k hmk
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
      have hstep : X i (k + 1) ≤ X i k + 1 := by
        have h1 : |X i (k + 1) - X i k| ≤ 1 := le_of_eq (hne i k)
        have h2 := (abs_le.1 h1).2
        linarith
      have hcast : (((k + 1 - m : ℕ)) : ℤ) = (((k - m : ℕ)) : ℤ) + 1 := by
        have h : k + 1 - m = (k - m) + 1 := by omega
        rw [h]
        push_cast
        ring
      rw [hcast]
      linarith

/-- **The transfer inequality.**  Once the record level has passed `y`, the defect at level `y`
is bounded by the spread below the record level held at time `n` plus the time overshoot
`n - τ y`.  This is the deterministic content of the paper's last block-estimate step. -/
theorem defect_le_e_add (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {y n : ℕ} (hy : τ y ≤ n) :
    defect X τ y ≤ e X n + ((n : ℤ) - (τ y : ℤ)) := by
  have hbound : ∀ i : ι, runMin X n - (((n - τ y : ℕ)) : ℤ) ≤ X i (τ y) := by
    intro i
    have h1 := step_le_add (X := X) hne i hy
    have h2 := runMin_le (X := X) n i
    linarith
  have hmin : runMin X n - (((n - τ y : ℕ)) : ℤ) ≤ runMin X (τ y) :=
    Finset.le_inf' _ _ (fun i _ => hbound i)
  have hrho := le_rho_of_tau_le hτ hy
  have hcast : (((n - τ y : ℕ)) : ℤ) = (n : ℤ) - (τ y : ℤ) := by
    push_cast [hy]
    ring
  rw [defect, e]
  linarith

/-! ### The block estimate from one fluid time -/

/-- **The paper's block inequalities from a single good time.**

If at a time `n`, at most `T L` steps after the record time of level `r`,
(i) the record level has reached `r + B L`,
(ii) the spread below that level is at most `L/4`,
(iii) the record time of level `r + B L` is within `L/4` of `n`,
then the three block inequalities of Proposition `tight` hold at `(r, L)` on `{d r ≤ L}`. -/
theorem goodBlock_of_fluid (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0)
    {B T C₀ r L n : ℕ} (hC₀ : B + T + 1 ≤ C₀)
    (hbase : defect X τ r ≤ (L : ℤ))
    (hn : n ≤ τ r + T * L)
    (hadv : (((r + B * L : ℕ)) : ℤ) ≤ rho X n)
    (hspread : 4 * e X n ≤ (L : ℤ))
    (hslack : 4 * ((n : ℤ) - (τ (r + B * L) : ℤ)) ≤ (L : ℤ)) :
    GoodBlock (defect X τ) τ T C₀ B r L := by
  have htime : τ (r + B * L) ≤ n := (tau_le_iff_rho_le hτ hne h0).mpr hadv
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have htimeClause : τ (r + B * L) - τ r ≤ T * L := by omega
  have hd := defect_le_e_add hτ hne htime
  have hhalf : 2 * defect X τ (r + B * L) ≤ (L : ℤ) := by linarith
  refine ⟨htimeClause, hhalf, ?_⟩
  intro u hru huBL
  have hb := block_defect_bound hτ hne (B := B) (T := T) (L := L) (r := r) hbase htimeClause
      u hru huBL
  have hCL : (((B + T + 1 : ℕ)) : ℤ) * (L : ℤ) ≤ (((C₀ : ℕ)) : ℤ) * (L : ℤ) := by
    have h1 : (((B + T + 1 : ℕ)) : ℤ) ≤ (((C₀ : ℕ)) : ℤ) := by exact_mod_cast hC₀
    exact mul_le_mul_of_nonneg_right h1 (by exact_mod_cast Nat.zero_le L)
  linarith

/-- The same, in the `GoodSeq` form consumed by `HblkTwo`. -/
theorem goodSeq_of_fluid (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0)
    {B T C₀ r L n : ℕ} (hC₀ : B + T + 1 ≤ C₀)
    (hbase : defect X τ r ≤ (L : ℤ))
    (hn : n ≤ τ r + T * L)
    (hadv : (((r + B * L : ℕ)) : ℤ) ≤ rho X n)
    (hspread : 4 * e X n ≤ (L : ℤ))
    (hslack : 4 * ((n : ℤ) - (τ (r + B * L) : ℤ)) ≤ (L : ℤ)) :
    GoodSeq B C₀ T (fun u => (defect X τ u).toNat) τ r L :=
  (goodBlock_iff_goodSeq (d := defect X τ) (fun r => defect_nonneg hτ r)).mp
    (goodBlock_of_fluid hτ hne h0 hC₀ hbase hn hadv hspread hslack)

/-- On the single-time good condition the paper's first bad event does not occur. -/
theorem not_badTime_of_fluid (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0)
    {B T C₀ r L n : ℕ} (hC₀ : B + T + 1 ≤ C₀)
    (hbase : defect X τ r ≤ (L : ℤ))
    (hn : n ≤ τ r + T * L)
    (hadv : (((r + B * L : ℕ)) : ℤ) ≤ rho X n)
    (hspread : 4 * e X n ≤ (L : ℤ))
    (hslack : 4 * ((n : ℤ) - (τ (r + B * L) : ℤ)) ≤ (L : ℤ)) :
    ¬ BadTime B T (fun u => (defect X τ u).toNat, τ) r L := by
  intro hb
  have hg := goodSeq_of_fluid hτ hne h0 hC₀ hbase hn hadv hspread hslack
  have h1 : τ (r + B * L) ≤ τ r + T * L := hg.1
  exact absurd h1 (not_le.mpr hb.2)

/-- On the single-time good condition the paper's second bad event does not occur. -/
theorem not_badHalf_of_fluid (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0)
    {B T C₀ r L n : ℕ} (hC₀ : B + T + 1 ≤ C₀)
    (hbase : defect X τ r ≤ (L : ℤ))
    (hn : n ≤ τ r + T * L)
    (hadv : (((r + B * L : ℕ)) : ℤ) ≤ rho X n)
    (hspread : 4 * e X n ≤ (L : ℤ))
    (hslack : 4 * ((n : ℤ) - (τ (r + B * L) : ℤ)) ≤ (L : ℤ)) :
    ¬ BadHalf B (fun u => (defect X τ u).toNat, τ) r L := by
  intro hb
  have hg := goodSeq_of_fluid hτ hne h0 hC₀ hbase hn hadv hspread hslack
  have h1 : (defect X τ (r + B * L)).toNat ≤ L / 2 := hg.2.1
  exact absurd h1 (not_le.mpr hb.2)

/-! ### The residual stochastic input, in measure form

The condition below is the paper's good set at the level of the array: it asks that at the
(free) integer time `n` the record level has reached `r + B L` and the configuration has
coalesced below it, with the record time of level `r + B L` within `L/4` of `n`.  No
measurability is needed for the inclusion; `measure_mono` then bounds both bad events by the
probability that no such time exists. -/

/-- The single-time good condition of `goodBlock_of_fluid`. -/
def GoodTime (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (B T r L n : ℕ) : Prop :=
  defect X τ r ≤ (L : ℤ) ∧ n ≤ τ r + T * L ∧ (((r + B * L : ℕ)) : ℤ) ≤ rho X n ∧
    4 * e X n ≤ (L : ℤ) ∧ 4 * ((n : ℤ) - (τ (r + B * L) : ℤ)) ≤ (L : ℤ)

theorem goodTime_imp_not_bad (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) {B T C₀ r L n : ℕ} (hC₀ : B + T + 1 ≤ C₀)
    (h : GoodTime X τ B T r L n) :
    ¬ BadTime B T (fun u => (defect X τ u).toNat, τ) r L ∧
      ¬ BadHalf B (fun u => (defect X τ u).toNat, τ) r L :=
  ⟨not_badTime_of_fluid hτ hne h0 hC₀ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2,
   not_badHalf_of_fluid hτ hne h0 hC₀ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

/-- **The measure-level reduction.**  For any measure space of nearest-neighbour families with
record-sequence structure, the probability of the paper's first bad event is at most the
probability that no single good fluid time exists. -/
theorem measure_badTime_le_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (h0 : ∀ (ω : Ω) (i : ι), X ω i 0 = 0)
    (hτ : ∀ ω : Ω, IsRecord (X ω) (τ ω))
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    μ {ω | BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | ¬ ∃ n : ℕ, GoodTime (X ω) (τ ω) B T r L n} := by
  apply measure_mono
  intro ω hω
  rintro ⟨n, hn⟩
  exact (goodTime_imp_not_bad (hτ ω) (hne ω) (h0 ω) hC₀ hn).1 hω

/-- The same for the paper's second bad event. -/
theorem measure_badHalf_le_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (h0 : ∀ (ω : Ω) (i : ι), X ω i 0 = 0)
    (hτ : ∀ ω : Ω, IsRecord (X ω) (τ ω))
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    μ {ω | BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | ¬ ∃ n : ℕ, GoodTime (X ω) (τ ω) B T r L n} := by
  apply measure_mono
  intro ω hω
  rintro ⟨n, hn⟩
  exact (goodTime_imp_not_bad (hτ ω) (hne ω) (h0 ω) hC₀ hn).2 hω

/-! ### Sharpness: the ballistic advance alone does not give the contraction

Two counter-moving walkers `X⁰_n = n`, `X¹_n = -n`.  The record level advances at maximal speed
(`rho = n`, `τ = id`), so the paper's `(time)` clause holds for every admissible `(r, L)`; but the
spread below the record level is `2n`, and `(half)` fails at every level.  So the coalescence
hypotheses of `goodBlock_of_fluid` are independent of the ballistic one. -/

/-- Two counter-moving walkers. -/
def Xtwo : Bool → ℕ → ℤ := fun i n => if i then (n : ℤ) else -(n : ℤ)

theorem Xtwo_zero (i : Bool) : Xtwo i 0 = 0 := by
  cases i <;> rfl

theorem Xtwo_step (i : Bool) (n : ℕ) : |Xtwo i (n + 1) - Xtwo i n| = 1 := by
  cases i <;> simp [Xtwo] <;> norm_num

theorem Xtwo_runMax (n : ℕ) : runMax Xtwo n = (n : ℤ) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun i _ => ?_)
    cases i <;> simp [Xtwo]
  · have h := le_runMax (X := Xtwo) n true
    simpa [Xtwo] using h

theorem Xtwo_runMin (n : ℕ) : runMin Xtwo n = -(n : ℤ) := by
  refine le_antisymm ?_ ?_
  · have h := runMin_le (X := Xtwo) n false
    simpa [Xtwo] using h
  · refine Finset.le_inf' _ _ (fun i _ => ?_)
    cases i <;> simp [Xtwo]

theorem Xtwo_isRecord : IsRecord Xtwo id := by
  intro r
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [Xtwo_runMax]
    exact_mod_cast hn
  · simp [Xtwo_runMax]

theorem Xtwo_rho (n : ℕ) : rho Xtwo n = (n : ℤ) := by
  induction n with
  | zero => simp [rho_zero, Xtwo_runMax]
  | succ n ih => rw [rho_succ, ih, Xtwo_runMax]; simp

theorem Xtwo_e (n : ℕ) : e Xtwo n = 2 * (n : ℤ) := by
  rw [e, Xtwo_rho, Xtwo_runMin]
  ring

theorem Xtwo_defect (y : ℕ) : defect Xtwo id y = 2 * (y : ℤ) := by
  rw [defect, Xtwo_runMin]
  simp
  ring

/-- In the counter-moving example the ballistic advance condition of `goodBlock_of_fluid` holds at
every admissible block, yet the block estimate fails: the coalescence clause is indispensable. -/
theorem advance_alone_insufficient {B T C₀ r L : ℕ} (hr : 1 ≤ r) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hTB : B * L ≤ T * L) :
    (((r + B * L : ℕ)) : ℤ) ≤ rho Xtwo (r + T * L) ∧
      ¬ GoodBlock (defect Xtwo id) id T C₀ B r L := by
  have hrho : rho Xtwo (r + T * L) = (((r + T * L : ℕ)) : ℤ) := Xtwo_rho _
  constructor
  · rw [hrho]
    exact_mod_cast Nat.add_le_add_left hTB r
  · intro hg
    have hhalf : 2 * defect Xtwo id (r + B * L) ≤ (L : ℤ) := hg.2.1
    rw [Xtwo_defect] at hhalf
    have hpos : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    have hLpos : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    have hmul : L ≤ B * L := Nat.le_mul_of_pos_left L (by omega : 0 < B)
    have hBL : (1 : ℤ) + (L : ℤ) ≤ (((r + B * L : ℕ)) : ℤ) := by
      have h1 : 1 + L ≤ r + B * L := by omega
      exact_mod_cast h1
    nlinarith [hpos, hLpos, hBL, hhalf]

/-! ### Non-vacuity of the criterion

A single walker moving deterministically `X n = n` with `T = B` satisfies every hypothesis of
`goodBlock_of_fluid`, so the criterion is not vacuous. -/

/-- The deterministic right-moving single walker. -/
def Xid : Unit → ℕ → ℤ := fun _ n => (n : ℤ)

theorem Xid_zero (i : Unit) : Xid i 0 = 0 := rfl

theorem Xid_step (i : Unit) (n : ℕ) : |Xid i (n + 1) - Xid i n| = 1 := by
  simp [Xid]

theorem Xid_runMax (n : ℕ) : runMax Xid n = (n : ℤ) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun i _ => ?_)
    simp [Xid]
  · have h := le_runMax (X := Xid) n Unit.unit
    simpa [Xid] using h

theorem Xid_runMin (n : ℕ) : runMin Xid n = (n : ℤ) := by
  refine le_antisymm ?_ ?_
  · have h := runMin_le (X := Xid) n Unit.unit
    simpa [Xid] using h
  · refine Finset.le_inf' _ _ (fun i _ => ?_)
    simp [Xid]

theorem Xid_isRecord : IsRecord Xid id := by
  intro r
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [Xid_runMax]
    exact_mod_cast hn
  · simp [Xid_runMax]

theorem Xid_rho (n : ℕ) : rho Xid n = (n : ℤ) := by
  induction n with
  | zero => simp [rho_zero, Xid_runMax]
  | succ n ih => rw [rho_succ, ih, Xid_runMax]; simp

theorem Xid_e (n : ℕ) : e Xid n = 0 := by
  rw [e, Xid_rho, Xid_runMin]
  ring

theorem Xid_defect (y : ℕ) : defect Xid id y = 0 := by
  rw [defect, Xid_runMin]
  simp

/-- **The single-time criterion is satisfiable** (hence not a vacuous reduction): at
`T = B`, `B ≥ 1`, `L ≥ 1` the deterministic walker satisfies all fluid hypotheses and the block
estimate holds. -/
theorem fluid_nonvacuous {B C₀ r L : ℕ} (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hC₀ : B + B + 1 ≤ C₀) :
    GoodTime Xid id B B r L (r + B * L) ∧
      GoodBlock (defect Xid id) id B C₀ B r L := by
  have hG : GoodTime Xid id B B r L (r + B * L) := by
    refine ⟨?_, le_rfl, ?_, ?_, ?_⟩
    · rw [Xid_defect]
      exact_mod_cast Nat.zero_le L
    · simp [Xid_rho]
    · rw [Xid_e]
      exact_mod_cast Nat.zero_le L
    · simp
  exact ⟨hG, goodBlock_of_fluid (X := Xid) Xid_isRecord Xid_step Xid_zero hC₀ hG.1 hG.2.1
    hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2⟩

end FluidBlock


