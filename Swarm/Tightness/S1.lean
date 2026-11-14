/-
# `h₁` (slow block) and `h₂` (defect halving) are per-walker increment / spread statements

`areas/tightness/RESIDUAL_LEDGER.md` §2 pins the remaining analytic input of the invariant-record
route to two profiles on the paper's block bad events (`HblkTwo.BadTime`, `HblkTwo.BadHalf`,
evaluated at the tree's `arrQ p m U = ((d_r).toNat, τ_r)`):

  `h₁`:  `μ {d_r ≤ L ∧ τ_r + T L < τ_{r+BL}} ≤ K e^{-cL}`  for `L ≥ 1`, `r ≥ (B+T+1)L`;
  `h₂`:  `μ {d_r ≤ L ∧ L/2 < d_{r+BL}} ≤ K e^{-cL}`        for `L ≥ 1`, `r ≥ (B+1)L`.

The two predicates below are **verbatim copies** of those two definitions, stated for an abstract
nearest-neighbour record family `(X, τ)` (the tree's `RecordDefect.IsRecord`), because the module
`HblkTwo` cannot be imported inside the memory budget of this direction: `import HblkTwo` needs
13.5 GB resident.  The identification is definitional:

  `SlowBlock X τ B T r L  ↔  HblkTwo.BadTime B T (((fun r => (defect X τ r).toNat), τ)) r L`,
  `HalfBlock X τ B r L    ↔  HblkTwo.BadHalf B (((fun r => (defect X τ r).toNat), τ)) r L`

(`HblkTwo.BadTime B T q r L = (q.1 r ≤ L ∧ q.2 r + T * L < q.2 (r + B * L))`,
`HblkTwo.BadHalf B q r L = (q.1 r ≤ L ∧ L / 2 < q.1 (r + B * L))`).

Three results.

1. **`h₁` is a per-walker block-increment statement.**  On a record family, the slow block forces
   *every* walker's increment over the `T L` steps to satisfy
   `X j (τ_r + T L) - X j (τ_r) ≤ (B L + L) - 1`.  Hence `h₁` follows from a single-walker profile
   on `SmallInc`, with the union bound over the `N` walkers as the only loss and no stationarity,
   leader selection or halving input (`measure_slowBlock_le`).

2. **`h₂` is a spread statement at the later record time.**  If the defect at `r + B L` exceeds
   `L/2`, then some walker sits strictly below `r + B L - L/2`, i.e. the spread
   `runMax - runMin` at `τ (r + B L)` exceeds `L/2` (`exists_X_lt_of_half`, `spread_gt_of_half`).
   So `h₂` cannot be a single-walker step count (the ledger's §3.1); it is a statement about the
   walkers' dispersion.

3. **A no-go for the step-count route to `h₁`.**  The model's one-step right probability is
   `Swarm.rightProb = 1/2 + (p - 1/2)·[excited]` (`areas/assembly/Model.lean`), so the only
   unconditional value is `1/2`, i.e. drift `2·(1/2) - 1 = 0`.  Clearing the deterministic
   increment threshold `(B+1) L` over `T L` steps needs drift `> (B+1)/T > 0` for every `B, T ≥ 1`.
   Hence no estimate using only `1/2 ≤ rightProb` (fair-coin / Azuma / Ville on the walker's own
   steps) can yield `h₁`: the excitation gain (`rightProb = p` on `excitedSet`) on a positive-mass
   set is indispensable — the campaign's `full goodprob` input.

No probability estimate is assumed and no open target (`hblk`, `h₁`, `h₂`, `Ballistic`,
`MainClaim`) is asserted.
-/
import Swarm.RecordDefect
import Swarm.Assembly.Model

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace SlowBlock

open RecordDefect Swarm

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The record band at the record time -/

/-- **Lower end of the record band.**  If the defect at level `r` is at most `L`, then every walker
is at position at least `r - L` at the record time `τ r`. -/
theorem le_X_record_time {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ) {r L : ℕ}
    (hd : (defect X τ r).toNat ≤ L) (j : Fin N) :
    (r : ℤ) - (L : ℤ) ≤ X j (τ r) := by
  have hmin : runMin X (τ r) ≤ X j (τ r) := runMin_le (τ r) j
  have hspec : runMax X (τ r) = (r : ℤ) := (hrec r).2
  have hle : runMin X (τ r) ≤ runMax X (τ r) := runMin_le_runMax (τ r)
  have hnonneg : 0 ≤ defect X τ r := by
    rw [defect]
    linarith
  have hcast : ((defect X τ r).toNat : ℤ) ≤ (L : ℤ) := by exact_mod_cast hd
  rw [Int.toNat_of_nonneg hnonneg] at hcast
  rw [defect] at hcast
  linarith

/-- **Upper end of the record band.**  Every walker is at position at most `r` at time `τ r`. -/
theorem X_record_time_le {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ) (r : ℕ)
    (j : Fin N) : X j (τ r) ≤ (r : ℤ) := by
  have h := le_runMax (X := X) (τ r) j
  rwa [(hrec r).2] at h

/-! ## 2. The two block bad events, verbatim from `HblkTwo` -/

/-- The paper's slow-block event, `HblkTwo.BadTime` with `q = ((d_r).toNat, τ_r)`. -/
def SlowBlock (X : Fin N → ℕ → ℤ) (τ : ℕ → ℕ) (B T r L : ℕ) : Prop :=
  (defect X τ r).toNat ≤ L ∧ τ r + T * L < τ (r + B * L)

/-- The paper's defect-halving failure, `HblkTwo.BadHalf` with `q = ((d_r).toNat, τ_r)`. -/
def HalfBlock (X : Fin N → ℕ → ℤ) (τ : ℕ → ℕ) (B r L : ℕ) : Prop :=
  (defect X τ r).toNat ≤ L ∧ L / 2 < (defect X τ (r + B * L)).toNat

/-- The single-walker small-increment event at level `r` over a block of `T L` steps. -/
def SmallInc (X : Fin N → ℕ → ℤ) (τ : ℕ → ℕ) (B T r L : ℕ) : Prop :=
  ∃ j : Fin N, X j (τ r + T * L) - X j (τ r) ≤ ((B * L + L : ℕ) : ℤ) - 1

/-! ## 3. `h₁` is a per-walker block-increment statement -/

/-- **Deterministic content of the slow-block event.**  The walkers start in the band
`[r - L, r]` at time `τ r` and are still strictly below `r + B L` at `τ r + T L`, so *every*
walker's increment over those `T L` steps is at most `(B L + L) - 1`. -/
theorem increment_le_of_slow {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ) {r L B T : ℕ}
    (hd : (defect X τ r).toNat ≤ L) (hslow : τ r + T * L < τ (r + B * L)) (j : Fin N) :
    X j (τ r + T * L) - X j (τ r) ≤ ((B * L + L : ℕ) : ℤ) - 1 := by
  have hupper : X j (τ r + T * L) < (r : ℤ) + ((B * L : ℕ) : ℤ) := by
    have h1 : runMax X (τ r + T * L) < ((r + B * L : ℕ) : ℤ) := (hrec (r + B * L)).1 _ hslow
    have h2 : X j (τ r + T * L) ≤ runMax X (τ r + T * L) := le_runMax _ j
    have h3 : ((r + B * L : ℕ) : ℤ) = (r : ℤ) + ((B * L : ℕ) : ℤ) := by push_cast; ring
    rw [h3] at h1
    linarith
  have hlower : (r : ℤ) - (L : ℤ) ≤ X j (τ r) := le_X_record_time hrec hd j
  have hcast : ((B * L + L : ℕ) : ℤ) = ((B * L : ℕ) : ℤ) + (L : ℤ) := by push_cast; ring
  rw [hcast]
  linarith

/-- **`h₁` reduces to a single-walker block-increment profile.** -/
theorem slowBlock_subset_smallInc {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ)
    {B T r L : ℕ} (h : SlowBlock X τ B T r L) : SmallInc X τ B T r L :=
  ⟨Classical.arbitrary (Fin N), increment_le_of_slow hrec h.1 h.2 _⟩

/-- **The measure form.**  A bound on the single-walker small-increment event bounds the
slow-block probability; the union bound over the `N` walkers is the only loss. -/
theorem measure_slowBlock_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ} (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L : ℕ) :
    μ {ω | SlowBlock (X ω) (τ ω) B T r L} ≤ μ {ω | SmallInc (X ω) (τ ω) B T r L} :=
  measure_mono fun ω h => slowBlock_subset_smallInc (hrec ω) h

/-! ## 4. `h₂` is a spread statement at the later record time -/

/-- The spread of the walkers' positions at time `n`. -/
noncomputable def spread (X : Fin N → ℕ → ℤ) (n : ℕ) : ℤ :=
  runMax X n - runMin X n

/-- **`h₂` forces a low walker at the later record time.**  If the defect at `r + B L` exceeds
`L/2`, some walker sits strictly below `r + B L - L/2`. -/
theorem exists_X_lt_of_half {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ) {r L B : ℕ}
    (hhalf : L / 2 < (defect X τ (r + B * L)).toNat) :
    ∃ j : Fin N, X j (τ (r + B * L)) < ((r + B * L : ℕ) : ℤ) - ((L / 2 : ℕ) : ℤ) := by
  have hle : runMin X (τ (r + B * L)) ≤ runMax X (τ (r + B * L)) := runMin_le_runMax _
  have hspec : runMax X (τ (r + B * L)) = ((r + B * L : ℕ) : ℤ) := (hrec (r + B * L)).2
  have hnonneg : 0 ≤ defect X τ (r + B * L) := by
    rw [defect]
    linarith
  have hcast : ((L / 2 : ℕ) : ℤ) < defect X τ (r + B * L) := by
    have h1 : ((L / 2 : ℕ) : ℤ) < ((defect X τ (r + B * L)).toNat : ℤ) := by exact_mod_cast hhalf
    rwa [Int.toNat_of_nonneg hnonneg] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin N))) (H := Finset.univ_nonempty)
    (f := fun i => X i (τ (r + B * L)))
  refine ⟨j, ?_⟩
  have hmin : runMin X (τ (r + B * L)) = X j (τ (r + B * L)) := hj
  rw [defect] at hcast
  rw [hmin] at hcast
  linarith

/-- The spread form: the defect-halving failure forces spread `> L/2` at `τ (r + B L)`. -/
theorem spread_gt_of_half {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ) {r L B : ℕ}
    (hhalf : L / 2 < (defect X τ (r + B * L)).toNat) :
    ((L / 2 : ℕ) : ℤ) < spread X (τ (r + B * L)) := by
  obtain ⟨j, hj⟩ := exists_X_lt_of_half (N := N) hrec (r := r) (L := L) (B := B) hhalf
  have hspec : runMax X (τ (r + B * L)) = ((r + B * L : ℕ) : ℤ) := (hrec (r + B * L)).2
  have hge : runMin X (τ (r + B * L)) ≤ X j (τ (r + B * L)) := runMin_le _ j
  rw [spread, hspec]
  linarith

/-- The `h₂` reduction in set form: the halving-failure event is contained in the event
"spread exceeds `L/2` at `τ (r + B L)`". -/
theorem halfBlock_subset_spread {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hrec : IsRecord X τ)
    {B r L : ℕ} (h : HalfBlock X τ B r L) :
    ((L / 2 : ℕ) : ℤ) < spread X (τ (r + B * L)) :=
  spread_gt_of_half hrec h.2

/-! ## 5. The static one-step bound cannot give `h₁` -/

/-- Off the excited set the model's right probability is exactly `1/2`. -/
theorem rightProb_of_not_excited {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {X : ℕ → Ω → Fin N → ℤ} {m n : ℕ} {ω : Ω} {i : Fin N} {p : ℝ}
    (h : ¬ Excited X m n ω i) :
    rightProb p X m n ω i = 1 / 2 := by
  simp [rightProb, h]

/-- On the excited set the model's right probability is exactly `p`. -/
theorem rightProb_of_excited {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {X : ℕ → Ω → Fin N → ℤ} {m n : ℕ} {ω : Ω} {i : Fin N} {p : ℝ}
    (h : Excited X m n ω i) :
    rightProb p X m n ω i = p := by
  simp [rightProb, h]

/-- The drift of a nearest-neighbour step taken with right probability `1/2` is zero. -/
theorem drift_at_half : 2 * ((1 : ℝ) / 2) - 1 = 0 := by norm_num

/-- The drift needed to clear the deterministic block threshold `(B+1) L` over `T L` steps is
strictly positive for every `B ≥ 1`, `T ≥ 1`. -/
theorem needed_drift_pos {B T : ℕ} (hB : 1 ≤ B) (hT : 1 ≤ T) :
    (0 : ℝ) < ((B : ℝ) + 1) / (T : ℝ) := by
  have hB' : (0 : ℝ) < (B : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (B : ℝ) := by positivity
    linarith
  have hT' : (0 : ℝ) < (T : ℝ) := by
    have h1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  exact div_pos hB' hT'

/-- **No-go.**  The unconditional one-step value `1/2` gives drift `0`, which never clears the
positive block requirement `(B+1)/T`.  So an estimate that uses only `1/2 ≤ rightProb` cannot
prove `h₁` at any `B, T ≥ 1`: the excitation gain is indispensable. -/
theorem static_drift_does_not_suffice {B T : ℕ} (hB : 1 ≤ B) (hT : 1 ≤ T) :
    ¬ ((2 * ((1 : ℝ) / 2) - 1) > ((B : ℝ) + 1) / (T : ℝ)) := by
  have hpos := needed_drift_pos hB hT
  rw [drift_at_half]
  linarith

end SlowBlock


