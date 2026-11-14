/-
  **DIRECTION E (m5) — `JBudgetActual.lean`: the `(Jbound)` record-cost budget for the actual
  array, in the shape the occupation ledger consumes.**

  The occupation ledger `OccInterface.occupation_bound_actual` needs an eventual pathwise bound

      Jsum p m eps i j U T  <=  M U T + delta * T

  on the summed record cost `Jsum = sum_{t<T} Jcorr t`.  This file supplies that bound at the
  actual model, with the coefficient on the running maximum of walker `i` kept **explicit**
  (it is a deterministic function of `p, m, eps` and the environment's spatial statistic `K`,
  not of the walker count `N`).

  What is new here, and what is reused:

  * `hprevCap`, `bCap`, `wCap`: the paper's cap `b_n = h_j(M_n^j-1)+2` and the `(spav)` weight
    `9 h_j(M_n^j-1)^2` **as functions of the record value**, including the boundary
    `h_j(-1) = 1`.  `bRec_eq`: the actual `bRec p m n j U` is literally `bCap` evaluated at the
    running record `M_n^j`.  This is the index shift the earlier `Jbound*` statements left open
    (they take an abstract `b : ℕ → ℝ`).
  * `Jcorr_eq_Jinc`: the ledger's `Jcorr` **is** `SwarmJb.Jinc` at `a = aRec p m`, the actual
    cap `bCap`, walker `i`'s position and walker `j`'s running record.  Definitional after the
    two identifications above; no probability.
  * `runMax_le_succ`, `runMax_succ_le`, `recNat_*`: the actual running record is monotone with
    unit steps, which is the hypothesis `hmono`/`hstep` of the deterministic combinatorial
    `(Jbound)` `SwarmJb.Jsum_le_index`.
  * `exists_wCap_eventual`: the `(spav)` second-moment spatial average, at the *shifted* weight
    `9 h_j(x-1)^2`, transferred to the boundary-correct weight `wCap` (they differ only at
    `x = 0`, where `wCap 0 = 9 <= 9 h_j(0)^2`).
  * `Jinc_bound_all`, `Jsum_eventual`: **the eventual a.e. record-cost budget**

        sum_{t<T} |J_{t+1}|  <=  B * M_T^i + (1/64) T        eventually, a.s.

    with `B = 2 K / (eps (1-a)^2)` explicit, obtained from `SwarmSpatialSq.Jbound_runMax_eventual`
    plus the a.s. unboundedness of walker `i`'s running record
    (`ae_runMax_eventually_ge_all`, from `SwarmSpatial.ae_forall_walkers_trajectory_exists_ge`,
    which needs only `p ≥ 1/2`), which is what makes the record eventually pass the
    environment-dependent spatial threshold `R_0`.  The onset is necessarily
    environment-dependent, and that fact is *not* papered over: the statement is
    `∀ᵐ U, ∃ N_0, ∀ T ≥ N_0`.
  * `Jsum_eventual_one_eighth`: the same at `eps = 1/32`, `delta = 1/64`.
  * `occbnd_coef_ae`: the composite with the ledger at **abstract** coefficients `A` (for `Z`)
    and `B` (for `J`), producing `Occ T <= max 1 (A+B) * M_T^i + T/8` eventually a.s.

  An honest note on the interface.  `OccInterface.occupation_bound_one_eighth` carries the
  coefficient **1** on `M` for all three budgets, i.e. it needs `B <= 1`.  The paper's own
  `(Jbound)` constant is `C = C_eps * (spav constant)` with `C_eps = 1/(eps (1-a)^2)`; since
  `h_j >= 1` the spatial constant satisfies `K >= 9`, so at `eps = 1/32` the absolute-sum
  budget has coefficient `2 K/(eps (1-a)^2) >= 18/(eps) = 576 > 1`.  The paper therefore
  keeps the coefficient abstract and raises the final occupation constant to `C >= 1`
  ("increase `C` to at least 1"), which is exactly `SwarmJb.occbnd_coef` /
  `SwarmJb.speed_from_pieces_coef` with `kappa = 7/(40 C)`.  `Jsum_hJ_of_coef_le_one` records
  the (unavailable) numerical hypothesis that would be needed for the coefficient-`1` form, so
  that the gap is a named hypothesis rather than a silent weakening.  See `NOTE_coef_gap`
  below.

  No `sorry`, no `admit`, no custom axiom.  `paperWeight`/`HpotInc` conditional bounds and the
  correction-drift identity are *not* touched here.
-/
import Swarm.OccInterface
import Swarm.S15
import Swarm.SymmAeMax

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace JBudgetActual

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open VdriftAssembly

variable {N : ℕ}

/-! ## 1. The paper's cap `b_n = h_j(M_n^j - 1) + 2` as a function of the record

`bRec p m n j U` is defined from `HprevAt`, which reads the record value
`(recVal j (prefOf p m n U)).toNat`.  The deterministic `(Jbound)` of
`Swarm/JboundActual.lean` and `Swarm/S15.lean` is stated for an abstract
cap sequence `b : ℕ → ℝ` applied to the record.  The definitions below make the actual cap a
function of the record value, so that the two can be identified. -/

/-- `h_j(x-1)` at the record value `x`, with the paper's boundary convention `h_j(-1) = 1`.
This is exactly the paper's `b x = h_j(x-1) + 2` without the `+2`. -/
noncomputable def hprevCap (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) : ℝ :=
  if x = 0 then 1 else SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (x - 1)

/-- The paper's cap sequence `b x = h_j(x-1) + 2` (eq. `(hrec)`/`(Jbound)`). -/
noncomputable def bCap (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) : ℝ :=
  hprevCap p m U j x + 2

/-- The `(spav)` weight `w x = 9 h_j(x-1)^2` matching the cap: `b x ^ 2 <= w x`. -/
noncomputable def wCap (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) : ℝ :=
  9 * (hprevCap p m U j x) ^ 2

/-- `1 <= h_j(x-1)`: both branches of `(hrec)` give at least one, and the boundary value is
`1`.  This is the only property of `h_j` used for the cap algebra. -/
theorem one_le_hprevCap {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (U : Array N)
    (j : Fin N) (x : ℕ) : 1 ≤ hprevCap p m U j x := by
  unfold hprevCap
  split_ifs with hx
  · norm_num
  · exact SwarmMarks.one_le_hof hp0 hp1 (SwarmLogRatio.siteMarks p m U j) (x - 1)

/-- **`b x ^ 2 <= w x`** at the actual cap: `(h+2)^2 <= 9 h^2` for `h >= 1`. -/
theorem bCap_sq_le_wCap {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (U : Array N)
    (j : Fin N) (x : ℕ) : (bCap p m U j x) ^ 2 ≤ wCap p m U j x := by
  have h1 := one_le_hprevCap (N := N) hp0 hp1 m U j x
  simpa only [bCap, wCap] using SwarmJb.sq_add_two_le_nine_mul_sq h1

/-- The cap is nonnegative, hence `0 <= b x`. -/
theorem bCap_nonneg {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (U : Array N)
    (j : Fin N) (x : ℕ) : 0 ≤ bCap p m U j x := by
  have h1 := one_le_hprevCap (N := N) hp0 hp1 m U j x
  simp only [bCap]
  linarith

/-- The weight is nonnegative. -/
theorem wCap_nonneg (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) :
    0 ≤ wCap p m U j x := by
  unfold wCap
  positivity

/-- **The index shift**: the actual `HprevAt` is `hprevCap` evaluated at the running record. -/
theorem HprevAt_eq_hprevCap (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    HprevAt p m n j U = hprevCap p m U j ((runMax p m U j n).toNat) := by
  rw [HprevAt, ← runMax_eq_recVal (N := N) p m U j n]
  rfl

/-- **The actual cap is the generic cap sequence at the record**: `bRec = bCap ∘ M^j_n`. -/
theorem bRec_eq_bCap (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    bRec p m n j U = bCap p m U j ((runMax p m U j n).toNat) := by
  simp only [bRec, bCap, HprevAt_eq_hprevCap]

/-- The record cast: `M_n^j` is nonnegative, so its `toNat` cast back is `M_n^j`. -/
theorem cast_recNat (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) (t : ℕ) :
    (((runMax p m U j t).toNat : ℕ) : ℤ) = runMax p m U j t :=
  Int.toNat_of_nonneg (zero_le_runMax p m U j t)

/-! ## 2. The actual running record is monotone with unit steps -/

/-- Walker `i`'s actual step is at most `+1` (`drivenStep` is `±1`). -/
theorem pos_succ_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (t : ℕ) :
    (trajectory p m U (t + 1)).pos i ≤ (trajectory p m U t).pos i + 1 := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  unfold drivenStep
  split_ifs <;> simp

/-- The record of walker `j` as a `SwarmSpeed.runMax`.  Definitional. -/
theorem runMax_eq_speedRunMax (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n = SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) n := rfl

/-- The running record of walker `j` is nondecreasing. -/
theorem runMax_le_succ (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    runMax p m U j t ≤ runMax p m U j (t + 1) := by
  have h : SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) t
      ≤ SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) (t + 1) :=
    SwarmSpeed.runMax_mono _ (Nat.le_succ t)
  simpa only [runMax_eq_speedRunMax] using h

/-- Walker `j`'s running maximum increases by at most one per step. -/
theorem speedRunMax_succ_le (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) (t + 1)
      ≤ SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) t + 1 := by
  refine SwarmSpeed.runMax_le (u := fun s => (trajectory p m U s).pos j) fun s hs => ?_
  rcases Nat.lt_or_ge s (t + 1) with hlt | hge
  · have h1 : (trajectory p m U s).pos j
        ≤ SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) t :=
      SwarmSpeed.le_runMax (u := fun s => (trajectory p m U s).pos j) (t := s) (n := t)
        (by omega)
    linarith
  · have hse : s = t + 1 := by omega
    subst hse
    have h1 : (trajectory p m U t).pos j
        ≤ SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j) t :=
      SwarmSpeed.le_runMax (u := fun s => (trajectory p m U s).pos j) (t := t) (n := t) le_rfl
    have h2 := pos_succ_le p m U j t
    linarith

/-- The running record of walker `j` increases by at most one per step. -/
theorem runMax_succ_le (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    runMax p m U j (t + 1) ≤ runMax p m U j t + 1 := by
  have h := speedRunMax_succ_le p m U j t
  simpa only [runMax_eq_speedRunMax] using h

/-- The natural-number record `(M_t^j).toNat` is nondecreasing. -/
theorem recNat_le_succ (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    (runMax p m U j t).toNat ≤ (runMax p m U j (t + 1)).toNat :=
  Int.toNat_le_toNat (runMax_le_succ p m U j t)

/-- The natural-number record increases by at most one. -/
theorem recNat_succ_le (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    (runMax p m U j (t + 1)).toNat ≤ (runMax p m U j t).toNat + 1 := by
  have h := Int.toNat_le_toNat (runMax_succ_le p m U j t)
  have hnn := zero_le_runMax p m U j t
  have hcast : ((runMax p m U j t + 1).toNat) = (runMax p m U j t).toNat + 1 := by
    have h3 : ((runMax p m U j t).toNat : ℤ) = runMax p m U j t := Int.toNat_of_nonneg hnn
    have h4 : (((runMax p m U j t).toNat + 1 : ℕ) : ℤ) = runMax p m U j t + 1 := by
      push_cast
      omega
    have h5 := Int.toNat_of_nonneg (a := runMax p m U j t + 1) (by linarith)
    omega
  rw [hcast] at h
  exact h

/-! ## 3. The ledger's `Jcorr` is the paper's `Jinc` at the actual data -/

/-- **`Jcorr` is `SwarmJb.Jinc`.**  The ledger's `J_{t+1}` written with `bRec`, the actual
trajectory of walker `i`, and walker `j`'s running record agrees definitionally with the
deterministic `(Jbound)` object `Jinc` at `a = aRec p m` and the cap sequence `bCap`. -/
theorem Jcorr_eq_Jinc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    Jcorr p m eps i j U t =
      SwarmJb.Jinc (aRec p m) eps (bCap p m U j)
        (fun s => (trajectory p m U s).pos i) (fun s => (runMax p m U j s).toNat) t := by
  simp only [SwarmJb.Jinc, Jcorr, bRec_eq_bCap, cast_recNat]

/-- The record cost sum is at most the sum of absolute record costs. -/
theorem Jsum_le_abs_sum (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) :
    Jsum p m eps i j U T
      ≤ ∑ t ∈ Finset.range T, |Jcorr p m eps i j U t| := by
  unfold Jsum
  exact Finset.sum_le_sum fun t _ => le_abs_self _

open VdriftAssembly

/-! ## 4. The `(spav)` second-moment spatial average at the boundary-correct weight

`Swarm/S15.lean` proves the eventual linear spatial bound for the *shifted* weight
`x ↦ 9 h_j(x-1)^2`.  The cap sequence actually used by the ledger differs from that at the single
index `x = 0`, where the paper's boundary convention is `h_j(-1) = 1` rather than `h_j(0)`.  Since
`h_j >= 1`, the boundary-correct weight is pointwise at most the shifted one, so the same `K` and
the same threshold `R_0` work. -/

theorem wCap_le_shifted {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (U : Array N)
    (j : Fin N) (x : ℕ) :
    wCap p m U j x
      ≤ 9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (x - 1)) ^ 2 := by
  unfold wCap hprevCap
  split_ifs with hx
  · subst hx
    have h1 : (1 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (0 - 1) :=
      SwarmMarks.one_le_hof hp0 hp1 (SwarmLogRatio.siteMarks p m U j) (0 - 1)
    have h0 : (0 - 1 : ℕ) = 0 := rfl
    rw [h0]
    nlinarith [h1]
  · exact le_rfl

/-- **`(spav)` in the form the record-cost estimate needs.**  There is a deterministic constant
`K = K(p,m,N) > 0`, independent of the walker family and of `eps`, and for almost every array and
every walker `j` an environment-dependent spatial threshold `R_0` such that
`sum_{x<r} wCap x <= K r` for all `r >= R_0`. -/
theorem exists_wCap_eventual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, ∃ R₀ : ℕ,
      ∀ r ≥ R₀, ∑ x ∈ Finset.range r, wCap p m U j x ≤ K * (r : ℝ) := by
  obtain ⟨K, hKpos, hU⟩ :=
    SwarmSpatialSq.exists_shifted_sq_linear_bound_array (N := N) hp0 hp1 hm
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [hU] with U hU j
  obtain ⟨R₀, hR₀⟩ := hU j
  refine ⟨R₀, fun r hr => ?_⟩
  have hle := Finset.sum_le_sum (fun x (_ : x ∈ Finset.range r) =>
    wCap_le_shifted (N := N) hp0.le hp1 m U j x)
  have hshift : (∑ x ∈ Finset.range r,
        9 * (SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2)
      ≤ K * (r : ℝ) := hR₀ r hr
  refine le_trans hle ?_
  simpa only [SwarmLogRatio.siteMarksN] using hshift

/-- **The `(spav)` constant is at least `9`.**  `wCap x >= 9` pointwise (`h_j >= 1`), so any `K`
that dominates the spatial average linearly at a positive index satisfies `K >= 9`.  This is the
deterministic reason why the coefficient-`1` interface of
`OccInterface.occupation_bound_one_eighth` cannot be met by the paper's `(Jbound)` route; see
`NOTE_coef_gap`. -/
theorem nine_le_of_wCap_bound {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (U : Array N) (j : Fin N) {K : ℝ} {R₀ : ℕ}
    (h : ∀ r ≥ R₀, ∑ x ∈ Finset.range r, wCap p m U j x ≤ K * (r : ℝ)) :
    9 ≤ K := by
  have hnine : ∀ x : ℕ, 9 ≤ wCap p m U j x := by
    intro x
    unfold wCap
    have h1 : (1 : ℝ) ≤ hprevCap p m U j x := one_le_hprevCap hp0 hp1 m U j x
    nlinarith [h1]
  set r : ℕ := max R₀ 1 with hrdef
  have hrR₀ : R₀ ≤ r := le_max_left _ _
  have hr1 : 0 < r := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hsum : (9 : ℝ) * (r : ℝ) ≤ ∑ x ∈ Finset.range r, wCap p m U j x := by
    have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.range r) => hnine x)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using h
  have hcast : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have h2 := h r hrR₀
  nlinarith [hsum, h2, hcast]

/-! ## 4'. Every walker's running record passes every level almost surely

The record-cost budget needs only `M_T^i -> infinity`, not `X_T^i -> +infinity`.  Accordingly the
almost-sure unboundedness of the actual trajectory (`Swarming.SymmAeMax`, which needs only
`p >= 1/2`) suffices, and **no distinctness of `i` and `j` is required**. -/

theorem ae_runMax_eventually_ge_all {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ b : ℕ, ∃ N : ℕ,
      ∀ n ≥ N, b ≤ (runMax p m U i n).toNat := by
  filter_upwards [Swarming.SymmAeMax.ae_forall_walkers_trajectory_exists_ge (N := N) (p := p) hp m]
    with U hU i b
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hU i b)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, hbk⟩ := hN n hn
  have h1 : (b : ℤ) ≤ runMax p m U i n := by
    rw [runMax_eq_speedRunMax (j := i) (n := n)]
    exact le_trans hbk
      (SwarmSpeed.le_runMax (u := fun s => (trajectory p m U s).pos i) (t := k) (n := n) hk)
  have h2 : ((b : ℤ)).toNat ≤ (runMax p m U i n).toNat := Int.toNat_le_toNat h1
  have h3 : ((b : ℤ)).toNat = b := Int.toNat_natCast b
  omega

/-! ## 5. The eventual record-cost budget on the actual array -/

/-- **`(Jbound)` for the actual array, absolute-sum form, with an explicit coefficient and an
explicit environment-dependent onset.**

There is a constant `B > 0`, a deterministic function of `p, m, eps` (through the `(spav)`
constant `K` only), such that almost surely, for all sufficiently large `T`,

    sum_{t<T} |J_{t+1}|  <=  B * M_T^i + T/64,

where `M_T^i` is walker `i`'s actual running maximum.  The onset depends on the array through
the spatial threshold `R_0` of walker `j`'s mark sequence; this is unavoidable, because `(spav)`
is only an eventual statement.  Almost-sure unboundedness of walker `i`'s running record
(`ae_runMax_eventually_ge_all`) is what guarantees that `M_T^i` eventually exceeds `R_0`; it
needs only `p ≥ 1/2`, so no distinctness of `i` and `j` is required. -/
theorem abs_Jcorr_sum_eventual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      (∑ t ∈ Finset.range T, |Jcorr p m eps i j U t|)
        ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ) := by
  obtain ⟨K, hKpos, hU⟩ := exists_wCap_eventual (N := N) hp0 hp1 hm
  have hq : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have haa := ExcitedEnv.aConst_bounds hp0 hp1 hq (ExcitedEnv.q_le_half hp0 hp1 hm)
  have ha0 : 0 ≤ aRec p m := by
    have h := haa.1
    simp only [aRec]
    linarith
  have ha1 : aRec p m < 1 := by
    simpa only [aRec] using haa.2.1
  have h1ma : (0 : ℝ) < 1 - aRec p m := by linarith
  refine ⟨2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K, by positivity, ?_⟩
  filter_upwards [hU, ae_runMax_eventually_ge_all (N := N) hp0.le m] with U hUj hlev
  obtain ⟨R₀, hR₀⟩ := hUj j
  obtain ⟨N₁, hN₁⟩ := hlev i R₀
  refine ⟨max N₁ ⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊, fun T hT => ?_⟩
  have hTN₁ : N₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTceil : ⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊ ≤ T :=
    le_trans (le_max_right _ _) hT
  -- walker `i`'s running maximum has passed the spatial threshold
  have hM : R₀ ≤ max 0 (SwarmSpeed.runMax (fun s => (trajectory p m U s).pos i) T).toNat := by
    rw [← runMax_eq_speedRunMax (N := N) p m U i T]
    have hmax : max 0 (runMax p m U i T).toNat = (runMax p m U i T).toNat :=
      Nat.max_eq_right (Nat.zero_le _)
    rw [hmax]
    exact hN₁ T hTN₁
  have hb : ∀ x : ℕ, 0 ≤ bCap p m U j x := fun x => bCap_nonneg hp0.le hp1 m U j x
  have hw : ∀ x : ℕ, 0 ≤ wCap p m U j x := fun x => wCap_nonneg p m U j x
  have hbw : ∀ x : ℕ, (bCap p m U j x) ^ 2 ≤ wCap p m U j x :=
    fun x => bCap_sq_le_wCap hp0.le hp1 m U j x
  have hmono : ∀ t : ℕ, (runMax p m U j t).toNat ≤ (runMax p m U j (t + 1)).toNat :=
    fun t => recNat_le_succ p m U j t
  have hstep : ∀ t : ℕ, (runMax p m U j (t + 1)).toNat ≤ (runMax p m U j t).toNat + 1 :=
    fun t => recNat_succ_le p m U j t
  have hbound := SwarmSpatialSq.Jbound_runMax_eventual (a := aRec p m) (ε := eps)
    ha0 ha1 hε hb hw hbw hmono hstep (K := K) (R₀ := R₀) hR₀ T hM
  have hsum : (∑ t ∈ Finset.range T, |Jcorr p m eps i j U t|)
      = ∑ t ∈ Finset.range T, |SwarmJb.Jinc (aRec p m) eps (bCap p m U j)
          (fun s => (trajectory p m U s).pos i) (fun s => (runMax p m U j s).toNat) t| := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Jcorr_eq_Jinc]
  rw [hsum]
  have hz : (0 : ℝ) ≤ (((runMax p m U i T : ℤ)) : ℝ) := by
    have h := zero_le_runMax p m U i T
    exact_mod_cast h
  have hmax2 : max 0 (((SwarmSpeed.runMax (fun s => (trajectory p m U s).pos i) T : ℤ)) : ℝ)
      = (((runMax p m U i T : ℤ)) : ℝ) := by
    rw [← runMax_eq_speedRunMax (N := N) p m U i T]
    exact max_eq_right hz
  rw [hmax2] at hbound
  have hBle : 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K ≤ (1 / 64) * (T : ℝ) := by
    have h1 : 64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K) ≤ (⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈64 * (2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K)⌉₊ : ℕ) : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast hTceil
    linarith
  calc (∑ t ∈ Finset.range T, |SwarmJb.Jinc (aRec p m) eps (bCap p m U j)
          (fun s => (trajectory p m U s).pos i) (fun s => (runMax p m U j s).toNat) t|)
      ≤ 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K
          * ((((runMax p m U i T : ℤ)) : ℝ) + 1) :=
        hbound
    _ = 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K * (((runMax p m U i T : ℤ)) : ℝ)
          + 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K := by
        ring
    _ ≤ 2 * (1 / (eps * (1 - aRec p m) ^ 2)) * K * (((runMax p m U i T : ℤ)) : ℝ)
          + (1 / 64) * (T : ℝ) := by
        linarith

/-- **The `Jsum` record-cost budget at `eps = 1/32`, `delta = 1/64`** — the constants of the
occupation assembly.  This is the `hJ` premise of `OccInterface.occupation_bound_one_eighth`,
with the coefficient on `M_T^i` left explicit (see `NOTE_coef_gap`). -/
theorem Jsum_eventual_one_eighth {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 32) i j U T ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ) := by
  obtain ⟨B, hBpos, hU⟩ :=
    abs_Jcorr_sum_eventual (N := N) hp0 hp1 hm (i := i) (j := j) (eps := 1 / 32) (by norm_num)
  refine ⟨B, hBpos, ?_⟩
  filter_upwards [hU] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  exact ⟨N₀, fun T hT => le_trans (Jsum_le_abs_sum p m (1 / 32) i j U T) (hN₀ T hT)⟩

/-- **The `Jsum` budget at a general `eps > 0`** (`delta = 1/64`).  Corollary of the
absolute-sum form; this is the shape needed by any consumer that does not use `eps = 1/32`. -/
theorem Jsum_eventual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m eps i j U T ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ) := by
  obtain ⟨B, hBpos, hU⟩ := abs_Jcorr_sum_eventual (N := N) hp0 hp1 hm (i := i) (j := j) hε
  exact ⟨B, hBpos, hU.mono fun U hU => by
    obtain ⟨N₀, hN₀⟩ := hU
    exact ⟨N₀, fun T hT => le_trans (Jsum_le_abs_sum p m eps i j U T) (hN₀ T hT)⟩⟩

/-! ## 6. The numerical gap in the coefficient-`1` interface (`NOTE_coef_gap`)

`OccInterface.occupation_bound_one_eighth` uses the coefficient `1` on `M` for all three budgets,
so it requires the `(Jbound)` coefficient to be `<= 1`.  The paper's `(Jbound)` coefficient is
`C = C_eps * K` with `C_eps = 1/(eps (1-a)^2)` and `K >= 9` (because `h_j >= 1`), hence at
`eps = 1/32` it is at least `576`.  The coefficient-`1` form is therefore *not* what the paper
proves; the paper keeps `C` abstract and raises the final occupation constant to `C >= 1`
(`SwarmJb.occbnd_coef`, `SwarmJb.speed_from_pieces_coef`, `kappa = 7/(40 C)`).  The two lemmas
below state this precisely. -/

/-- Arithmetic: the total `(Jbound)` coefficient `2 K/(eps (1-a)^2)` is at least `18/eps`. -/
theorem eighteen_div_eps_le_coef {a eps K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < eps)
    (hK : 9 ≤ K) : 18 / eps ≤ 2 * (1 / (eps * (1 - a) ^ 2)) * K := by
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (1 - a) ^ 2 ≤ 1 := by nlinarith
  have h3 : (0 : ℝ) < (1 - a) ^ 2 := by positivity
  have h4 : (1 : ℝ) ≤ 1 / (1 - a) ^ 2 := by
    rw [le_div_iff₀ h3]
    simpa using h2
  have h5 : (1 : ℝ) / (eps * (1 - a) ^ 2) = (1 / eps) * (1 / (1 - a) ^ 2) := by
    field_simp
  have h6 : (0 : ℝ) < 1 / eps := by positivity
  have h7 : 1 / eps ≤ 1 / (eps * (1 - a) ^ 2) := by
    rw [h5]
    nlinarith [h4, h6]
  have h8 : (1 / eps) * 9 ≤ (1 / (eps * (1 - a) ^ 2)) * K :=
    mul_le_mul h7 hK (by norm_num) (by positivity)
  have h9 : (18 : ℝ) / eps = 2 * ((1 / eps) * 9) := by ring
  rw [h9]
  linarith [h8]

/-- **The `(Jbound)` coefficient cannot be `<= 1` at `eps = 1/32`.**  Any `K` dominating the
spatial average (`K >= 9`) gives coefficient `>= 576`. -/
theorem coef_gap_one_eighth {a K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 9 ≤ K) :
    ¬ (2 * (1 / ((1 / 32 : ℝ) * (1 - a) ^ 2)) * K ≤ 1) := by
  have h := eighteen_div_eps_le_coef ha0 ha1 (by norm_num : (0 : ℝ) < 1 / 32) hK
  have h1 : (18 : ℝ) / (1 / 32) = 576 := by norm_num
  rw [h1] at h
  intro hle
  linarith

/-- The coefficient-`1` form of `hJ`, under the (unavailable) hypothesis `B <= 1`.  This records
exactly what the coefficient-`1` interface needs. -/
theorem hJ_coef_one_of_le_one {p : ℝ} (m : ℕ) {eps : ℝ} {i j : Fin N} {B : ℝ} (hB1 : B ≤ 1)
    {M : Array N → ℕ → ℝ} (hM : ∀ U n, 0 ≤ M U n) :
    (∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        Jsum p m eps i j U T ≤ B * M U T + (1 / 64) * (T : ℝ)) →
      ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        Jsum p m eps i j U T ≤ M U T + (1 / 64) * (T : ℝ) := by
  intro h
  filter_upwards [h] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  refine ⟨N₀, fun T hT => ?_⟩
  have h1 := hN₀ T hT
  have h2 : B * M U T ≤ 1 * M U T := by
    exact mul_le_mul_of_nonneg_right hB1 (hM U T)
  linarith

/-! ## 7. Composition with the ledger at abstract coefficients (the correct interface)

`OccInterface.occupation_bound_one_eighth` fixes the coefficient `1` for all three budgets.  The
paper's route keeps the coefficients abstract (`SwarmJb.occbnd_coef`) and raises the final
occupation constant.  The theorem below is that interface in the **a.e.-onset** form that the
actual budgets have: the three budgets and the one-step `enlFilt` bound are all that is used. -/

theorem occbnd_coef_ae {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {A B : ℝ}
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zpot p m (1 / 32) i j U T ≤ A * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 32) i j U T ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      occSum p m i j U T ≤ max 1 (A + B) * (((runMax p m U i T : ℤ)) : ℝ)
        + (1 / 8) * (T : ℝ) := by
  have hdrift : ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      occSum p m i j U n
        ≤ (1 / 32) * (n : ℝ) + (Zpot p m (1 / 32) i j U n - Zpot p m (1 / 32) i j U 0)
          + Jsum p m (1 / 32) i j U n
          - Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U n := by
    filter_upwards [oneStep_all hp0 hp1 (by norm_num : (0 : ℝ) < 1 / 32)
      (fun t U => one_half_le_alphaFun hp0 hp1 m t i U) hAB] with U hall
    intro n
    exact ledger_pointwise p m (1 / 32) (fun t => alphaFun p m t i) i j U hall n
  filter_upwards [hdrift, hZ, hJ, hQ] with U hd hZl hJl hQl
  obtain ⟨NZ, hNZ⟩ := hZl
  obtain ⟨NJ, hNJ⟩ := hJl
  obtain ⟨NQ, hNQ⟩ := hQl
  refine ⟨max (max (max NZ NJ) NQ) ⌈64 * max 0 (-(Zpot p m (1 / 32) i j U 0))⌉₊,
    fun T hT => ?_⟩
  have hN : max (max NZ NJ) NQ ≤ T := le_trans (le_max_left _ _) hT
  refine SwarmJb.occbnd_coef (Occ := fun n => occSum p m i j U n)
    (Z := fun n => Zpot p m (1 / 32) i j U n)
    (J := fun n => Jsum p m (1 / 32) i j U n)
    (Q := fun n => Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U n)
    (M := fun n => (((runMax p m U i n : ℤ)) : ℝ)) (A := A) (B := B)
    (N := max (max NZ NJ) NQ)
    (fun n => by
      have h := zero_le_runMax p m U i n
      exact_mod_cast h)
    hd
    (fun n hn => hNZ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn))
    (fun n hn => hNJ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn))
    (fun n hn => hNQ n (le_trans (le_max_right _ _) hn)) T ?_
  exact max_le hN (le_trans (le_max_right _ _) hT)

/-- **The conditional reduction**: with the `Z` budget at coefficient `A` and the `Q` budget
`-(T/64) <= Q_T` — and with the one-step `enlFilt` bound `hAB` — the `J` budget proved here
discharges the `J` premise of the occupation assembly, giving

    Occ T <= max 1 (A + B) * M_T^i + T/8     eventually, a.s.

with `B` the explicit `(Jbound)` coefficient of `Jsum_eventual_one_eighth`.  The two remaining
premises are exactly the `(Vbound)` budget on `Zpot` and the strong-law lower bound on `Qcomp`
(the paper's `Q_n = o(n)`); neither is claimed here. -/
theorem occupation_bound_with_Jbudget {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} {A : ℝ}
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zpot p m (1 / 32) i j U T ≤ A * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U T) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      occSum p m i j U T ≤ max 1 (A + B) * (((runMax p m U i T : ℤ)) : ℝ)
        + (1 / 8) * (T : ℝ) := by
  obtain ⟨B, hBpos, hJ⟩ := Jsum_eventual_one_eighth (N := N) hp0 hp1 hm (i := i) (j := j)
  exact ⟨B, hBpos, occbnd_coef_ae hp0 hp1 hAB hZ hJ hQ⟩

/-- **Consistency with the integrated coefficient-`1` occupation bound.**  When both budgets
happen to hold with coefficient at most `1`, the abstract-coefficient assembly reproduces the
conclusion of `OccInterface.occupation_bound_one_eighth`
(`occSum <= 2 * M_T^i + T/8`), only with an environment-dependent onset.  This is a shape check:
it shows that the a.e.-onset interface is the coefficient-`1` interface plus two honest
hypotheses (`A <= 1`, `B <= 1`), which `coef_gap_one_eighth` shows the `J` budget cannot meet. -/
theorem occbnd_two_of_coef_le_one {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {A B : ℝ} (hA : A ≤ 1) (hB : B ≤ 1)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zpot p m (1 / 32) i j U T ≤ A * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 32) i j U T ≤ B * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      occSum p m i j U T ≤ 2 * (((runMax p m U i T : ℤ)) : ℝ) + (1 / 8) * (T : ℝ) := by
  filter_upwards [occbnd_coef_ae hp0 hp1 hAB hZ hJ hQ] with U hU
  obtain ⟨N₀, hN₀⟩ := hU
  refine ⟨N₀, fun T hT => ?_⟩
  have hM : (0 : ℝ) ≤ (((runMax p m U i T : ℤ)) : ℝ) := by
    have h := zero_le_runMax p m U i T
    exact_mod_cast h
  have h2 : max 1 (A + B) ≤ 2 := by
    refine max_le (by norm_num) ?_
    linarith
  have h3 : max 1 (A + B) * (((runMax p m U i T : ℤ)) : ℝ)
      ≤ 2 * (((runMax p m U i T : ℤ)) : ℝ) :=
    mul_le_mul_of_nonneg_right h2 hM
  linarith [hN₀ T hT]

end JBudgetActual
end Swarming.Enl
