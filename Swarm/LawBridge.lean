/-
# The stopped-record path-law identification, reduced to the joint `(defect, record time)` law

`areas/tightness/ScaleRepairRecord.probCtxRT` fixes `B`, `C₀`, `T` and then asks for the `hterm`
field on the Ionescu–Tulcea path law `recordTrajT p hp hp1 hm ν` of the stopped record kernel.
`areas/recordo` proves the corresponding block statement for the *array's own* record data, and
`SCALE_REPAIR.md` lists as a separate open premise the "actual record-path law identification"
(the `hlaw` of `areas/recordo/README.md`).

This file isolates that premise in the smallest form that actually feeds the tightness route.
Observe that `GoodT B C₀ T ω r L` of `ProbCtxRecord.lean` is, verbatim, a predicate on the two
numeric sequences

  `r ↦ dT ω r`  (the paper's `d_r = max_i d_i(ω r)`)   and   `r ↦ tauT ω r`  (the paper's `τ_r`),

namely `GoodSeq` below.  Consequently the identification needed for `hterm` is only the equality
of the **joint laws of these two sequences**,

  `hlaw : (recordTrajT …).map (fun ω => (dT ω, tauT ω))
            = (arrayMeasure N).map (fun U => (d-law U, τ-law U))`,

not the full record-state law.  (The full identification implies it; it does *not* require the
`RecState`-valued extraction map to be constructed.)

Main declarations:

* `GoodSeq`, `goodT_iff_goodSeq` — `GoodT` is a predicate on `(d, τ)` sequences.
* `goodBlock_iff_goodSeq` — the array's `GoodBlock` is the same predicate on
  `(fun r => (defect … r).toNat, τ)`.
* `hterm_transfer` — a measurable transfer of an almost-sure block statement along an equality of
  laws of sequence-valued statistics.
* `hterm_pathlaw_of_array` — the `hterm` field of `probCtxRT` at the **fixed** constants
  `T = ⌈2B/κ⌉+2`, `C₀ = B+T+1`, from (i) the array-side `hterm` (`ActualHterm.hterm_actual_fixed`),
  (ii) `(diam)`, and (iii) `hlaw`.

Residual technical hypothesis: measurability of the array's `(defect, record time)` statistic.
It is the only non-probabilistic input; the route to it is `Swarming.Fair.measurable_trajectory`
for the positions plus measurability of the fibres of the `Nat.find` record time.  This file does
not prove that measurability, and it does not prove `hlaw` itself.
-/
import Swarm.ActualHterm
import Swarm.ProbCtxRecord

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SwarmM4C

namespace LawBridge

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec SwarmM4C.FixedConst

/-! ### The paper's block predicate as a predicate on `(d, τ)` sequences -/

/-- The three block inequalities as a predicate on the two numeric sequences
`(defects, record times)`.  This is `GoodT` with its two statistic components separated. -/
def GoodSeq (B C₀ T : ℕ) (d τ : ℕ → ℕ) (r L : ℕ) : Prop :=
  (τ (r + B * L) ≤ τ r + T * L) ∧
  (d (r + B * L) ≤ L / 2) ∧
  (∀ u : ℕ, r ≤ u → u ≤ r + B * L → d u ≤ C₀ * L)

/-- `GoodT` is literally `GoodSeq` applied to the record-distance and record-time sequences. -/
theorem goodT_iff_goodSeq {N m : ℕ} (B C₀ T r L : ℕ) (ω : ℕ → RecState N m × ℕ) :
    GoodT B C₀ T ω r L ↔ GoodSeq B C₀ T (dT ω) (tauT ω) r L :=
  Iff.rfl

/-- The array's `GoodBlock` (integer defect) is the same predicate on the natural-valued defect
sequence and the record times. -/
theorem goodBlock_iff_goodSeq {d : ℕ → ℤ} (hd : ∀ r : ℕ, 0 ≤ d r) {τ : ℕ → ℕ}
    {T C₀ B r L : ℕ} :
    RecordoSupply.GoodBlock d τ T C₀ B r L ↔
      GoodSeq B C₀ T (fun u => (d u).toNat) τ r L := by
  unfold RecordoSupply.GoodBlock GoodSeq
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.sub_le_iff_le_add] at h1
      omega
    · show (d (r + B * L)).toNat ≤ L / 2
      have hc : ((2 * (d (r + B * L)).toNat : ℕ) : ℤ) ≤ (L : ℤ) := by
        push_cast
        rwa [Int.toNat_of_nonneg (hd _)]
      have hnat : 2 * (d (r + B * L)).toNat ≤ L := by exact_mod_cast hc
      omega
    · intro u hu1 hu2
      show (d u).toNat ≤ C₀ * L
      have hle := h3 u hu1 hu2
      have hc : ((d u).toNat : ℤ) ≤ ((C₀ * L : ℕ) : ℤ) := by
        push_cast
        rwa [Int.toNat_of_nonneg (hd u)]
      exact_mod_cast hc
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.sub_le_iff_le_add]
      omega
    · show 2 * d (r + B * L) ≤ (L : ℤ)
      have h2' : (d (r + B * L)).toNat ≤ L / 2 := h2
      have hnat : 2 * (d (r + B * L)).toNat ≤ L := by omega
      have hc : ((2 * (d (r + B * L)).toNat : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast hnat
      push_cast at hc
      rwa [Int.toNat_of_nonneg (hd _)] at hc
    · intro u hu1 hu2
      show d u ≤ (C₀ : ℤ) * (L : ℤ)
      have hle := h3 u hu1 hu2
      have hc : ((d u).toNat : ℤ) ≤ ((C₀ * L : ℕ) : ℤ) := by
        show ((d u).toNat : ℤ) ≤ ((C₀ * L : ℕ) : ℤ)
        exact_mod_cast hle
      push_cast at hc
      rwa [Int.toNat_of_nonneg (hd u)] at hc

/-! ### Measurability of the block predicate on sequence space -/

theorem measurableSet_goodSeq (B C₀ T r L : ℕ) :
    MeasurableSet {p : (ℕ → ℕ) × (ℕ → ℕ) | GoodSeq B C₀ T p.1 p.2 r L} := by
  have hcomp : ∀ k : ℕ, Measurable fun p : (ℕ → ℕ) × (ℕ → ℕ) => p.1 k :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hcomp2 : ∀ k : ℕ, Measurable fun p : (ℕ → ℕ) × (ℕ → ℕ) => p.2 k :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  simp only [GoodSeq, Set.ofPred_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le (hcomp2 _) ((hcomp2 _).add_const (T * L))
  · exact measurableSet_le (hcomp _) measurable_const
  · have hEq : {p : (ℕ → ℕ) × (ℕ → ℕ) |
        ∀ u : ℕ, r ≤ u → u ≤ r + B * L → p.1 u ≤ C₀ * L}
        = ⋂ u ∈ (Finset.Icc r (r + B * L) : Finset ℕ),
            {p : (ℕ → ℕ) × (ℕ → ℕ) | p.1 u ≤ C₀ * L} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc, and_imp]
    rw [hEq]
    exact MeasurableSet.biInter (Finset.countable_toSet _)
      (fun u _ => measurableSet_le (hcomp u) measurable_const)

theorem measurableSet_goodSeq_exists (B C₀ T r L : ℕ) :
    MeasurableSet {p : (ℕ → ℕ) × (ℕ → ℕ) | ∃ j : ℕ, GoodSeq B C₀ T p.1 p.2 r (2 ^ j * L)} := by
  have hEq : {p : (ℕ → ℕ) × (ℕ → ℕ) | ∃ j : ℕ, GoodSeq B C₀ T p.1 p.2 r (2 ^ j * L)}
      = ⋃ j : ℕ, {p : (ℕ → ℕ) × (ℕ → ℕ) | GoodSeq B C₀ T p.1 p.2 r (2 ^ j * L)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hEq]
  exact MeasurableSet.iUnion fun j => measurableSet_goodSeq B C₀ T r (2 ^ j * L)

/-! ### Transferring an almost-sure block statement along an equality of laws -/

/-- **Law transfer.**  If the law of the sequence-valued statistic `s` (on the target space)
equals the law of `s'` (on the source space), and `s'` satisfies the block statement almost
surely on the source, then `s` does so on the target.  `μ` is the source (array) measure and `ν`
the target (path) measure. -/
theorem hterm_transfer {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (ν : Measure Ω') (μ : Measure Ω) (s : Ω' → (ℕ → ℕ) × (ℕ → ℕ))
    (s' : Ω → (ℕ → ℕ) × (ℕ → ℕ)) (hs : Measurable s) (hs' : Measurable s')
    {B C₀ T : ℕ} (hlaw : ν.map s = μ.map s')
    (hterm' : ∀ᵐ x ∂μ, ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ, GoodSeq B C₀ T (s' x).1 (s' x).2 r (2 ^ j * L)) :
    ∀ r L : ℕ, 1 ≤ L → ∀ᵐ y ∂ν, ∃ j : ℕ, GoodSeq B C₀ T (s y).1 (s y).2 r (2 ^ j * L) := by
  intro r L hL
  have h1 : ∀ᵐ x ∂μ, ∃ j : ℕ, GoodSeq B C₀ T (s' x).1 (s' x).2 r (2 ^ j * L) := by
    filter_upwards [hterm'] with x hx
    exact hx r L hL
  have h2 : ∀ᵐ z ∂(μ.map s'), ∃ j : ℕ, GoodSeq B C₀ T z.1 z.2 r (2 ^ j * L) :=
    (ae_map_iff hs'.aemeasurable (measurableSet_goodSeq_exists B C₀ T r L)).2 h1
  have h3 : ∀ᵐ z ∂(ν.map s), ∃ j : ℕ, GoodSeq B C₀ T z.1 z.2 r (2 ^ j * L) := by
    rw [hlaw]
    exact h2
  exact ae_of_ae_map hs.aemeasurable h3

/-! ### The `hterm` field of `probCtxRT` at fixed constants -/

/-- **The `hterm` field of the repaired interface, on the stopped-record path law, at fixed
model constants.**

Given
* a fixed ballistic slope `κ` and the array's one-walker speed bound at that slope,
* a record map `U ↦ τf U` which is almost surely a record sequence,
* the diameter estimate `(diam)`,
* measurability of the array statistic `U ↦ ((d_r(U))_r, (τ_r(U))_r)`,
* and the joint-law identification `hlaw` of the `(defect, record time)` sequences,

the path law `recordTrajT p hp hp1 hm ν` satisfies

  `∀ r L ≥ 1, ∀ᵐ ω, ∃ j, GoodT B C₀ T ω r (2^j L)`

with `T = ⌈2B/κ⌉ + 2` and `C₀ = B + T + 1`, which depend only on `p, m, B`. -/
theorem hterm_pathlaw_of_array {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) [Nonempty (Fin N)] (_hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (τf : Swarming.Uniform.Array N → ℕ → ℕ)
    (hτf : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (τf U))
    (hmeasSeq : Measurable fun U : Swarming.Uniform.Array N =>
      (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν).map (fun ω => (dT ω, tauT ω))
      = (Swarming.Uniform.arrayMeasure N).map
          (fun U => (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U))) :
    ∀ r L : ℕ, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
      GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L) := by
  classical
  -- the array-side block statement, at the fixed constants
  have harr : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ,
      RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U) (⌈2 * (B : ℝ) / κ⌉₊ + 2)
        (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L) := by
    filter_upwards [hspeed, hτf, hdiam] with U hU hτ hspread
    intro r L hL
    have hspd := hU (Classical.arbitrary (Fin N))
    exact hterm_fixed hτ (actX_step p m U) (actX_zero p m U) hκ hspd
      (defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd hspread)
      B hB r L hL
  -- rewrite it as a block statement for the natural-valued sequence statistic
  have harr' : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ,
      GoodSeq B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2)
        (fun r => (defect (actX p m U) (τf U) r).toNat) (τf U) r (2 ^ j * L) := by
    filter_upwards [harr, hτf] with U hU hτ r L hL
    obtain ⟨j, hj⟩ := hU r L hL
    exact ⟨j, (goodBlock_iff_goodSeq (fun r => defect_nonneg hτ r)).1 hj⟩
  -- transfer along the law identification
  have hseq := hterm_transfer (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν)
    (Swarming.Uniform.arrayMeasure N)
    (fun ω => (dT ω, tauT ω))
    (fun U => (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U))
    (measurable_dT.prodMk measurable_tauT) hmeasSeq hlaw harr'
  -- translate back to `GoodT`
  intro r L hL
  filter_upwards [hseq r L hL] with ω hω
  obtain ⟨j, hj⟩ := hω
  exact ⟨j, (goodT_iff_goodSeq B _ _ r (2 ^ j * L) ω).2 hj⟩

/-- **The same, with the ballistic constant existentially quantified**: no speed hypothesis is
left to the caller. -/
theorem hterm_pathlaw_of_array_exists {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) [Nonempty (Fin N)] (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    (τf : Swarming.Uniform.Array N → ℕ → ℕ)
    (hτf : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (τf U))
    (hmeasSeq : Measurable fun U : Swarming.Uniform.Array N =>
      (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν).map (fun ω => (dT ω, tauT ω))
      = (Swarming.Uniform.arrayMeasure N).map
          (fun U => (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
        GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L) := by
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  exact ⟨κ, hκ, hterm_pathlaw_of_array hp0 hp1 hm N hN B hB hκ (hspeed N hN) τf hτf
    hmeasSeq hdiam ν hlaw⟩

end LawBridge

end SwarmM4C


namespace SwarmM4C

namespace LawBridge

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec SwarmM4C.FixedConst

theorem measurableSet_goodT_exists {N m : ℕ} (B C₀ T r L : ℕ) :
    MeasurableSet {ω : ℕ → RecState N m × ℕ | ∃ j : ℕ, GoodT B C₀ T ω r (2 ^ j * L)} := by
  have hEq : {ω : ℕ → RecState N m × ℕ | ∃ j : ℕ, GoodT B C₀ T ω r (2 ^ j * L)}
      = ⋃ j : ℕ, {ω : ℕ → RecState N m × ℕ | GoodT B C₀ T ω r (2 ^ j * L)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hEq]
  exact MeasurableSet.iUnion fun j => measurableSet_goodT B C₀ T r (2 ^ j * L)

/-- **Measurability-free form of the law bridge.**

The law identification can also be stated *only at the level of the block events* that the
tightness route consumes: for every `r` and `L ≥ 1` the event "some dyadic multiple of `L` is a
good block at `r`" has the same probability in the stopped-record path law and in the actual
array law.  Then no measurability of the array statistic is needed: the array side enters only
through the almost-sure block statement, and the conversion from "the complement is null" to
"the event has full outer measure" uses subadditivity only.

This hypothesis is implied by the joint-law identification of `hterm_pathlaw_of_array` whenever
the array statistic is measurable; it is genuinely weaker (it is an exchange rate for the block
events alone). -/
theorem hterm_pathlaw_of_eventlaw {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) [Nonempty (Fin N)] (_hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (τf : Swarming.Uniform.Array N → ℕ → ℕ)
    (hτf : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (τf U))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : ∀ r L : ℕ, 1 ≤ L →
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν)
          {ω | ∃ j : ℕ, GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
            (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L)}
        = (Swarming.Uniform.arrayMeasure N)
          {U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
            (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)}) :
    ∀ r L : ℕ, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
      GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L) := by
  classical
  intro r L hL
  have harr : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∃ j : ℕ,
      RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U) (⌈2 * (B : ℝ) / κ⌉₊ + 2)
        (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L) := by
    filter_upwards [hspeed, hτf, hdiam] with U hU hτ hspread
    have hspd := hU (Classical.arbitrary (Fin N))
    exact hterm_fixed hτ (actX_step p m U) (actX_zero p m U) hκ hspd
      (defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd hspread)
      B hB r L hL
  -- the array-side block event has full outer measure
  have hzero : (Swarming.Uniform.arrayMeasure N)
      {U | ¬ ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
        (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)} = 0 := by
    rw [← ae_iff]
    exact harr
  have hfull : (Swarming.Uniform.arrayMeasure N)
      {U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
        (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)}
      = (Swarming.Uniform.arrayMeasure N) Set.univ := by
    refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
    have hsub : (Set.univ : Set (Swarming.Uniform.Array N)) ⊆
        {U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)}
        ∪ {U | ¬ ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)} := by
      intro U _
      by_cases h : ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)
      · exact Or.inl h
      · exact Or.inr h
    calc (Swarming.Uniform.arrayMeasure N) Set.univ
        ≤ (Swarming.Uniform.arrayMeasure N)
            ({U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
                (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)}
              ∪ {U | ¬ ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
                (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)}) :=
          measure_mono hsub
      _ ≤ (Swarming.Uniform.arrayMeasure N)
            {U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
              (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)}
          + (Swarming.Uniform.arrayMeasure N)
            {U | ¬ ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
              (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)} :=
          measure_union_le _ _
      _ = (Swarming.Uniform.arrayMeasure N)
            {U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
              (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)} := by
          rw [hzero, add_zero]
  have hpath : (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν)
      {ω | ∃ j : ℕ, GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
        (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L)}
      = (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν) Set.univ := by
    rw [hlaw r L hL, hfull, measure_univ, measure_univ]
  exact (ae_mem_iff_measure_eq
    (measurableSet_goodT_exists B _ _ r L).nullMeasurableSet).2 hpath

end LawBridge

end SwarmM4C


/-! ### Consistency constraint: the identification forces the start law

The array's level-`0` record statistic is *deterministic*: its first record time is `0` and its
defect is `0` (all walkers are at the origin).  Hence the joint-law identification `hlaw` can only
hold when the start law `ν` of the path law is supported on states with `max_i d_i = 0` at record
time `0`.  In particular `hlaw` is **not** satisfiable for an arbitrary initial law `μ`, and no
identification of the array can discharge the `hterm` field for arbitrary `μ`: that field, at
index `0`, is a genuinely stochastic statement about the record kernel from an arbitrary start.

This is recorded here so that the identification is not used outside its scope.  The Krylov–
Bogoliubov step `exists_invariant_measure_pos_hitKInf` needs tightness of the iterates for a
*single* initial law, for which a start law with `max_i d_i = 0` suffices. -/

namespace SwarmM4C

namespace LawBridge

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `runMin` at time `0` vanishes when every walker starts at the origin. -/
theorem runMin_zero {X : ι → ℕ → ℤ} (h0 : ∀ i, X i 0 = 0) : runMin X 0 = 0 := by
  refine le_antisymm ?_ ?_
  · have hle := runMin_le (X := X) 0 (Classical.arbitrary ι)
    rw [h0 (Classical.arbitrary ι)] at hle
    exact hle
  · exact Finset.le_inf' (s := Finset.univ) (f := fun i => X i 0) Finset.univ_nonempty
      (fun i _ => by rw [h0 i])

/-- The first record time of a unit-step family started at the origin is `0`. -/
theorem tau_zero_of_isRecord {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0) :
    τ 0 = 0 := by
  have hpos := (hτ 0).2
  have hz : runMax X 0 = (0 : ℤ) := RecordoSupply.runMax_zero X h0
  by_contra hne0
  have hlt : 0 < τ 0 := Nat.pos_of_ne_zero hne0
  have hcon := (hτ 0).1 0 hlt
  rw [hz] at hcon
  exact absurd hcon (by norm_num)

/-- The defect at level `0` of a unit-step family started at the origin is `0`. -/
theorem defect_zero_of_isRecord {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0) :
    defect X τ 0 = 0 := by
  rw [defect, tau_zero_of_isRecord hτ hne h0, runMin_zero h0]
  norm_num

/-- A set whose complement is null has full outer measure. -/
theorem measure_eq_univ_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (h : ∀ᵐ a ∂μ, a ∈ s) : μ s = μ Set.univ := by
  have hzero : μ {a | ¬ a ∈ s} = 0 := ae_iff.1 h
  have hzero' : μ sᶜ = 0 := hzero
  refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
  calc μ Set.univ = μ (s ∪ sᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ s + μ sᶜ := measure_union_le _ _
    _ = μ s := by rw [hzero', add_zero]

/-- The evaluation-at-`0` statistic on record paths is measurable. -/
theorem measurable_seqP_zero {N m : ℕ} :
    Measurable fun ω : ℕ → RecState N m × ℕ => ((dT ω, tauT ω) : (ℕ → ℕ) × (ℕ → ℕ)) :=
  measurable_dT.prodMk measurable_tauT

theorem measurableSet_seq_zero :
    MeasurableSet {s : (ℕ → ℕ) × (ℕ → ℕ) | (s.1 0, s.2 0) = (0, 0)} := by
  have hmap : Measurable fun s : (ℕ → ℕ) × (ℕ → ℕ) => (s.1 0, s.2 0) :=
    ((measurable_pi_apply (0 : ℕ)).comp measurable_fst).prodMk
      ((measurable_pi_apply (0 : ℕ)).comp measurable_snd)
  exact (measurableSet_singleton (0, 0)).preimage hmap

theorem measurableSet_start_zero {N m : ℕ} :
    MeasurableSet {z : RecState N m × ℕ | (dmax z.1, z.2) = (0, 0)} := by
  have h1 : Measurable fun z : RecState N m × ℕ => dmax z.1 := measurable_dmax.comp measurable_fst
  have h2 : Measurable fun z : RecState N m × ℕ => z.2 := measurable_snd
  exact (measurableSet_singleton (0, 0)).preimage (h1.prodMk h2)

end LawBridge

end SwarmM4C


