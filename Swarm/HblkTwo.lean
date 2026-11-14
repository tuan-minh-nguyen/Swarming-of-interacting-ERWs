/-
# The fluid block estimate `(blkprob)`: the third clause is geometry, not analysis

`ScaleRepairReduce.PCtxR.of_eventual` reduces the invariant-record tightness route to the paper's
block estimate `hblk`

  `μ ({d r ≤ ℓ} ∩ {¬ Good r ℓ}) ≤ p ℓ   (ℓ ≥ 1, r ≥ C₀ ℓ)`,

where `Good r L` is the conjunction of the paper's three block inequalities

  `(time)`  `τ (r + B L) - τ r ≤ T L`,
  `(half)`  `2 d (r + B L) ≤ L`,
  `(diam)`  `∀ u ∈ [r, r + B L], d u ≤ C₀ L`.

The point of this file is that **(diam) is not an analytic input**: it follows from `(time)` and
`d r ≤ L` by the nearest-neighbour record geometry, already formalised as
`RecordDefect.block_defect_bound`.  Consequently the entire stochastic content of `(blkprob)` is
concentrated in the two remaining clauses:

* `(time)` — the record advances `B ℓ` levels in `T ℓ` steps (the paper's fluid-limit bound
  `R(T) > B + 2`, i.e. the ballistic advance of the record);
* `(half)` — the defect is halved over a block of `B ℓ` record levels (the paper's fluid-limit
  contraction).

Main declarations.

* `BadBlk`, `BadTime`, `BadHalf` — the three bad events as predicates on the `(defect, record
  time)` sequence, together with their measurability.
* `badBlk_subset` — `¬ Good ⊆ ¬ (time) ∪ ¬ (half)` given the two-clause-to-`Good` implication.
* `twoBlock_goodSeq` — the array-side geometry: `(time) ∧ (half) ⟹ GoodBlock` for a
  nearest-neighbour family with first-hitting record times.
* `himpl_of_record` — the same in the `GoodSeq` (natural-valued) form consumed by the record path
  law.
* `measure_preimage_le_of_map_eq` and `hblk_of_array` — the law transfer: an array-side bound for
  the two bad events gives the path-side `hblk` for `p₁ + p₂`.
* `hblk_canonical_of_two` — the resulting two-input form of `hblk` on the canonical stopped-record
  path law, using the proved joint record law `M7Block.jointLawIdentity_actual`.

No proof holes.  No probabilistic content beyond measure subadditivity and the two proved
transfers is assumed; the residual analytic inputs are exactly the two bad-event bounds.
-/
import Swarm.ActualRecordoHterm
import Swarm.TightChain

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace HblkTwo

open RecordDefect RecordoSupply SwarmM4C.LawBridge SimJump.RecKernel SwarmRec
  SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform

/-! ### The three bad events as predicates on the `(defect, record time)` sequence -/

/-- The paper's `(blkprob)` bad event, as a predicate of the numeric sequence
`q = (defect sequence, record time sequence)`. -/
def BadBlk (B C₀ T : ℕ) (q : (ℕ → ℕ) × (ℕ → ℕ)) (r L : ℕ) : Prop :=
  q.1 r ≤ L ∧ ¬ GoodSeq B C₀ T q.1 q.2 r L

/-- The failure of the first block inequality `(time)` on `{d r ≤ L}`. -/
def BadTime (B T : ℕ) (q : (ℕ → ℕ) × (ℕ → ℕ)) (r L : ℕ) : Prop :=
  q.1 r ≤ L ∧ q.2 r + T * L < q.2 (r + B * L)

/-- The failure of the second block inequality `(half)` on `{d r ≤ L}`. -/
def BadHalf (B : ℕ) (q : (ℕ → ℕ) × (ℕ → ℕ)) (r L : ℕ) : Prop :=
  q.1 r ≤ L ∧ L / 2 < q.1 (r + B * L)

/-! ### Measurability -/

theorem measurable_coord (k : ℕ) : Measurable fun q : (ℕ → ℕ) × (ℕ → ℕ) => q.1 k :=
  (measurable_pi_apply k).comp measurable_fst

theorem measurable_coord2 (k : ℕ) : Measurable fun q : (ℕ → ℕ) × (ℕ → ℕ) => q.2 k :=
  (measurable_pi_apply k).comp measurable_snd

theorem measurableSet_badBlk (B C₀ T r L : ℕ) :
    MeasurableSet {q : (ℕ → ℕ) × (ℕ → ℕ) | BadBlk B C₀ T q r L} :=
  (measurableSet_le (measurable_coord r) measurable_const).inter
    (measurableSet_goodSeq B C₀ T r L).compl

theorem measurableSet_badTime (B T r L : ℕ) :
    MeasurableSet {q : (ℕ → ℕ) × (ℕ → ℕ) | BadTime B T q r L} :=
  (measurableSet_le (measurable_coord r) measurable_const).inter
    (measurableSet_lt ((measurable_coord2 r).add_const (T * L)) (measurable_coord2 _))

theorem measurableSet_badHalf (B r L : ℕ) :
    MeasurableSet {q : (ℕ → ℕ) × (ℕ → ℕ) | BadHalf B q r L} :=
  (measurableSet_le (measurable_coord r) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_coord _))

/-! ### Set-level decomposition -/

/-- **The third block clause is redundant.**  If the first two block clauses at `(r, L)` already
force `GoodSeq`, then the `(blkprob)` bad event is contained in the union of the two remaining bad
events. -/
theorem badBlk_subset {B C₀ T r L : ℕ} {q : (ℕ → ℕ) × (ℕ → ℕ)}
    (himpl : q.1 r ≤ L → q.2 (r + B * L) ≤ q.2 r + T * L →
      q.1 (r + B * L) ≤ L / 2 → GoodSeq B C₀ T q.1 q.2 r L) :
    BadBlk B C₀ T q r L → BadTime B T q r L ∨ BadHalf B q r L := by
  rintro ⟨hd, hng⟩
  by_contra hcon
  simp only [not_or] at hcon
  have ht : q.2 (r + B * L) ≤ q.2 r + T * L := by
    by_contra hc
    exact hcon.1 ⟨hd, not_le.1 hc⟩
  have hh : q.1 (r + B * L) ≤ L / 2 := by
    by_contra hc
    exact hcon.2 ⟨hd, not_le.1 hc⟩
  exact hng (himpl hd ht hh)

/-! ### The array-side geometry: `(time) ∧ (half) ⟹ GoodBlock`

The paper's third block inequality is a deterministic consequence of the first one.  We reuse
`RecordDefect.block_defect_bound`, which is proved for an abstract nearest-neighbour family with
first-hitting record times, hence applies to the actual array through `actX`. -/

section Geometry

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-- **`(time) ∧ (half) ⟹ GoodBlock`.**  The paper's three block inequalities reduce to two, at the
price of the constant `C₀ ≥ B + T + 1` used in the paper's `(BTchoice)`. -/
theorem twoBlock_goodBlock (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {T C₀ B r L : ℕ} (hC₀ : B + T + 1 ≤ C₀)
    (hdr : defect X τ r ≤ (L : ℤ))
    (htime : τ (r + B * L) - τ r ≤ T * L)
    (hhalf : 2 * defect X τ (r + B * L) ≤ (L : ℤ)) :
    GoodBlock (defect X τ) τ T C₀ B r L := by
  refine ⟨htime, hhalf, fun u hu1 hu2 => ?_⟩
  have hbd := block_defect_bound hτ hne hdr htime u hu1 hu2
  have hL0 : (0 : ℤ) ≤ (L : ℤ) := by exact_mod_cast Nat.zero_le L
  have hle : ((B + T + 1 : ℕ) : ℤ) ≤ ((C₀ : ℕ) : ℤ) := by exact_mod_cast hC₀
  have hmul : ((B + T + 1 : ℕ) : ℤ) * (L : ℤ) ≤ ((C₀ : ℕ) : ℤ) * (L : ℤ) :=
    mul_le_mul_of_nonneg_right hle hL0
  exact le_trans hbd hmul

/-- **The natural-valued form.**  The same statement for the sequence
`q = ((defect X τ r).toNat, τ r)` consumed by `GoodSeq` and hence by the stopped-record path
law. -/
theorem himpl_of_record (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {T C₀ B : ℕ} (hC₀ : B + T + 1 ≤ C₀) {r L : ℕ}
    (hdr : (fun u : ℕ => (defect X τ u).toNat) r ≤ L)
    (htime : τ (r + B * L) ≤ τ r + T * L)
    (hhalf : (fun u : ℕ => (defect X τ u).toNat) (r + B * L) ≤ L / 2) :
    GoodSeq B C₀ T (fun u : ℕ => (defect X τ u).toNat) τ r L := by
  classical
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  -- convert the two natural-valued clauses to the integer form of `GoodBlock`
  have htimeZ : τ (r + B * L) - τ r ≤ T * L := by omega
  have hdrZ : defect X τ r ≤ (L : ℤ) := by
    have h1 : ((defect X τ r).toNat : ℤ) ≤ (L : ℤ) := by exact_mod_cast hdr
    rwa [Int.toNat_of_nonneg (defect_nonneg hτ r)] at h1
  have hhalfZ : 2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
    have h1 : ((defect X τ (r + B * L)).toNat : ℤ) ≤ ((L / 2 : ℕ) : ℤ) := by
      exact_mod_cast hhalf
    have h2 : ((L / 2 : ℕ) : ℤ) * 2 ≤ (L : ℤ) := by
      have := Nat.div_mul_le_self L 2
      push_cast
      exact_mod_cast this
    have h3 : ((defect X τ (r + B * L)).toNat : ℤ) = defect X τ (r + B * L) :=
      Int.toNat_of_nonneg (defect_nonneg hτ _)
    linarith
  have hGB := twoBlock_goodBlock hτ hne hC₀ hdrZ htimeZ hhalfZ
  exact (goodBlock_iff_goodSeq (fun u => defect_nonneg hτ u)).1 hGB

end Geometry

/-! ### Law transport of the two bad events -/

/-- **Transport of a measure bound along an equality of laws.** -/
theorem measure_preimage_le_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {ν : Measure Ω'} {μ : Measure Ω} {s : Ω' → (ℕ → ℕ) × (ℕ → ℕ)}
    {q : Ω → (ℕ → ℕ) × (ℕ → ℕ)}
    (hs : Measurable s) (hq : Measurable q) (hlaw : ν.map s = μ.map q)
    {S : Set ((ℕ → ℕ) × (ℕ → ℕ))} (hS : MeasurableSet S) {c : ℝ≥0∞}
    (h : μ (q ⁻¹' S) ≤ c) : ν (s ⁻¹' S) ≤ c := by
  rw [← Measure.map_apply hs hS, hlaw, Measure.map_apply hq hS]
  exact h

/-! ### The two-input form of `hblk` on the canonical stopped-record path law -/

/-- **`hblk` for the actual array from the two bad-event bounds.**

The array is the canonical one (`actX p m`, canonical record times `recTimeA`), and the two
hypotheses are the paper's block estimate for the two *remaining* clauses:

* `h₁`: on `{d r ≤ ℓ}`, the record advance `τ_{r+Bℓ} - τ_r ≤ T ℓ` fails with probability at most
  `p₁ ℓ`;
* `h₂`: on `{d r ≤ ℓ}`, the halving `d_{r+Bℓ} ≤ ℓ/2` fails with probability at most `p₂ ℓ`.

Then the path-side `hblk` at the canonical Dirac start holds with profile `p₁ + p₂`.  The
hypotheses `(diam)` of the block are eliminated by `twoBlock_goodBlock`. -/
theorem hblk_canonical_of_two {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B C₀ T : ℕ) (hC₀ : B + T + 1 ≤ C₀) (p₁ p₂ : ℕ → ℝ≥0∞)
    (hrec : ∀ᵐ U ∂(arrayMeasure N), IsRecord (actX p m U) (recTimeA p m U))
    (h₁ : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U | BadTime B T
        (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r) r ℓ} ≤ p₁ ℓ)
    (h₂ : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U | BadHalf B
        (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r) r ℓ} ≤ p₂ ℓ) :
    ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ}) ≤ p₁ ℓ + p₂ ℓ := by
  classical
  intro ℓ hℓ r hr
  set q : Swarming.Uniform.Array N → (ℕ → ℕ) × (ℕ → ℕ) := fun U =>
    (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
      fun r => recTimeA p m U r) with hqdef
  set s : (ℕ → RecState N m × ℕ) → (ℕ → ℕ) × (ℕ → ℕ) := fun ω => (dT ω, tauT ω) with hsdef
  have hs : Measurable s := measurable_dT.prodMk measurable_tauT
  have hq : Measurable q := measurable_recordStat (N := N) p m
  have hlaw : (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))).map s
      = (arrayMeasure N).map q :=
    M7Block.jointLawIdentity_actual (N := N) hp0 hp1 hm hN
  -- the array-side bound for the union
  set QT : Set (Swarming.Uniform.Array N) := {U | BadTime B T (q U) r ℓ} with hQT
  set QH : Set (Swarming.Uniform.Array N) := {U | BadHalf B (q U) r ℓ} with hQH
  have hsub : {U : Swarming.Uniform.Array N | BadBlk B C₀ T (q U) r ℓ}
      ≤ᵐ[arrayMeasure N] (Set.union QT QH) := by
    filter_upwards [hrec] with U hU hbl
    rcases badBlk_subset
      (himpl_of_record (X := actX p m U) (τ := recTimeA p m U) hU
        (actX_step p m U) hC₀) hbl with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hbound : (arrayMeasure N) {U : Swarming.Uniform.Array N | BadBlk B C₀ T (q U) r ℓ}
      ≤ p₁ ℓ + p₂ ℓ :=
    calc (arrayMeasure N) {U : Swarming.Uniform.Array N | BadBlk B C₀ T (q U) r ℓ}
        ≤ (arrayMeasure N) (Set.union QT QH) := measure_mono_ae hsub
      _ ≤ (arrayMeasure N) QT + (arrayMeasure N) QH := measure_union_le _ _
      _ ≤ p₁ ℓ + p₂ ℓ := add_le_add (h₁ ℓ hℓ r hr) (h₂ ℓ hℓ r hr)
  -- transport to the path law
  have hpre : s ⁻¹' {Q : (ℕ → ℕ) × (ℕ → ℕ) | BadBlk B C₀ T Q r ℓ}
      = {ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, hsdef, BadBlk,
      goodT_iff_goodSeq]
  rw [← hpre]
  exact measure_preimage_le_of_map_eq hs hq hlaw (measurableSet_badBlk B C₀ T r ℓ) hbound

end HblkTwo


