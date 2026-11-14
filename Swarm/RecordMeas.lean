/-
# Measurability of the actual array's record statistics


`Swarm/LawBridge.lean` reduces the `hterm` field of the stopped-record path
interface to a *joint law identification* between the record kernel's `(defect, record time)`
sequences and the actual array's.  Its two non-probabilistic inputs on the array side are

* `hτf : ∀ᵐ U, IsRecord (actX p m U) (τf U)`, and
* the **measurability** of the array statistic `U ↦ ((d_r).toNat, τ_r)`

for a record map `τf`.  The second was listed there as an open technical hypothesis ("the only
non-probabilistic input"), with the remark that the route is measurability of the positions
plus measurability of the fibres of the `Nat.find` record time.

This file proves that measurability, and does it for a *canonical* record map constructed from
the array itself, so that both hypotheses become theorems:

* `ReachAll` is the (measurable) event that the running maximum attains every level;
* `recTimeA p m U r` is the first time the running maximum attains level `r`, defined by
  `Nat.find` with a constant fallback off `ReachAll`, hence a genuine function of `U` with no
  dependence on a proof of reachability;
* `measurable_recTimeA`, `measurable_defectA`, `measurable_recordStat` : measurability of the
  record time, of the defect `d_r`, and of the joint sequence statistic;
* `isRecord_recTimeA`, `ae_isRecord_recTimeA` : the paper's `IsRecord` description for
  `recTimeA`, the almost-sure form from the proved actual ballistic lower bound;
* (`RecordLawBridge.lean`) `hterm_pathlaw_of_array_canonical` and `..._exists` : the LawBridge
  transfer with `hτf` and the measurability hypothesis *discharged*, leaving exactly the joint
  law identity `hlaw` (and the diameter estimate `(diam)`) as residual inputs;
* `measurableSet_goodBlockA` : the array-side block events are measurable, so the event-level
  form of the law identity relates genuine probabilities;
* `recTimeA_eq_iff`, `defectA_eq_of_recTimeA_eq` : finite-prefix determination of the record
  time and of the defect (`{τ_r = k}` is a function of the positions up to time `k`);
* `recTimeA_zero`, `defectA_zero` : the level-`0` record time and defect are `0` pointwise;
* `recTimeA_eq_recTime` : agreement with `RecordoSupply.recTime` on `ReachAll`.

Notation: `actX p m U` is `RecordoSupply.actX`, the actual recursive position field of
`Swarming.Trajectory.trajectory`.
-/
import Swarm.LawBridge
import Swarm.MeasurableInc
import Swarm.ActualRecordFiltration

open MeasureTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace SwarmRecordMeas

open RecordDefect RecordoSupply Swarming.Uniform

/-! ### Measurability of finite suprema and infima in the array

`runMax X n = max_i X i n` is a `Finset.sup'` over `univ`.  Its measurability is proved through
the level-set characterisation of `sup'`, which avoids any general theory of measurable
lattice-complete operations. -/


/-! ### Patching a measurable function against a measurable `ℕ`-valued index

Evaluating a *jointly* defined quantity at a random time is measurable when each slice is. -/

section Patch

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- **Countable patching.**  If `τ : α → ℕ` is measurable and every slice `g k` is measurable,
then `a ↦ g (τ a) a` is measurable. -/
theorem measurable_comp_nat {τ : α → ℕ} (hτ : Measurable τ) {g : ℕ → α → β}
    (hg : ∀ k, Measurable (g k)) : Measurable fun a => g (τ a) a := by
  intro t ht
  have hset : (fun a => g (τ a) a) ⁻¹' t = ⋃ k : ℕ, ({a | τ a = k} ∩ (g k) ⁻¹' t) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro ha
      exact ⟨τ a, rfl, ha⟩
    · rintro ⟨k, hk, ha⟩
      rw [hk]
      exact ha
  rw [hset]
  exact MeasurableSet.iUnion fun k => (hτ (measurableSet_singleton k)).inter (hg k ht)

/-- **`Nat.find` measurability.**  For a predicate whose `n`-slices are measurable and which
holds somewhere at every point, the least witness is measurable. -/
theorem measurable_firstHit {P : α → ℕ → Prop} (hP : ∀ n, MeasurableSet {a | P a n})
    (h : ∀ a, ∃ n, P a n) : Measurable fun a => firstHit P h a := by
  refine measurable_to_countable' fun k => ?_
  change MeasurableSet {a | firstHit P h a = k}
  have hset : {a | firstHit P h a = k} =
      {a | P a k} ∩ ⋂ j ∈ Finset.range k, {a | ¬ P a j} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
    rw [firstHit_eq]
    exact Nat.find_eq_iff (h a)
  rw [hset]
  exact (hP k).inter (MeasurableSet.biInter (Finset.countable_toSet _) fun j _ => (hP j).compl)

end Patch

/-! ### The actual array's canonical record times

The record time of level `r` is the first time the running maximum attains `r`.  The definition
below is total: off the event `ReachAll` (where some level is never attained) it takes the value
`0`.  This makes it an honest function of the array, which is what measurability needs, and on
`ReachAll` it is exactly the paper's `τ_r`. -/

namespace Actual

open RecordDefect RecordoSupply Swarming.Uniform

variable {N : ℕ} [Nonempty (Fin N)]

/-- The actual position field is measurable in the array. -/
theorem measurable_actX (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => actX p m U i n :=
  (Swarming.Fair.measurable_trajectory (N := N) p m n).1 i

/-- The actual running maximum is measurable in the array at fixed time. -/
theorem measurable_runMax_actX (p : ℝ) (m : ℕ) (n : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => runMax (actX p m U) n :=
  measurable_runMax (ι := Fin N) (f := fun i U => actX p m U i n) (fun i => measurable_actX p m i n) n

/-- The actual running minimum is measurable in the array at fixed time. -/
theorem measurable_runMin_actX (p : ℝ) (m : ℕ) (n : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => runMin (actX p m U) n :=
  measurable_runMin (ι := Fin N) (f := fun i U => actX p m U i n) (fun i => measurable_actX p m i n) n

/-- `ReachAll` is a measurable event. -/
theorem measurableSet_reachAll (p : ℝ) (m : ℕ) :
    MeasurableSet (ReachAll (N := N) p m) := by
  have hset : ReachAll (N := N) p m =
      ⋂ r : ℕ, ⋃ n : ℕ, {U : Swarming.Uniform.Array N | runMax (actX p m U) n = (r : ℤ)} := by
    ext U
    simp only [ReachAll, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
  rw [hset]
  exact MeasurableSet.iInter fun r =>
    MeasurableSet.iUnion fun n =>
      measurable_runMax_actX (N := N) p m n (measurableSet_singleton (r : ℤ))

/-- **The level-`0` defect is `0`, pointwise.**  No speed, `(diam)` or `IsRecord` hypothesis is
used: the canonical record time at level `0` is literally `0`. -/
theorem defectA_zero (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) :
    defect (actX p m U) (recTimeA p m U) 0 = 0 := by
  rw [defect, recTimeA_zero, SwarmM4C.LawBridge.runMin_zero (actX_zero p m U)]
  norm_num

/-- **Measurability of the record time.** -/
theorem measurable_recTimeA (p : ℝ) (m : ℕ) (r : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => recTimeA p m U r := by
  have hP : ∀ n : ℕ, MeasurableSet {U : Swarming.Uniform.Array N | hitPred p m r U n} := by
    intro n
    exact (measurableSet_reachAll (N := N) p m).compl.union
      (measurable_runMax_actX (N := N) p m n (measurableSet_singleton (r : ℤ)))
  exact measurable_firstHit hP (hitExists p m r)

/-- **Measurability of the record-time sequence.** -/
theorem measurable_recSeqA (p : ℝ) (m : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => fun r : ℕ => recTimeA p m U r :=
  measurable_pi_iff.2 fun r => measurable_recTimeA p m r

/-- **`IsRecord` for the canonical record times.**  This is the paper's definition of `τ_r`
(nearest-neighbour steps and the start at the origin are used for the `1`-Lipschitz property of
the running maximum). -/
theorem isRecord_recTimeA (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N)
    (hreach : ∀ r : ℕ, ∃ n : ℕ, runMax (actX p m U) n = (r : ℤ)) :
    IsRecord (actX p m U) (recTimeA p m U) := by
  have hstep := runMax_step (actX p m U) (actX_step p m U)
  intro r
  have hnot : ∀ n : ℕ, n < recTimeA p m U r → runMax (actX p m U) n ≠ (r : ℤ) := by
    intro n hn hEq
    exact recTimeA_min p m U r n hn (Or.inr hEq)
  constructor
  · intro n
    induction n with
    | zero =>
        intro hn
        have hz : runMax (actX p m U) 0 = (0 : ℤ) := by
          simpa using runMax_zero (actX p m U) (actX_zero p m U)
        have hne := hnot 0 hn
        rw [hz] at hne ⊢
        omega
    | succ n ih =>
        intro hn
        have hprev : runMax (actX p m U) n < (r : ℤ) := ih (by omega)
        have hne := hnot (n + 1) hn
        have hub := (abs_le.1 (hstep n)).2
        omega
  · refine (recTimeA_spec p m U r).resolve_left ?_
    intro hcon
    exact hcon hreach

/-- The almost-sure `IsRecord` statement from an explicit one-walker speed bound. -/
theorem ae_isRecord_recTimeA_of_speed {p : ℝ} {m : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ)) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (recTimeA p m U) := by
  filter_upwards [hspeed] with U hU
  have hspd := hU (Classical.arbitrary (Fin N))
  refine isRecord_recTimeA p m U fun r => ?_
  obtain ⟨n, hn⟩ := exists_runMax_ge (actX p m U) hκ hspd r
  obtain ⟨k, -, hk⟩ := exists_runMax_eq (actX p m U) (actX_step p m U) (actX_zero p m U) hn
  exact ⟨k, hk⟩

/-- The unconditional almost-sure `IsRecord` statement for the actual array. -/
theorem ae_isRecord_recTimeA {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (recTimeA p m U) := by
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  exact ae_isRecord_recTimeA_of_speed (N := N) (p := p) (m := m) hκ (hspeed N hN)

/-- **The canonical record time agrees with `RecordoSupply.recTime`.**  On `ReachAll` the two
`Nat.find` constructions have pointwise equivalent predicates, so every `RecordoSupply` statement
about `recTime` applies to the measurable map `recTimeA`. -/
theorem recTimeA_eq_recTime (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ)
    (hreach : ∀ r : ℕ, ∃ n : ℕ, runMax (actX p m U) n = (r : ℤ)) :
    recTimeA p m U r = RecordoSupply.recTime (actX p m U) hreach r := by
  have hU : U ∈ ReachAll (N := N) p m := hreach
  have hcongr : ∀ n : ℕ, hitPred p m r U n ↔ runMax (actX p m U) n = (r : ℤ) := by
    intro n
    simp only [hitPred, hU, not_true, false_or]
  exact Nat.find_congr' (fun {n} => hcongr n)

/-- **Measurability of the defect `d_r` at the canonical record time.** -/
theorem measurable_defectA (p : ℝ) (m : ℕ) (r : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N =>
      defect (actX p m U) (recTimeA p m U) r := by
  have hτ : Measurable fun U : Swarming.Uniform.Array N => recTimeA p m U r := measurable_recTimeA p m r
  have hmin : Measurable fun U : Swarming.Uniform.Array N =>
      runMin (actX p m U) (recTimeA p m U r) :=
    measurable_comp_nat hτ (g := fun k U => runMin (actX p m U) k)
      (fun k => measurable_runMin_actX (N := N) p m k)
  have h : Measurable fun U : Swarming.Uniform.Array N =>
      (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) :=
    measurable_const.sub hmin
  simpa only [defect] using h

/-- `Int.toNat` is measurable. -/
theorem measurable_intToNat : Measurable (fun z : ℤ => z.toNat) := measurable_of_countable _

/-- **Measurability of the joint record statistic** `U ↦ ((d_r).toNat, τ_r)_r`: exactly the
`hmeasSeq` hypothesis of `LawBridge.hterm_pathlaw_of_array`. -/
theorem measurable_recordStat (p : ℝ) (m : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N =>
      (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
        fun r => recTimeA p m U r) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.2 fun r => ?_
    exact measurable_intToNat.comp (measurable_defectA p m r)
  · exact measurable_recSeqA p m

/-- **Measurability of the array-side block events.**  With the canonical record map the paper's
`GoodBlock` event is a measurable subset of the array space, so the event-level law identity of
`LawBridge.hterm_pathlaw_of_eventlaw` is an identity between genuine probabilities. -/
theorem measurableSet_goodBlockA (p : ℝ) (m : ℕ) (T C₀ B r L : ℕ) :
    MeasurableSet {U : Swarming.Uniform.Array N |
      GoodBlock (defect (actX p m U) (recTimeA p m U)) (recTimeA p m U) T C₀ B r L} := by
  have hd : ∀ u : ℕ, Measurable fun U : Swarming.Uniform.Array N =>
      defect (actX p m U) (recTimeA p m U) u := measurable_defectA p m
  have hτ : Measurable fun U : Swarming.Uniform.Array N => recTimeA p m U (r + B * L) :=
    measurable_recTimeA p m _
  have hτ0 : Measurable fun U : Swarming.Uniform.Array N => recTimeA p m U r :=
    measurable_recTimeA p m r
  have hset : {U : Swarming.Uniform.Array N |
        GoodBlock (defect (actX p m U) (recTimeA p m U)) (recTimeA p m U) T C₀ B r L}
      = ({U : Swarming.Uniform.Array N |
            recTimeA p m U (r + B * L) ≤ recTimeA p m U r + T * L}
          ∩ {U : Swarming.Uniform.Array N |
            2 * defect (actX p m U) (recTimeA p m U) (r + B * L) ≤ (L : ℤ)})
        ∩ {U : Swarming.Uniform.Array N | ∀ u : ℕ, r ≤ u → u ≤ r + B * L →
            defect (actX p m U) (recTimeA p m U) u ≤ (C₀ : ℤ) * (L : ℤ)} := by
    ext U
    simp only [GoodBlock, Set.mem_ofPred_eq, Set.mem_inter_iff, Nat.sub_le_iff_le_add]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, h2, h3⟩
  rw [hset]
  refine ((measurableSet_le hτ (hτ0.add_const (T * L))).inter
    (measurableSet_le ((hd (r + B * L)).const_mul 2) measurable_const)).inter ?_
  have hEq : {U : Swarming.Uniform.Array N | ∀ u : ℕ, r ≤ u → u ≤ r + B * L →
        defect (actX p m U) (recTimeA p m U) u ≤ (C₀ : ℤ) * (L : ℤ)}
      = ⋂ u ∈ (Finset.Icc r (r + B * L) : Finset ℕ),
          {U : Swarming.Uniform.Array N |
            defect (actX p m U) (recTimeA p m U) u ≤ (C₀ : ℤ) * (L : ℤ)} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc, and_imp]
  rw [hEq]
  exact MeasurableSet.biInter (Finset.countable_toSet _)
    fun u _ => measurableSet_le (hd u) measurable_const

end Actual

end SwarmRecordMeas
