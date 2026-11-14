/-
  **`locsum`, layer 4: block independence and the Hoeffding block bound.**

  For a block length `k >= 1`, a base `a0 >= k` and `n` blocks, the variables

      Q p k (a0 + j*k),     j < n,

  depend on the disjoint mark windows `{a0 + j*k - u : u < k}`; they are independent
  (`iIndepFun_Q`), identified as functions of the block through `Qrel`.  Hoeffding applied to
  the bounded variables `Q^2` and the uniform second moment of layer 3 gives the block bound
  `residue_concentration`, and a union over the `k` residue classes gives
  `block_concentration`.
-/
import Swarm.Imports
import Mathlib.Probability.Moments.SubGaussian
import Swarm.L3Uniform

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LocSum

noncomputable section

open SwarmMarks SwarmSpatial

/-- Extension of a finite block to all of `ℕ` by `false`. -/
def extFin (k : ℕ) (v : Fin k → Bool) : ℕ → Bool := fun n => if h : n < k then v ⟨n, h⟩ else false

lemma extFin_eq {k : ℕ} {v : Fin k → Bool} {n : ℕ} (hn : n < k) :
    extFin k v n = v ⟨n, hn⟩ := by
  simp [extFin, hn]

/-- The truncation applied to the reversed mark sequence `v u = omega(x-u)`. -/
def Qseq (p : ℝ) (k : ℕ) (v : ℕ → Bool) : ℝ :=
  2 * (∑ j ∈ Finset.range k, ∏ u ∈ Finset.range j, rat p v u) - 1

lemma Q_seq (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    Q p k x ω = Qseq p k (fun u => ω (x - u)) := by
  unfold Q Gsum Pz Qseq
  rfl

lemma Qseq_congr (p : ℝ) (k : ℕ) {v v' : ℕ → Bool} (h : ∀ u < k, v u = v' u) :
    Qseq p k v = Qseq p k v' := by
  have hsum : (∑ j ∈ Finset.range k, ∏ u ∈ Finset.range j, rat p v u)
      = ∑ j ∈ Finset.range k, ∏ u ∈ Finset.range j, rat p v' u := by
    refine Finset.sum_congr rfl (fun j hj => Finset.prod_congr rfl (fun u hu => ?_))
    have hu' : u < k := lt_trans (Finset.mem_range.1 hu) (Finset.mem_range.1 hj)
    simp only [rat]
    rw [h u hu']
  unfold Qseq
  rw [hsum]

/-- The truncation as a functional of the `k`-element mark block `x, x-1, …, x-k+1`. -/
def Qrel (p : ℝ) (k : ℕ) (v : Fin k → Bool) : ℝ := Qseq p k (extFin k v)

lemma measurable_Qrel (p : ℝ) (k : ℕ) : Measurable (Qrel p k) := measurable_of_finite _

/-- `Q p k x` only depends on the block through `Qrel`. -/
lemma Q_eq_Qrel (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    Q p k x ω = Qrel p k (fun u : Fin k => ω (x - u.1)) := by
  have h := Qseq_congr p k (v := fun u => ω (x - u))
    (v' := extFin k (fun u : Fin k => ω (x - u.1)))
    (fun u hu => by rw [extFin_eq hu])
  rw [Q_seq]
  unfold Qrel
  exact h

/-! ### The index map of the blocks -/

/-- The site carrying the `u`-th mark of the `j`-th block. -/
def bidx (a0 k j u : ℕ) : ℕ := a0 + j * k - u

lemma bidx_lt {a0 k j u j' u' : ℕ} (hk : 1 ≤ k) (hu : u < k) (hu' : u' < k) (hjj : j < j') :
    bidx a0 k j u < bidx a0 k j' u' := by
  have hkey : a0 + j * k + 1 ≤ a0 + j' * k - u' := by
    have hu'k : u' ≤ k - 1 := by omega
    have h4 : j * k + k ≤ j' * k := by
      have h5 : j + 1 ≤ j' := hjj
      calc j * k + k = (j + 1) * k := by ring
        _ ≤ j' * k := Nat.mul_le_mul_right k h5
    have h6 : a0 + j * k + 1 = a0 + (j * k + k) - (k - 1) := by
      rw [Nat.add_sub_assoc (by omega : k - 1 ≤ j * k + k)]
      omega
    have h7 : a0 + (j * k + k) - (k - 1) ≤ a0 + j' * k - (k - 1) :=
      Nat.sub_le_sub_right (Nat.add_le_add_left h4 a0) (k - 1)
    have h8 : a0 + j' * k - (k - 1) ≤ a0 + j' * k - u' :=
      Nat.sub_le_sub_left hu'k (a0 + j' * k)
    calc a0 + j * k + 1 = a0 + (j * k + k) - (k - 1) := h6
      _ ≤ a0 + j' * k - (k - 1) := h7
      _ ≤ a0 + j' * k - u' := h8
  have h1 : a0 + j * k - u ≤ a0 + j * k := Nat.sub_le _ _
  calc bidx a0 k j u = a0 + j * k - u := rfl
    _ ≤ a0 + j * k := h1
    _ < a0 + j' * k - u' := lt_of_lt_of_le (Nat.lt_succ_self _) hkey

lemma bidx_inj {n k a0 : ℕ} (hk : 1 ≤ k) (ha : k ≤ a0) :
    Function.Injective (fun p : Fin n × Fin k => bidx a0 k p.1.1 p.2.1) := by
  rintro ⟨j, u⟩ ⟨j', u'⟩ h
  simp only [bidx] at h
  have hu : u.1 < k := u.2
  have hu' : u'.1 < k := u'.2
  have hul : u.1 ≤ a0 + j.1 * k := by omega
  have hu'l : u'.1 ≤ a0 + j'.1 * k := by omega
  rcases lt_trichotomy j.1 j'.1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (bidx_lt hk hu hu' hlt))
  · have h4 : a0 + j.1 * k - u.1 = a0 + j'.1 * k - u'.1 := h
    rw [heq] at h4
    have h5 : u.1 ≤ a0 + j'.1 * k := by omega
    have h6 : u'.1 ≤ a0 + j'.1 * k := by omega
    have h2 : u.1 = u'.1 := by omega
    exact Prod.ext (Fin.ext heq) (Fin.ext h2)
  · exact absurd h.symm (ne_of_lt (bidx_lt hk hu' hu hgt))

lemma bidx_single_inj {k a0 j : ℕ} (ha : k ≤ a0) :
    Function.Injective (fun u : Fin k => bidx a0 k j u.1) := by
  intro u u' h
  simp only [bidx] at h
  have h1 : u.1 ≤ a0 + j * k := by
    have := u.2; omega
  have h2 : u'.1 ≤ a0 + j * k := by
    have := u'.2; omega
  exact Fin.ext (by omega)

/-! ### The law of one block and of the block family -/

lemma map_block {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {k a0 j : ℕ} (ha : k ≤ a0) :
    (markMeasure (boolMeasure q)).map
        (fun ω : ℕ → Bool => fun u : Fin k => ω (bidx a0 k j u.1))
      = Measure.infinitePi (fun _ : Fin k => boolMeasure q) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hinj : Function.Injective (fun u : Fin k => bidx a0 k j u.1) := bidx_single_inj ha
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => boolMeasure q) hinj
  simpa [markMeasure, Function.comp_def] using h

lemma map_block_family {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {n k a0 : ℕ} (hk : 1 ≤ k)
    (ha : k ≤ a0) :
    (markMeasure (boolMeasure q)).map
        (fun ω : ℕ → Bool => fun (j : Fin n) (u : Fin k) => ω (bidx a0 k j.1 u.1))
      = Measure.infinitePi (fun _ : Fin n => Measure.infinitePi (fun _ : Fin k => boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hG := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => boolMeasure q)
    (bidx_inj (n := n) (k := k) (a0 := a0) hk ha)
  have hC := Measure.infinitePi_map_curry (μ := fun (_ : Fin n) (_ : Fin k) => boolMeasure q)
  have hcomp2 : (markMeasure (boolMeasure q)).map
      ((⇑(MeasurableEquiv.curry (Fin n) (Fin k) Bool)) ∘
        (fun ω (p : Fin n × Fin k) => ω (bidx a0 k p.1.1 p.2.1)))
      = ((markMeasure (boolMeasure q)).map
          (fun ω (p : Fin n × Fin k) => ω (bidx a0 k p.1.1 p.2.1))).map
          (MeasurableEquiv.curry (Fin n) (Fin k) Bool) :=
    (Measure.map_map (μ := markMeasure (boolMeasure q))
      (f := fun ω (p : Fin n × Fin k) => ω (bidx a0 k p.1.1 p.2.1))
      (g := ⇑(MeasurableEquiv.curry (Fin n) (Fin k) Bool))
      (by fun_prop : Measurable (⇑(MeasurableEquiv.curry (Fin n) (Fin k) Bool)))
      (by fun_prop : Measurable (fun (ω : ℕ → Bool) (p : Fin n × Fin k) => ω (bidx a0 k p.1.1 p.2.1)))).symm
  have hmain : ((markMeasure (boolMeasure q)).map
        (fun ω (p : Fin n × Fin k) => ω (bidx a0 k p.1.1 p.2.1))).map
        (MeasurableEquiv.curry (Fin n) (Fin k) Bool)
      = Measure.infinitePi (fun _ : Fin n => Measure.infinitePi (fun _ : Fin k => boolMeasure q)) := by
    simp only [markMeasure]
    rw [hG, hC]
  have hFG : (fun ω : ℕ → Bool => fun (j : Fin n) (u : Fin k) => ω (bidx a0 k j.1 u.1))
      = (⇑(MeasurableEquiv.curry (Fin n) (Fin k) Bool)) ∘
        (fun ω (p : Fin n × Fin k) => ω (bidx a0 k p.1.1 p.2.1)) := rfl
  rw [hFG]
  exact hcomp2.trans hmain

/-! ### Independence of the block variables -/

lemma iIndepFun_Q {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {n k a0 : ℕ} (hk : 1 ≤ k) (ha : k ≤ a0)
    (p : ℝ) :
    iIndepFun (fun (j : Fin n) (ω : ℕ → Bool) => Q p k (a0 + j.1 * k) ω)
      (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hB : iIndepFun (fun (j : Fin n) (ω : ℕ → Bool) => fun u : Fin k => ω (bidx a0 k j.1 u.1))
      (markMeasure (boolMeasure q)) := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map]
    · rw [map_block_family h0 h1 hk ha]
      have hfam : (fun j : Fin n => Measure.infinitePi (fun _ : Fin k => boolMeasure q))
          = fun j : Fin n => (markMeasure (boolMeasure q)).map
              (fun ω : ℕ → Bool => fun u : Fin k => ω (bidx a0 k j.1 u.1)) := by
        funext j
        exact (map_block (j := j.1) h0 h1 ha).symm
      rw [hfam]
    · intro j
      exact measurable_pi_lambda _ (fun u => measurable_pi_apply _)
  have hcomp := hB.comp (fun _ : Fin n => Qrel p k) (fun _ => measurable_Qrel p k)
  refine hcomp.congr ?_
  intro j
  exact Filter.Eventually.of_forall (fun ω => (Q_eq_Qrel p k (a0 + j.1 * k) ω).symm)

/-! ### Sub-Gaussian tails of the squared truncations -/

/-- The sub-Gaussian parameter of `Q^2`, whose range is `[0, (2k+1)^2]`: Hoeffding's lemma
gives `((b-a)/2)^2 = (((2k+1)^2)/2)^2`. -/
def subGnn (k : ℕ) : ℝ≥0 := (‖(2 * (k : ℝ) + 1) ^ 2 - 0‖₊ / 2) ^ 2

/-- The same constant as a real number. -/
def subG (k : ℕ) : ℝ := ((2 * (k : ℝ) + 1) ^ 2 / 2) ^ 2

lemma Q_sq_subgaussian {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) :
    HasSubgaussianMGF
      (fun ω : ℕ → Bool => (Q p k x ω) ^ 2
        - ∫ ω, (Q p k x ω) ^ 2 ∂(markMeasure (boolMeasure q)))
      (subGnn k) (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
  have hmeas : AEMeasurable (fun ω : ℕ → Bool => (Q p k x ω) ^ 2)
      (markMeasure (boolMeasure q)) := ((measurable_Q p k x).pow_const 2).aemeasurable
  have hbdd : ∀ᵐ ω ∂(markMeasure (boolMeasure q)),
      (Q p k x ω) ^ 2 ∈ Set.Icc (0 : ℝ) ((2 * (k : ℝ) + 1) ^ 2) := by
    filter_upwards with ω
    have h := Q_abs_le hp1 hp2 k x ω
    have h1' : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
    constructor
    · positivity
    · nlinarith [abs_nonneg (Q p k x ω), sq_abs (Q p k x ω)]
  have h := hasSubgaussianMGF_of_mem_Icc (μ := markMeasure (boolMeasure q)) hmeas hbdd
  exact h

/-! ### The Hoeffding bound for one residue class -/

theorem residue_concentration {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {n k a0 r : ℕ} (hk : 1 ≤ k)
    (ha : k ≤ a0 + r) {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (markMeasure (boolMeasure q)).real
        {ω | ε ≤ ∑ j : Fin n, ((Q p k (a0 + r + j.1 * k) ω) ^ 2
          - ∫ ω, (Q p k (a0 + r + j.1 * k) ω) ^ 2 ∂(markMeasure (boolMeasure q)))}
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ _j : Fin n, subGnn k : ℝ≥0) : ℝ))) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
  have hind : iIndepFun (fun (j : Fin n) (ω : ℕ → Bool) => Q p k (a0 + r + j.1 * k) ω)
      (markMeasure (boolMeasure q)) := iIndepFun_Q h0 h1 hk ha p
  have hX : iIndepFun (fun (j : Fin n) (ω : ℕ → Bool) => (Q p k (a0 + r + j.1 * k) ω) ^ 2
      - ∫ ω, (Q p k (a0 + r + j.1 * k) ω) ^ 2 ∂(markMeasure (boolMeasure q)))
      (markMeasure (boolMeasure q)) :=
    hind.comp (fun j y => y ^ 2 - ∫ ω, (Q p k (a0 + r + j.1 * k) ω) ^ 2
      ∂(markMeasure (boolMeasure q))) (fun j => by fun_prop)
  have hsub : ∀ j : Fin n, HasSubgaussianMGF
      (fun ω : ℕ → Bool => (Q p k (a0 + r + j.1 * k) ω) ^ 2
        - ∫ ω, (Q p k (a0 + r + j.1 * k) ω) ^ 2 ∂(markMeasure (boolMeasure q)))
      (subGnn k) (markMeasure (boolMeasure q)) :=
    fun j => Q_sq_subgaussian h0 h1 hp1 hp2 k _
  have hmain := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hX (s := Finset.univ)
    (c := fun _ : Fin n => subGnn k) (fun j _ => hsub j) hε
  exact hmain

end

end LocSum
