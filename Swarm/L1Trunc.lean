/-
  **`locsum`, layer 1: the truncated stationary potential on the actual mark row.**

  `Q p k x ω` is the `k`-th truncation of the paper's stationary potential

      h^*(x) = 1 + 2 sum_{q>=1} prod_{u<q} rho(x-u),      rho(x) = (1-omega(x))/omega(x)

  at site `x` of the i.i.d. mark row `ω : ℕ → Bool`, namely `h^*_{k-1}` in the paper's
  indexing (`k` marks, i.e. the sites `x-k+1, …, x`).  This file proves the deterministic
  facts:

  * `Q_zero`, `Q_one`, and the range bounds `0 <= Q p k x <= 2k-1` for `k >= 1`;
  * the two exact recursions
      `Q (k+1) x = Q k x + 2 Pz x k`   and   `Q (k+1) x = 1 + rho(x) (1 + Q k (x-1))`;
  * block dependence: `Q p k x` is a function of the marks in `blkS k x` only, through the
    explicit finite functional `Qblk`, and is measurable;
  * the exact finite telescoping identity
      `Q p (k+m) x - Q p k x = Pz x k * (1 + Q p m (x-k))`.
-/
import Swarm.Imports
import Swarm.S0

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocSum

noncomputable section

variable {p : ℝ}

/-- The paper's ratio `(1 - omega)/omega` at site `n` of a mark row: `(1-p)/p` at a marked
site and `1` at an unmarked one. -/
def rat (p : ℝ) (ω : ℕ → Bool) (n : ℕ) : ℝ := if ω n then (1 - p) / p else 1

lemma rat_nonneg (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) (n : ℕ) :
    0 ≤ rat p ω n := by
  unfold rat
  split
  · exact div_nonneg (by linarith) (by linarith)
  · norm_num

lemma rat_le_one (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) (n : ℕ) :
    rat p ω n ≤ 1 := by
  unfold rat
  split
  · rw [div_le_one (by linarith)]; linarith
  · norm_num

lemma measurable_rat (p : ℝ) (n : ℕ) : Measurable (fun ω : ℕ → Bool => rat p ω n) :=
  (measurable_of_finite (fun b : Bool => if b then (1 - p) / p else 1)).comp
    (measurable_pi_apply n)

/-- The product `Pz x k = prod_{u<k} rho(x-u)` of display `(hstat)`. -/
def Pz (p : ℝ) (x k : ℕ) (ω : ℕ → Bool) : ℝ := ∏ u ∈ Finset.range k, rat p ω (x - u)

lemma measurable_Pz (p : ℝ) (x k : ℕ) : Measurable (Pz p x k) :=
  Finset.measurable_prod _ fun u _ => measurable_rat p _

lemma Pz_nonneg (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (x k : ℕ) (ω : ℕ → Bool) :
    0 ≤ Pz p x k ω :=
  Finset.prod_nonneg fun u _ => rat_nonneg hp1 hp2 ω _

lemma Pz_le_one (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (x k : ℕ) (ω : ℕ → Bool) :
    Pz p x k ω ≤ 1 :=
  Finset.prod_le_one (fun u _ => rat_nonneg hp1 hp2 ω _) (fun u _ => rat_le_one hp1 hp2 ω _)

@[simp] lemma Pz_zero (p : ℝ) (x : ℕ) (ω : ℕ → Bool) : Pz p x 0 ω = 1 := by
  simp [Pz]

/-- The one-step factorisation `Pz x (k+1) = rho(x) * Pz (x-1) k`. -/
lemma Pz_succ (p : ℝ) (x k : ℕ) (ω : ℕ → Bool) :
    Pz p x (k + 1) ω = rat p ω x * Pz p (x - 1) k ω := by
  have h := Finset.prod_range_succ' (fun u => rat p ω (x - u)) k
  simp only [Pz]
  rw [h, Nat.sub_zero, mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun u _ => by rw [Nat.add_comm u 1, Nat.sub_sub])

lemma Pz_add (p : ℝ) (x k m : ℕ) (ω : ℕ → Bool) :
    Pz p x (k + m) ω = Pz p x k ω * Pz p (x - k) m ω := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 from by ring, Pz_succ, ih (x - 1), Pz_succ, Nat.sub_sub]
    ring

/-- The partial sum `Gsum = sum_{j<k} Pz x j = (Q + 1)/2`. -/
def Gsum (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) : ℝ := ∑ j ∈ Finset.range k, Pz p x j ω

/-- The `k`-th truncation of the stationary potential at site `x`. -/
def Q (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) : ℝ := 2 * Gsum p k x ω - 1

lemma measurable_Q (p : ℝ) (k x : ℕ) : Measurable (Q p k x) := by
  unfold Q Gsum
  exact Measurable.sub (Measurable.const_mul (Finset.measurable_sum _ fun j _ =>
    measurable_Pz p x j) 2) measurable_const

@[simp] lemma Q_zero (p : ℝ) (x : ℕ) (ω : ℕ → Bool) : Q p 0 x ω = -1 := by
  simp [Q, Gsum]

@[simp] lemma Q_one (p : ℝ) (x : ℕ) (ω : ℕ → Bool) : Q p 1 x ω = 1 := by
  simp [Q, Gsum]
  norm_num

lemma Q_nonneg (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (hk : 1 ≤ k)
    (ω : ℕ → Bool) : 0 ≤ Q p k x ω := by
  have hmem : 0 ∈ Finset.range k := Finset.mem_range.2 hk
  have hnn : ∀ j ∈ Finset.range k, 0 ≤ Pz p x j ω := fun j _ => Pz_nonneg hp1 hp2 x j ω
  have hle : (1 : ℝ) ≤ Gsum p k x ω := by
    have h := Finset.single_le_sum hnn hmem
    simpa [Gsum] using h
  unfold Q
  linarith

lemma Q_le (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (ω : ℕ → Bool) :
    Q p k x ω ≤ 2 * (k : ℝ) - 1 := by
  have hb : ∀ j ∈ Finset.range k, Pz p x j ω ≤ 1 := fun j _ => Pz_le_one hp1 hp2 x j ω
  have h := Finset.sum_le_sum hb
  have h2 : (∑ _j ∈ Finset.range k, (1 : ℝ)) = (k : ℝ) := by simp
  rw [h2] at h
  unfold Q Gsum
  linarith

lemma Q_abs_le (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (ω : ℕ → Bool) :
    |Q p k x ω| ≤ 2 * (k : ℝ) + 1 := by
  have hle := Q_le hp1 hp2 k x ω
  have hge : -1 ≤ Q p k x ω := by
    have hnn : 0 ≤ Gsum p k x ω :=
      Finset.sum_nonneg fun j _ => Pz_nonneg hp1 hp2 x j ω
    unfold Q
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Recursion (A): adding the `k`-th product. -/
lemma Q_succ' (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    Q p (k + 1) x ω = Q p k x ω + 2 * Pz p x k ω := by
  have h := Finset.sum_range_succ (fun j => Pz p x j ω) k
  unfold Q Gsum
  rw [h]
  ring

/-- Recursion (B), the paper's `(projh)`: `Q (k+1) x = 1 + rho(x)(1 + Q k (x-1))`. -/
lemma Q_succ (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    Q p (k + 1) x ω = 1 + rat p ω x * (1 + Q p k (x - 1) ω) := by
  have h1 : Gsum p (k + 1) x ω = 1 + rat p ω x * Gsum p k (x - 1) ω := by
    have hs := Finset.sum_range_succ' (fun j => Pz p x j ω) k
    have hshift : (∑ j ∈ Finset.range k, Pz p x (j + 1) ω)
        = rat p ω x * (∑ j ∈ Finset.range k, Pz p (x - 1) j ω) := by
      rw [show (∑ j ∈ Finset.range k, Pz p x (j + 1) ω)
          = ∑ j ∈ Finset.range k, rat p ω x * Pz p (x - 1) j ω from
        Finset.sum_congr rfl (fun j _ => Pz_succ p x j ω), ← Finset.mul_sum]
    unfold Gsum
    rw [hs, hshift, Pz_zero]
    ring
  unfold Q
  rw [h1]
  ring

/-! ### Block dependence -/

/-- The set of sites that `Q p k x` depends on. -/
def blkS (k x : ℕ) : Finset ℕ := (Finset.range k).image (fun u => x - u)

lemma mem_blkS {k x u : ℕ} (hu : u < k) : x - u ∈ blkS k x :=
  Finset.mem_image.2 ⟨u, Finset.mem_range.2 hu, rfl⟩

/-- Extend a function on a finite set of sites to all of `ℕ` by `false`. -/
def ext (s : Finset ℕ) (v : (↑s) → Bool) : ℕ → Bool := fun n => if h : n ∈ s then v ⟨n, h⟩ else false

lemma ext_restrict (s : Finset ℕ) (ω : ℕ → Bool) (n : ℕ) (hn : n ∈ s) :
    ext s (Finset.restrict s ω) n = ω n := by
  simp [ext, hn, Finset.restrict]

/-- `Q p k x` as a functional of the mark block `blkS k x`. -/
def Qblk (p : ℝ) (k x : ℕ) (v : (↑(blkS k x)) → Bool) : ℝ :=
  2 * (∑ j ∈ Finset.range k, ∏ u ∈ Finset.range j, rat p (ext (blkS k x) v) (x - u)) - 1

lemma measurable_Qblk (p : ℝ) (k x : ℕ) : Measurable (Qblk p k x) :=
  measurable_of_finite _

lemma Qblk_eq_Q (p : ℝ) (k x : ℕ) (v : (↑(blkS k x)) → Bool) :
    Qblk p k x v = Q p k x (ext (blkS k x) v) := rfl

lemma Q_congr (p : ℝ) (k x : ℕ) {ω ω' : ℕ → Bool} (h : ∀ u < k, ω (x - u) = ω' (x - u)) :
    Q p k x ω = Q p k x ω' := by
  have hsum : (∑ j ∈ Finset.range k, ∏ u ∈ Finset.range j, rat p ω (x - u))
      = ∑ j ∈ Finset.range k, ∏ u ∈ Finset.range j, rat p ω' (x - u) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.prod_congr rfl ?_
    intro u hu
    have hu' : u < k := lt_trans (Finset.mem_range.1 hu) (Finset.mem_range.1 hj)
    simp only [rat]
    rw [h u hu']
  unfold Q Gsum Pz
  rw [hsum]

lemma Q_eq_Qblk (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    Q p k x ω = Qblk p k x (Finset.restrict (blkS k x) ω) := by
  rw [Qblk_eq_Q]
  exact (Q_congr p k x (fun u hu => ext_restrict (blkS k x) ω (x - u) (mem_blkS hu))).symm

/-- **The exact finite `(hstat)` telescoping**:
`h^*_{k+m-1}(x) - h^*_{k-1}(x) = Pz x k * (1 + h^*_{m-1}(x-k))`. -/
lemma Q_telescope (p : ℝ) (m k x : ℕ) (ω : ℕ → Bool) :
    Q p (k + m) x ω - Q p k x ω = Pz p x k ω * (1 + Q p m (x - k) ω) := by
  induction k generalizing x with
  | zero =>
    simp [Q, Gsum, Pz]
  | succ k ih =>
    have h1 : Q p (k + 1 + m) x ω = 1 + rat p ω x * (1 + Q p (k + m) (x - 1) ω) := by
      rw [show k + 1 + m = (k + m) + 1 from by ring, Q_succ]
    have h2 : Q p (k + 1) x ω = 1 + rat p ω x * (1 + Q p k (x - 1) ω) := Q_succ p k x ω
    have hdiff : Q p (k + 1 + m) x ω - Q p (k + 1) x ω
        = rat p ω x * (Q p (k + m) (x - 1) ω - Q p k (x - 1) ω) := by
      rw [h1, h2]; ring
    rw [hdiff, ih (x - 1)]
    have h4 : Pz p x (k + 1) ω = rat p ω x * Pz p (x - 1) k ω := Pz_succ p x k ω
    have h5 : x - (k + 1) = x - 1 - k := by omega
    rw [h4, h5]
    ring

end

end LocSum
