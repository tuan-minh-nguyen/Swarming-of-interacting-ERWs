/-
# Clamped piecewise-affine interpolation on a finite uniform grid

The construction is internal to this file: no uninstalled piecewise-linear
module is used. Each recursive segment is clamped before and after its
endpoints. `interp_on_segment` proves the actual affine formula on every raw
block, including its two boundary cases. The global Lipschitz proof uses a
separate two-sided gluing lemma, not a sum of segment constants.
-/
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open Set
open scoped BoundedContinuousFunction NNReal

namespace FluidInterpolation

noncomputable section

/-- The affine coordinate relative to `[c,c+h]`, clamped to `[0,1]`. -/
def knotFraction (c h t : ℝ) : ℝ :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one ((t - c) / h) : ℝ)

/-- One affine grid segment, extended by its two endpoint values. -/
def segment (left right c h t : ℝ) : ℝ :=
  AffineMap.lineMap left right (knotFraction c h t)

lemma knotFraction_mem (c h t : ℝ) : knotFraction c h t ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one ((t - c) / h)).2

lemma knotFraction_eq_zero {c h t : ℝ} (hh : 0 ≤ h) (ht : t ≤ c) :
    knotFraction c h t = 0 := by
  have hq : (t - c) / h ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hh
  simp [knotFraction, Set.projIcc_of_le_left zero_le_one hq]

lemma knotFraction_eq_one {c h t : ℝ} (hh : 0 < h) (ht : c + h ≤ t) :
    knotFraction c h t = 1 := by
  have hq : 1 ≤ (t - c) / h := (le_div_iff₀ hh).2 (by linarith)
  simp [knotFraction, Set.projIcc_of_right_le zero_le_one hq]

lemma knotFraction_of_mem {c h t : ℝ} (hh : 0 < h) (ht : t ∈ Set.Icc c (c + h)) :
    knotFraction c h t = (t - c) / h := by
  have hq : (t - c) / h ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hh.le
    · exact (div_le_iff₀ hh).2 (by linarith [ht.2])
  simp [knotFraction, Set.projIcc_of_mem zero_le_one hq]

lemma segment_mem_Icc {left right c h t lo hi : ℝ}
    (hleft : left ∈ Set.Icc lo hi) (hright : right ∈ Set.Icc lo hi) :
    segment left right c h t ∈ Set.Icc lo hi := by
  exact (convex_Icc lo hi).lineMap_mem hleft hright (knotFraction_mem c h t)

lemma segment_eq_left_of_le {left right c h t : ℝ} (hh : 0 ≤ h) (ht : t ≤ c) :
    segment left right c h t = left := by
  rw [segment, knotFraction_eq_zero hh ht, AffineMap.lineMap_apply_zero]

lemma segment_eq_right_of_le {left right c h t : ℝ} (hh : 0 < h) (ht : c + h ≤ t) :
    segment left right c h t = right := by
  rw [segment, knotFraction_eq_one hh ht, AffineMap.lineMap_apply_one]

lemma segment_at_left (left right c h : ℝ) : segment left right c h c = left := by
  simp [segment, knotFraction, AffineMap.lineMap_apply_zero]

lemma segment_at_right (left right c h : ℝ) (hh : 0 < h) :
    segment left right c h (c + h) = right := by
  exact segment_eq_right_of_le hh le_rfl

lemma segment_eq_affine_of_mem {left right c h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Icc c (c + h)) :
    segment left right c h t = AffineMap.lineMap left right ((t - c) / h) := by
  rw [segment, knotFraction_of_mem hh ht]

lemma continuous_knotFraction (c h : ℝ) : Continuous (knotFraction c h) := by
  unfold knotFraction
  fun_prop

lemma continuous_segment (left right c h : ℝ) : Continuous (segment left right c h) := by
  exact AffineMap.lineMap_continuous.comp (continuous_knotFraction c h)

lemma dist_knotFraction_le {c h : ℝ} (hh : 0 < h) (x y : ℝ) :
    dist (knotFraction c h x) (knotFraction c h y) ≤ dist x y / h := by
  calc
    dist (knotFraction c h x) (knotFraction c h y) ≤
        dist ((x - c) / h) ((y - c) / h) := by
      change dist (Set.projIcc 0 1 zero_le_one ((x - c) / h))
        (Set.projIcc 0 1 zero_le_one ((y - c) / h)) ≤ _
      simpa only [NNReal.coe_one, one_mul] using
        (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num)).dist_le_mul
          ((x - c) / h) ((y - c) / h)
    _ = dist x y / h := by
      have heq : (x - c) - (y - c) = x - y := by ring
      simp only [Real.dist_eq]
      rw [div_sub_div_same, heq, abs_div, abs_of_pos hh]

lemma lipschitz_segment {left right c h : ℝ} (hh : 0 < h)
    (hd : dist left right ≤ h) : LipschitzWith 1 (segment left right c h) := by
  apply LipschitzWith.mk_one
  intro x y
  calc
    dist (segment left right c h x) (segment left right c h y) =
        dist (knotFraction c h x) (knotFraction c h y) * dist left right := by
      exact dist_lineMap_lineMap left right _ _
    _ ≤ (dist x y / h) * h := by
      exact mul_le_mul (dist_knotFraction_le hh x y) hd dist_nonneg
        (div_nonneg dist_nonneg hh.le)
    _ = dist x y := by field_simp [hh.ne']

/-- Compatible one-Lipschitz functions remain one-Lipschitz when glued at a
real-time cut. The proof covers both orders of points across the cut. -/
lemma lipschitzWith_one_ite_le (f g : ℝ → ℝ) (c : ℝ)
    (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) (hfg : f c = g c) :
    LipschitzWith 1 (fun t => if t ≤ c then f t else g t) := by
  have hcross : ∀ {x y : ℝ}, x ≤ c → ¬y ≤ c → dist (f x) (g y) ≤ dist x y := by
    intro x y hx hy
    have hxy : x ≤ y := hx.trans (le_of_not_ge hy)
    have hxc : dist x c = c - x := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx)]
      ring
    have hcy : dist c y = y - c := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hy))]
      ring
    have hxy' : dist x y = y - x := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    have hdist : dist x c + dist c y = dist x y := by rw [hxc, hcy, hxy']; ring
    calc
      dist (f x) (g y) ≤ dist (f x) (f c) + dist (f c) (g y) := dist_triangle _ _ _
      _ = dist (f x) (f c) + dist (g c) (g y) := by rw [hfg]
      _ ≤ dist x c + dist c y := by
        exact add_le_add (by simpa only [NNReal.coe_one, one_mul] using hf.dist_le_mul x c)
          (by simpa only [NNReal.coe_one, one_mul] using hg.dist_le_mul c y)
      _ = dist x y := hdist
  apply LipschitzWith.mk_one
  intro x y
  by_cases hx : x ≤ c <;> by_cases hy : y ≤ c
  · simpa only [if_pos hx, if_pos hy, NNReal.coe_one, one_mul] using hf.dist_le_mul x y
  · simpa only [if_pos hx, if_neg hy] using hcross hx hy
  · simpa only [if_neg hx, if_pos hy, dist_comm] using hcross hy hx
  · simpa only [if_neg hx, if_neg hy, NNReal.coe_one, one_mul] using hg.dist_le_mul x y

/-- Piecewise-affine interpolation of `a 0, ..., a N` on grid spacing `h`.
The function is constant below zero and above `N*h`. -/
def interp (a : ℕ → ℝ) (h : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => a 0
  | N + 1 => fun t => if t ≤ (N : ℝ) * h then interp a h N t
      else segment (a N) (a (N + 1)) ((N : ℝ) * h) h t

@[simp] lemma interp_at_last (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    interp a h N ((N : ℝ) * h) = a N := by
  cases N with
  | zero => simp [interp]
  | succ N =>
      have hnot : ¬((N + 1 : ℕ) : ℝ) * h ≤ (N : ℝ) * h := by
        push_cast
        nlinarith
      simp only [interp, if_neg hnot]
      have heq : ((N + 1 : ℕ) : ℝ) * h = (N : ℝ) * h + h := by push_cast; ring
      rw [heq]
      exact segment_at_right (a N) (a (N + 1)) ((N : ℝ) * h) h hh

lemma continuous_interp (a : ℕ → ℝ) (h : ℝ) (hh : 0 < h) : ∀ N,
    Continuous (interp a h N)
  | 0 => by simpa [interp] using (continuous_const : Continuous (fun _ : ℝ => a 0))
  | N + 1 => by
    simp only [interp]
    apply Continuous.if_le (continuous_interp a h hh N) (continuous_segment _ _ _ _)
      continuous_id continuous_const
    rintro x rfl
    rw [interp_at_last a hh, segment_at_left]

lemma lipschitz_interp (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h)
    (hstep : ∀ k, dist (a (k + 1)) (a k) ≤ h) : ∀ N, LipschitzWith 1 (interp a h N)
  | 0 => by simpa [interp] using (LipschitzWith.const' (a 0) :
      LipschitzWith (1 : ℝ≥0) (fun _ : ℝ => a 0))
  | N + 1 => by
    have hfg : interp a h N ((N : ℝ) * h) =
        segment (a N) (a (N + 1)) ((N : ℝ) * h) h ((N : ℝ) * h) := by
      rw [interp_at_last a hh, segment_at_left]
    have hseg : LipschitzWith 1 (segment (a N) (a (N + 1)) ((N : ℝ) * h) h) := by
      apply lipschitz_segment hh
      simpa only [dist_comm] using hstep N
    have hglue := lipschitzWith_one_ite_le _ _ ((N : ℝ) * h)
      (lipschitz_interp a hh hstep N) hseg hfg
    simpa only [interp] using hglue

lemma interp_at_knot (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h) : ∀ {N k : ℕ}, k ≤ N →
    interp a h N ((k : ℝ) * h) = a k := by
  intro N
  induction N with
  | zero =>
      intro k hk
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [interp]
  | succ N ih =>
      intro k hk
      by_cases hkN : k ≤ N
      · have hkt : (k : ℝ) * h ≤ (N : ℝ) * h :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) hh.le
        simp only [interp, if_pos hkt]
        exact ih hkN
      · have hkeq : k = N + 1 := by omega
        subst k
        have hnot : ¬((N + 1 : ℕ) : ℝ) * h ≤ (N : ℝ) * h := by
          push_cast
          nlinarith
        simp only [interp, if_neg hnot]
        have heq : ((N + 1 : ℕ) : ℝ) * h = (N : ℝ) * h + h := by push_cast; ring
        rw [heq]
        exact segment_at_right (a N) (a (N + 1)) ((N : ℝ) * h) h hh

@[simp] lemma interp_at_zero (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h) : ∀ N,
    interp a h N 0 = a 0
  | 0 => rfl
  | N + 1 => by
      have hn : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg N) hh.le
      simp only [interp, if_pos hn]
      exact interp_at_zero a hh N

lemma interp_eq_left_of_nonpos (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h) {t : ℝ}
    (ht : t ≤ 0) : ∀ N, interp a h N t = a 0
  | 0 => rfl
  | N + 1 => by
      have hn : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg N) hh.le
      simp only [interp, if_pos (ht.trans hn)]
      exact interp_eq_left_of_nonpos a hh ht N

lemma interp_eq_right_of_le (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h) {N : ℕ} {t : ℝ}
    (ht : (N : ℝ) * h ≤ t) : interp a h N t = a N := by
  cases N with
  | zero => simp [interp]
  | succ N =>
      have hn : (N : ℝ) * h < ((N + 1 : ℕ) : ℝ) * h := by
        push_cast
        nlinarith
      simp only [interp, if_neg (not_le_of_gt (hn.trans_le ht))]
      apply segment_eq_right_of_le hh
      calc
        (N : ℝ) * h + h = ((N + 1 : ℕ) : ℝ) * h := by push_cast; ring
        _ ≤ t := ht

lemma interp_mem_Icc (a : ℕ → ℝ) (h lo hi : ℝ) : ∀ N,
    (∀ k, k ≤ N → a k ∈ Set.Icc lo hi) → ∀ t, interp a h N t ∈ Set.Icc lo hi := by
  intro N
  induction N with
  | zero =>
      intro hb t
      simpa [interp] using hb 0 le_rfl
  | succ N ih =>
      intro hb t
      simp only [interp]
      split_ifs
      · exact ih (fun k hk => hb k (Nat.le_succ_of_le hk)) t
      · exact segment_mem_Icc (hb N (Nat.le_succ N)) (hb (N + 1) le_rfl)

/-- Literal affine sampled-point formula on every adjacent raw segment. -/
lemma interp_on_segment (a : ℕ → ℝ) {h : ℝ} (hh : 0 < h) : ∀ {N k : ℕ}, k < N →
    ∀ {t : ℝ}, t ∈ Set.Icc ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h) →
      interp a h N t = segment (a k) (a (k + 1)) ((k : ℝ) * h) h t := by
  intro N
  induction N with
  | zero => intro k hk; omega
  | succ N ih =>
      intro k hk t ht
      by_cases hkN : k = N
      · subst k
        by_cases hleft : t ≤ (N : ℝ) * h
        · have heq : t = (N : ℝ) * h := le_antisymm hleft ht.1
          subst t
          simp only [interp, if_pos le_rfl]
          rw [interp_at_last a hh, segment_at_left]
        · simp only [interp, if_neg hleft]
      · have hklt : k < N := by omega
        have hk1 : k + 1 ≤ N := by omega
        have htN : t ≤ (N : ℝ) * h := ht.2.trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hh.le)
        simp only [interp, if_pos htN]
        exact ih hklt ht

/-- Package the compact-time restriction as a bounded continuous function. -/
def bundle {a : ℕ → ℝ} {h T : ℝ} (N : ℕ) (hc : Continuous (interp a h N)) :
    Set.Icc (0 : ℝ) T →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => interp a h N t, hc.comp continuous_subtype_val⟩

@[simp] lemma bundle_apply {a : ℕ → ℝ} {h T : ℝ} (N : ℕ)
    (hc : Continuous (interp a h N)) (t : Set.Icc (0 : ℝ) T) :
    bundle N hc t = interp a h N t := rfl

lemma lipschitz_bundle {a : ℕ → ℝ} {h T : ℝ} (N : ℕ)
    (hc : Continuous (interp a h N)) (hl : LipschitzWith 1 (interp a h N)) :
    LipschitzWith 1 (bundle (T := T) N hc) := by
  apply LipschitzWith.mk_one
  intro x y
  change dist (interp a h N (x : ℝ)) (interp a h N (y : ℝ)) ≤ dist (x : ℝ) (y : ℝ)
  simpa only [NNReal.coe_one, one_mul] using hl.dist_le_mul (x : ℝ) (y : ℝ)

end
end FluidInterpolation
