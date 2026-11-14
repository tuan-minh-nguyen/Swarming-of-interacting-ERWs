/-
# The fluid-level deterministic core of the source's `(blkprob)`

Self-contained module (Mathlib only).  It formalises two facts about the source's own fluid-limit
objects as they appear in the proof of Proposition `tight` of
`attachments/improving-and-polishing-the-wcjf/main_1d.tex`: the display `(fluid)`, the running
maxima `m_i(u) = max (m_i(0)) (x_i(u))` and `R(u) = max_i m_i(u)`, the fractional occupation
display `(lococc)`, the ballistic lower bound `(Rlower)`, and the pointwise coincidence
`(coincide)`.

1. **`rlower_of_fractional_occupation` (positive).**  `(Rlower)` `R(t) ≥ 3t/(8C) - 3` follows from
   `(lococc)` *including its `1/8` saving*, for fluid limit functions, by the source's own pair
   count: at every time at least one of the two indicators `1{x_i ≤ m_j}`, `1{x_j ≤ m_i}` fires,
   so the two occupations add up to the elapsed time, while each is at most `t/8 + C(...)`; the
   height bracket is at most `2R(t) + 6` by the start normalisation
   `-1 ≤ x_i(0) ≤ m_i(0) ≤ 0`.

2. **`fluid_facts_do_not_force_coincide` (obstruction).**  The remaining fluid facts used before
   `(coincide)` — `(fluid)` at velocity `q = 2p-1 ∈ (0,1)`, the start normalisation
   `-1 ≤ x_i(0) ≤ 0` with `R(0) = 0`, and `(Rlower)` — do **not** imply `(coincide)`.
   Countermodel: one walker rises at velocity `q` for ever, the other rises at velocity `q` up to
   the coincidence time `s` and then stands still.

3. **`fluid_facts_do_not_force_join_rule` (obstruction, meeting rule).**  The same countermodel
   satisfies `(fluid)`, the start normalisation and `(Rlower)`, and yet its leader class never
   grows: the paper's meeting rule (`FluidMerge.JoinRuleFrom`, with any constant `b`) fails.  So
   that rule — the residual input of the one-coalescence-time route to `(half)` — cannot be
   derived from the compactness-limit facts either.

4. **`stall_occupation_full`, `stall_breaks_fractional_occupation`.**  In that countermodel the
   occupation of `{x_1 ≤ m_0}` is the whole interval, density `1` rather than `1/8`: the model is
   excluded by the `1/8` of `(lococc)` and by nothing else in the list of (1).  Hence the
   occupation input `(lococc)` is indispensable for the coalescence step of the source's block
   argument, and no argument resting on `(fluid)` + `(Rlower)` + the start normalisation alone can
   produce `(coincide)` — hence none can produce `(half)`/`(blkprob)` by that route.
-/
import Swarm.Imports

open Set MeasureTheory

namespace WCJFFluidCore

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## The source's fluid objects -/

/-- The source's `(fluid)` display at velocity `q`: every fluid coordinate is nondecreasing and
grows by at most `q (t - s)`. -/
def FluidOn (x : ι → ℝ → ℝ) (q : ℝ) : Prop :=
  ∀ (i : ι) (s t : ℝ), 0 ≤ s → s ≤ t → 0 ≤ x i t - x i s ∧ x i t - x i s ≤ q * (t - s)

/-- The source's running maximum of a single walker, `m_i(u) = max (m_i(0)) (x_i(u))`. -/
def mI (x : ι → ℝ → ℝ) (m0 : ι → ℝ) (i : ι) (u : ℝ) : ℝ := max (m0 i) (x i u)

/-- The source's pointwise coincidence `(coincide)`: two walkers that agree at a fluid time `s`
agree at every later fluid time up to `T`. -/
def CoincideOn (x : ι → ℝ → ℝ) (s T : ℝ) : Prop :=
  ∀ i j : ι, x i s = x j s → ∀ u : ℝ, s ≤ u → u ≤ T → x i u = x j u

/-! ## 1. `(Rlower)` from the fractional occupation display `(lococc)` -/

/-- `(volume (A ∪ B)).toReal ≤ (volume A).toReal + (volume B).toReal` for sets bounded by
`Ioo 0 t`. -/
lemma volume_union_toReal_le {A B : Set ℝ} {t : ℝ} (hA : A ⊆ Ioo 0 t) (hB : B ⊆ Ioo 0 t) :
    (volume (A ∪ B)).toReal ≤ (volume A).toReal + (volume B).toReal := by
  have hfin : volume (Ioo (0:ℝ) t) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hA)
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hB)
  have hmono : volume (A ∪ B) ≤ volume A + volume B := measure_union_le A B
  have hsum : volume A + volume B ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩
  have h1 : (volume (A ∪ B)).toReal ≤ (volume A + volume B).toReal :=
    ENNReal.toReal_mono hsum hmono
  rwa [ENNReal.toReal_add hAfin hBfin] at h1

/-- The source's pair count: at every time at least one of `x_i ≤ m_j`, `x_j ≤ m_i` holds. -/
lemma occ_pair_cover (x : ι → ℝ → ℝ) (m0 : ι → ℝ) (i j : ι) (u : ℝ) :
    x i u ≤ mI x m0 j u ∨ x j u ≤ mI x m0 i u := by
  by_cases h : x i u ≤ mI x m0 j u
  · exact Or.inl h
  · right
    have h' : mI x m0 j u < x i u := lt_of_not_ge h
    have h1 : x j u ≤ mI x m0 j u := le_max_right _ _
    exact le_trans (le_trans h1 h'.le) (le_max_right _ _)

/-- **The source's `(Rlower)` from the fractional occupation display `(lococc)`.**

`hocc` is the fluid-level content of `(lococc)` read from time `0`: the occupation of
`{x_i ≤ m_j}` is at most `c t` plus `C` times the source's three height terms
`(m_i(t) - m_i(0)) + (m_i(0) - x_i(0)) + (m_i(0) - m_j(0))_+`.  By the start normalisation each
of those is at most `R(t) + 1`, `1`, `1`, so a pair's two occupations add up to at most
`2ct + C (2R(t) + 6)` while they cover the whole interval: `(1 - 2c) t ≤ C (2R(t) + 6)`, i.e.
`R(t) ≥ (1 - 2c) t/(2C) - 3`.

The source's coefficient is `c = 1/8`, giving `(Rlower)` `R(t) ≥ 3t/(8C) - 3`
(`rlower_of_fractional_occupation_of_eighth`).  The argument only needs `c < 1/2`, so the exact
range of the `(lococc)` saving that yields a ballistic lower bound is recorded here.

`Rf` is the source's `R(u) = max_i m_i(u)`; only `hR` (`m_i(u) ≤ R(u)` for every `i`) is used, and
for the maximum itself that is definitional. -/
theorem rlower_of_occupation_coefficient
    (x : ι → ℝ → ℝ) (m0 : ι → ℝ) (Rf : ℝ → ℝ) {c C : ℝ} (_hc : 2 * c < 1) (hC : 1 ≤ C)
    (hx0 : ∀ i, -1 ≤ x i 0 ∧ x i 0 ≤ 0)
    (hm0lo : ∀ i, -1 ≤ m0 i) (hm0hi : ∀ i, m0 i ≤ 0)
    (hR : ∀ (i : ι) (u : ℝ), mI x m0 i u ≤ Rf u)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hocc : ∀ (i j : ι), i ≠ j → ∀ t : ℝ, 0 < t →
      (volume {u : ℝ | u ∈ Ioo 0 t ∧ x i u ≤ mI x m0 j u}).toReal ≤
        c * t + C * ((mI x m0 i t - m0 i) + (m0 i - x i 0) + max (m0 i - m0 j) 0)) :
    ∀ t : ℝ, 0 < t → (1 - 2 * c) * t / (2 * C) - 3 ≤ Rf t := by
  intro t ht
  set A : Set ℝ := {u : ℝ | u ∈ Ioo 0 t ∧ x i₀ u ≤ mI x m0 j₀ u} with hAdef
  set B : Set ℝ := {u : ℝ | u ∈ Ioo 0 t ∧ x j₀ u ≤ mI x m0 i₀ u} with hBdef
  have hAsub : A ⊆ Ioo (0:ℝ) t := fun u hu => hu.1
  have hBsub : B ⊆ Ioo (0:ℝ) t := fun u hu => hu.1
  have hcover : Ioo (0:ℝ) t ⊆ A ∪ B := by
    intro u hu
    rcases occ_pair_cover x m0 i₀ j₀ u with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  have hfin : volume (Ioo (0:ℝ) t) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hAsub)
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hBsub)
  have hUfin : volume (A ∪ B) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) (measure_union_le A B)
  have hvol : (volume (Ioo (0:ℝ) t)).toReal ≤ (volume A).toReal + (volume B).toReal :=
    le_trans (ENNReal.toReal_mono hUfin (measure_mono hcover))
      (volume_union_toReal_le hAsub hBsub)
  have hvolt : (volume (Ioo (0:ℝ) t)).toReal = t := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hAc : (volume A).toReal ≤
      c * t + C * ((mI x m0 i₀ t - m0 i₀) + (m0 i₀ - x i₀ 0) + max (m0 i₀ - m0 j₀) 0) :=
    hocc i₀ j₀ hij t ht
  have hBc : (volume B).toReal ≤
      c * t + C * ((mI x m0 j₀ t - m0 j₀) + (m0 j₀ - x j₀ 0) + max (m0 j₀ - m0 i₀) 0) :=
    hocc j₀ i₀ (Ne.symm hij) t ht
  have hterm1 : mI x m0 i₀ t - m0 i₀ ≤ Rf t + 1 := by
    have h2 : mI x m0 i₀ t ≤ Rf t := hR i₀ t
    have h3 : -(1:ℝ) ≤ m0 i₀ := hm0lo i₀
    linarith
  have hterm2 : m0 i₀ - x i₀ 0 ≤ 1 := by
    have h3 : -(1:ℝ) ≤ x i₀ 0 := (hx0 i₀).1
    have h4 : m0 i₀ ≤ 0 := hm0hi i₀
    linarith
  have hterm3 : max (m0 i₀ - m0 j₀) 0 ≤ 1 := by
    have h4 : m0 i₀ ≤ 0 := hm0hi i₀
    have h5 : -(1:ℝ) ≤ m0 j₀ := hm0lo j₀
    have h6 : m0 i₀ - m0 j₀ ≤ 1 := by linarith
    exact max_le h6 zero_le_one
  have hterm1' : mI x m0 j₀ t - m0 j₀ ≤ Rf t + 1 := by
    have h2 : mI x m0 j₀ t ≤ Rf t := hR j₀ t
    have h3 : -(1:ℝ) ≤ m0 j₀ := hm0lo j₀
    linarith
  have hterm2' : m0 j₀ - x j₀ 0 ≤ 1 := by
    have h3 : -(1:ℝ) ≤ x j₀ 0 := (hx0 j₀).1
    have h4 : m0 j₀ ≤ 0 := hm0hi j₀
    linarith
  have hterm3' : max (m0 j₀ - m0 i₀) 0 ≤ 1 := by
    have h4 : m0 j₀ ≤ 0 := hm0hi j₀
    have h5 : -(1:ℝ) ≤ m0 i₀ := hm0lo i₀
    have h6 : m0 j₀ - m0 i₀ ≤ 1 := by linarith
    exact max_le h6 zero_le_one
  have hbracket :
      ((mI x m0 i₀ t - m0 i₀) + (m0 i₀ - x i₀ 0) + max (m0 i₀ - m0 j₀) 0)
      + ((mI x m0 j₀ t - m0 j₀) + (m0 j₀ - x j₀ 0) + max (m0 j₀ - m0 i₀) 0)
      ≤ 2 * Rf t + 6 := by linarith
  have hCpos : (0:ℝ) < C := by linarith
  have hkey : (1 - 2 * c) * t ≤ C * (2 * Rf t + 6) := by
    have h1 : t ≤ (volume A).toReal + (volume B).toReal := by
      rw [← hvolt]; exact hvol
    have h2 : C * (((mI x m0 i₀ t - m0 i₀) + (m0 i₀ - x i₀ 0) + max (m0 i₀ - m0 j₀) 0)
        + ((mI x m0 j₀ t - m0 j₀) + (m0 j₀ - x j₀ 0) + max (m0 j₀ - m0 i₀) 0))
        ≤ C * (2 * Rf t + 6) := mul_le_mul_of_nonneg_left hbracket hCpos.le
    nlinarith [h1, h2]
  have hstep : (1 - 2 * c) * t / (2 * C) ≤ Rf t + 3 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * C)]
    nlinarith [hkey]
  linarith

/-- **The source's `(Rlower)` at its own coefficient `1/8`**: `R(t) ≥ 3t/(8C) - 3`. -/
theorem rlower_of_fractional_occupation
    (x : ι → ℝ → ℝ) (m0 : ι → ℝ) (Rf : ℝ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hx0 : ∀ i, -1 ≤ x i 0 ∧ x i 0 ≤ 0)
    (hm0lo : ∀ i, -1 ≤ m0 i) (hm0hi : ∀ i, m0 i ≤ 0)
    (hR : ∀ (i : ι) (u : ℝ), mI x m0 i u ≤ Rf u)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hocc : ∀ (i j : ι), i ≠ j → ∀ t : ℝ, 0 < t →
      (volume {u : ℝ | u ∈ Ioo 0 t ∧ x i u ≤ mI x m0 j u}).toReal ≤
        t / 8 + C * ((mI x m0 i t - m0 i) + (m0 i - x i 0) + max (m0 i - m0 j) 0)) :
    ∀ t : ℝ, 0 < t → 3 * t / (8 * C) - 3 ≤ Rf t := by
  have h := rlower_of_occupation_coefficient x m0 Rf (c := 1 / 8) (C := C)
    (by norm_num) hC hx0 hm0lo hm0hi hR hij ?_
  · intro t ht
    have h1 := h t ht
    have heq : (1 - 2 * (1 / 8 : ℝ)) = 3 / 4 := by norm_num
    rw [heq] at h1
    have h2 : 3 / 4 * t / (2 * C) = 3 * t / (8 * C) := by
      field_simp; ring
    rwa [h2] at h1
  · intro i j hij t ht
    have h1 := hocc i j hij t ht
    have heq : (1 / 8 : ℝ) * t = t / 8 := by ring
    rwa [heq]

/-! ## 2. The two-walker stalling model: `(fluid)` + `(Rlower)` without `(coincide)` -/

/-- Walker `0` rises at velocity `q` for ever; walker `1` rises at velocity `q` until time `s`
and then stands still. -/
noncomputable def stall (q s : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  if i = 0 then q * t else min (q * t) (q * s)

/-- The source's `R(u) = max_i m_i(u)` for the two-walker model. -/
noncomputable def R2 (x : Fin 2 → ℝ → ℝ) (m0 : Fin 2 → ℝ) (u : ℝ) : ℝ :=
  max (mI x m0 0 u) (mI x m0 1 u)

lemma R2_le_iff (x : Fin 2 → ℝ → ℝ) (m0 : Fin 2 → ℝ) (u r : ℝ) :
    R2 x m0 u ≤ r ↔ mI x m0 0 u ≤ r ∧ mI x m0 1 u ≤ r := max_le_iff

lemma stall_zero (q s t : ℝ) : stall q s 0 t = q * t := by
  unfold stall; simp

lemma stall_one (q s t : ℝ) : stall q s 1 t = min (q * t) (q * s) := by
  unfold stall; simp [show ¬ ((1 : Fin 2) = 0) from by decide]

lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma stall_nonneg {q s t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) : 0 ≤ stall q s 0 t := by
  rw [stall_zero]; exact mul_nonneg hq ht

lemma stall_one_nonneg {q s t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ stall q s 1 t := by
  rw [stall_one]; exact le_min (mul_nonneg hq ht) (mul_nonneg hq hs)

/-- `(fluid)` holds at velocity `q` for the stalling model. -/
theorem stall_fluid {q : ℝ} (hq : 0 ≤ q) (s : ℝ) : FluidOn (stall q s) q := by
  intro i s' t hs' hst
  have hmul : q * s' ≤ q * t := by
    exact mul_le_mul_of_nonneg_left hst hq
  rcases fin2_cases i with rfl | rfl
  · rw [stall_zero, stall_zero]
    constructor
    · nlinarith
    · nlinarith
  · rw [stall_one, stall_one]
    constructor
    · have h2 : min (q * s') (q * s) ≤ min (q * t) (q * s) :=
        le_min (le_trans (min_le_left _ _) hmul) (min_le_right _ _)
      linarith
    · -- upper bound
      have h1 : min (q * t) (q * s) ≤ q * t := min_le_left _ _
      by_cases hcase : q * s ≤ q * s'
      · have h2 : min (q * s') (q * s) = q * s := min_eq_right hcase
        have h3 : min (q * t) (q * s) = q * s :=
          min_eq_right (le_trans hcase hmul)
        rw [h2, h3]
        nlinarith
      · have h2 : min (q * s') (q * s) = q * s' := min_eq_left (le_of_not_ge hcase)
        rw [h2]
        nlinarith

/-- The start normalisation `-1 ≤ x_i(0) ≤ 0`: both walkers start at `0`. -/
lemma stall_start {q s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    ∀ i : Fin 2, -1 ≤ stall q s i 0 ∧ stall q s i 0 ≤ 0 := by
  intro i
  rcases fin2_cases i with rfl | rfl
  · rw [stall_zero]; constructor <;> nlinarith
  · rw [stall_one, min_eq_left (by nlinarith : q * 0 ≤ q * s)]
    constructor <;> nlinarith

/-- The running maximum of the stalling model is `q u`. -/
lemma stall_R2 {q s : ℝ} (hq : 0 < q) (_hs : 0 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    R2 (stall q s) (fun _ => 0) u = q * u := by
  have h0 : mI (stall q s) (fun _ => 0) 0 u = q * u := by
    simp only [mI]
    rw [stall_zero, max_eq_right (by nlinarith : (0:ℝ) ≤ q * u)]
  have h1 : mI (stall q s) (fun _ => 0) 1 u = min (q * u) (q * s) := by
    simp only [mI]
    rw [stall_one, max_eq_right (le_min (by nlinarith : (0:ℝ) ≤ q * u)
      (by nlinarith : (0:ℝ) ≤ q * s))]
  rw [R2, h0, h1, max_eq_left (min_le_left _ _)]

/-- The two walkers coincide at `s`. -/
lemma stall_coincide_at {q s : ℝ} (_hq : 0 ≤ q) : stall q s 0 s = stall q s 1 s := by
  rw [stall_zero, stall_one, min_eq_left le_rfl]

/-- After `s` the walkers separate for ever: `(coincide)` fails. -/
theorem stall_not_coincide {q s T : ℝ} (hq : 0 < q) (hT : s < T) :
    ¬ CoincideOn (stall q s) s T := by
  intro hC
  have h0 : stall q s 0 s = stall q s 1 s := stall_coincide_at hq.le
  have h := hC 0 1 h0 T hT.le le_rfl
  rw [stall_zero, stall_one] at h
  have h2 : q * T ≤ q * s := by rw [h]; exact min_le_right _ _
  nlinarith

/-- In the stalling model the occupation of `{x_1 ≤ m_0}` is the whole interval: density `1`,
not `1/8`. -/
theorem stall_occupation_full {q s : ℝ} (hq : 0 < q) (_hs : 0 ≤ s) {t : ℝ} (ht : 0 < t) :
    (volume {u : ℝ | u ∈ Ioo 0 t ∧ stall q s 1 u ≤ mI (stall q s) (fun _ => 0) 0 u}).toReal
      = t := by
  have hset : {u : ℝ | u ∈ Ioo 0 t ∧ stall q s 1 u ≤ mI (stall q s) (fun _ => 0) 0 u}
      = Ioo 0 t := by
    ext u
    constructor
    · intro h; exact h.1
    · intro hu
      refine ⟨hu, ?_⟩
      have hu0 : 0 ≤ u := le_of_lt hu.1
      have h1 : stall q s 1 u = min (q * u) (q * s) := stall_one q s u
      have h0 : mI (stall q s) (fun _ => 0) 0 u = q * u := by
        simp only [mI]
        rw [stall_zero, max_eq_right (by nlinarith : (0:ℝ) ≤ q * u)]
      rw [h1, h0]; exact min_le_left _ _
  rw [hset, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Consequently the shared hypothesis `hocc` of `rlower_of_fractional_occupation` **fails** for
the stalling model as soon as `C q < 7/8`: the model is excluded precisely by the `1/8` saving of
`(lococc)`, not by `(fluid)`, the start normalisation or `(Rlower)`. -/
theorem stall_breaks_fractional_occupation {q s C : ℝ} (hq : 0 < q) (hs : 0 ≤ s)
    (hC0 : 0 ≤ C) {t : ℝ} (ht : 0 < t) (hCq : C * q < 7 / 8) :
    ¬ ((volume {u : ℝ | u ∈ Ioo 0 t ∧ stall q s 1 u ≤
          mI (stall q s) (fun _ => 0) 0 u}).toReal ≤
        t / 8 + C * ((mI (stall q s) (fun _ => 0) 1 t - (0:ℝ))
          + ((0:ℝ) - stall q s 1 0) + max ((0:ℝ) - (0:ℝ)) 0)) := by
  intro h
  have hvol := stall_occupation_full hq hs ht
  have hm1 : mI (stall q s) (fun _ => 0) 1 t = min (q * t) (q * s) := by
    simp only [mI]
    rw [stall_one, max_eq_right (le_min (by nlinarith : (0:ℝ) ≤ q * t)
      (by nlinarith : (0:ℝ) ≤ q * s))]
  have hml : min (q * t) (q * s) ≤ q * t := min_le_left _ _
  have hs0 : stall q s 1 0 = 0 := by
    rw [stall_one, min_eq_left (by nlinarith : q * 0 ≤ q * s)]
    ring
  have hb : ((mI (stall q s) (fun _ => 0) 1 t - (0:ℝ))
      + ((0:ℝ) - stall q s 1 0) + max ((0:ℝ) - (0:ℝ)) 0) ≤ q * t := by
    rw [hm1, hs0]; simp only [sub_zero, max_self]; nlinarith
  have hle : t / 8 + C * ((mI (stall q s) (fun _ => 0) 1 t - (0:ℝ))
      + ((0:ℝ) - stall q s 1 0) + max ((0:ℝ) - (0:ℝ)) 0) ≤ t / 8 + C * (q * t) := by
    have h2 : C * ((mI (stall q s) (fun _ => 0) 1 t - (0:ℝ))
        + ((0:ℝ) - stall q s 1 0) + max ((0:ℝ) - (0:ℝ)) 0) ≤ C * (q * t) :=
      mul_le_mul_of_nonneg_left hb hC0
    exact add_le_add (le_refl _) h2
  have : t ≤ t / 8 + C * (q * t) := by
    rw [hvol] at h
    linarith
  have hCt : C * (q * t) = (C * q) * t := by ring
  rw [hCt] at this
  nlinarith

/-! ## 2b. `(fluid)` allows the diagnostic: the spread can grow at the maximal rate for ever -/

/-- Under `(fluid)` the diagnostic `x_i - x_j` grows at most at velocity `q` on top of its value at
the start of the window. -/
theorem fluid_spread_le (x : ι → ℝ → ℝ) {q : ℝ} (h : FluidOn x q)
    {i j : ι} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    x i t - x j t ≤ (x i s - x j s) + q * (t - s) := by
  obtain ⟨h1, h2⟩ := h i s t hs hst
  obtain ⟨h3, -⟩ := h j s t hs hst
  linarith

/-- In the stalling model the diagnostic grows at exactly the maximal velocity `q` after the
coincidence time: `(fluid)` alone therefore implies no contraction at all. -/
theorem stall_spread_grows {q s : ℝ} (hq : 0 < q) {u : ℝ} (hu : s ≤ u) :
    stall q s 0 u - stall q s 1 u = q * (u - s) := by
  rw [stall_zero, stall_one, min_eq_right (by nlinarith : q * s ≤ q * u)]
  ring

/-- In the stalling model the running maximum equals the current position from time `0` on,
i.e. the model also satisfies the first half of the source's `(fluidmax)` display
`m_i(u) = x_i(u)`. -/
lemma stall_mI_eq {q s : ℝ} (hq : 0 < q) (hs : 0 ≤ s) {i : Fin 2} {u : ℝ} (hu : 0 ≤ u) :
    mI (stall q s) (fun _ => 0) i u = stall q s i u := by
  simp only [mI]
  rcases fin2_cases i with rfl | rfl
  · rw [stall_zero]
    exact max_eq_right (by nlinarith : (0:ℝ) ≤ q * u)
  · rw [stall_one]
    exact max_eq_right (le_min (by nlinarith : (0:ℝ) ≤ q * u) (by nlinarith : (0:ℝ) ≤ q * s))

/-- **The stalling model witnesses every fluid fact of the source except `(lococc)`.**  At
`q = 2p-1 = 1/2`, `C = 1`, the coincidence time of the source's `(coincide)`, `s = 64C = 64`:
`(fluid)` holds, the start normalisation `-1 ≤ x_i(0) ≤ 0` holds, `(fluidmax)`'s `m_i = x_i` holds,
`(Rlower)` `R(u) ≥ 3u/(8C) - 3` holds — and the walkers coincide at `s` and at no later time. -/
theorem stall_admissible_not_coincident :
    ∃ (x : Fin 2 → ℝ → ℝ) (q C s : ℝ), 0 < q ∧ q ≤ 1 ∧ 1 ≤ C ∧ 3 ≤ 8 * C * q ∧
      s = 64 * C ∧ FluidOn x q ∧ (∀ i : Fin 2, -1 ≤ x i 0 ∧ x i 0 ≤ 0) ∧
      (∀ (i : Fin 2) (u : ℝ), 0 ≤ u → mI x (fun _ => 0) i u = x i u) ∧
      (∀ u : ℝ, 0 ≤ u → 3 * u / (8 * C) - 3 ≤ R2 x (fun _ => 0) u) ∧
      x 0 s = x 1 s ∧ ¬ CoincideOn x s (s + 1) := by
  refine ⟨stall (1 / 2) 64, 1 / 2, 1, 64, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, stall_fluid (by norm_num) 64, stall_start (by norm_num) (by norm_num), ?_, ?_,
    stall_coincide_at (by norm_num), ?_⟩
  · intro i u hu
    exact stall_mI_eq (by norm_num) (by norm_num) hu
  · intro u hu
    rw [stall_R2 (by norm_num) (by norm_num) hu]
    nlinarith
  · exact stall_not_coincide (by norm_num) (by norm_num : (64:ℝ) < 64 + 1)

/-! ## 2c. The meeting rule `JoinRuleFrom` is not a consequence of the fluid facts either -/

/-- The leader class `A = {i : x_i(s) = R(s)}` of the fluid configuration. -/
def leaders (x : Fin 2 → ℝ → ℝ) (s : ℝ) : Set (Fin 2) :=
  {i | x i s = max (x 0 s) (x 1 s)}

/-- The paper's meeting rule in the shape the campaign consumes it
(`FluidMerge.JoinRuleFrom`): past `s₀`, every proper leader class grows strictly within the
candidate deadline `s + b · gap(s)`. -/
def JoinRuleFrom (x : Fin 2 → ℝ → ℝ) (s₀ b : ℝ) : Prop :=
  ∀ s : ℝ, s₀ ≤ s → leaders x s ≠ Set.univ →
    ∃ u : ℝ, s ≤ u ∧ u ≤ s + b * (max (x 0 s) (x 1 s) - min (x 0 s) (x 1 s)) ∧
      leaders x s ⊂ leaders x u

lemma stall_leaders {q s : ℝ} (hq : 0 < q) (hs : 0 ≤ s) {u : ℝ} (hu : s < u) :
    leaders (stall q s) u = {0} := by
  have h0 : stall q s 0 u = q * u := stall_zero q s u
  have h1 : stall q s 1 u = q * s := by
    rw [stall_one, min_eq_right (by nlinarith : q * s ≤ q * u)]
  have hmax : max (stall q s 0 u) (stall q s 1 u) = q * u := by
    rw [h0, h1]; exact max_eq_left (by nlinarith)
  ext i
  rcases fin2_cases i with rfl | rfl
  · simp only [leaders, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [hmax, h0]; simp
  · simp only [leaders, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [hmax, h1] at h
      have hqu : q * s = q * u := h
      nlinarith
    · intro h
      exact absurd h (by decide : ¬ ((1 : Fin 2) = 0))

/-- **The stalling model violates the paper's meeting rule for every constant `b`.**  Past the
coincidence time `s`, its leader class is the singleton `{0}` for ever. -/
theorem stall_no_join_rule {q s s₀ b : ℝ} (hq : 0 < q) (_hs : 0 ≤ s) (hs₀ : s < s₀) :
    ¬ JoinRuleFrom (stall q s) s₀ b := by
  intro hJ
  have hproper : leaders (stall q s) s₀ ≠ Set.univ := by
    rw [stall_leaders hq _hs hs₀]
    intro h
    have h1 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by rw [h]; exact Set.mem_univ 1
    exact absurd h1 (by decide)
  obtain ⟨u, hu, -, hsub⟩ := hJ s₀ le_rfl hproper
  have hsu : s < u := lt_of_lt_of_le hs₀ hu
  rw [stall_leaders hq _hs hs₀, stall_leaders hq _hs hsu] at hsub
  exact hsub.2 (fun _ h => h)

/-- **The fluid facts do not imply the meeting rule `JoinRuleFrom`, at any constant.**

The stalling model at `q = 2p−1 = 1/2` satisfies `(fluid)`, the start normalisation and
`(Rlower)` at `C = 1`, and yet its leader class never grows: there is no `b` for which the
paper's meeting rule holds.  So `FluidMerge.JoinRuleFrom` — the residual input of
`FluidMeet.coalesced_at_some_time_of_join`, of `CoalesceSharp` and of the one-coalescence-time
route to `(half)` — cannot be derived from the compactness-limit facts; it must be produced from
the occupation/movement estimate, and the countermodel is excluded exactly by `(lococc)`
(`stall_breaks_fractional_occupation`). -/
theorem fluid_facts_do_not_force_join_rule :
    ∃ (x : Fin 2 → ℝ → ℝ) (q : ℝ), 0 < q ∧ q ≤ 1 ∧ FluidOn x q ∧
      (∀ i : Fin 2, -1 ≤ x i 0 ∧ x i 0 ≤ 0) ∧
      (∀ u : ℝ, 0 ≤ u → 3 * u / (8 * 1) - 3 ≤ R2 x (fun _ => 0) u) ∧
      ∀ b : ℝ, ¬ JoinRuleFrom x 64 b := by
  refine ⟨stall (1 / 2) 32, 1 / 2, by norm_num, by norm_num,
    stall_fluid (by norm_num) 32, stall_start (by norm_num) (by norm_num), ?_, ?_⟩
  · intro u hu
    rw [stall_R2 (by norm_num) (by norm_num) hu]
    nlinarith
  · intro b
    exact stall_no_join_rule (by norm_num) (by norm_num) (by norm_num : (32:ℝ) < 64)

/-! ## 3. The refutation of the fluid-only route to `(coincide)` -/

/-- **The fluid facts preceding `(coincide)` do not imply `(coincide)`.**

No assignment of the source's fluid-limit facts used before `(coincide)` — `(fluid)` at velocity
`q = 2p-1 ∈ (0,1)`, the start normalisation `-1 ≤ x_i(0) ≤ 0` and `R(0) = 0`, and the ballistic
lower bound `(Rlower)` — can force two walkers that coincide at a fluid time `s` to remain
coincident.  Hence the coalescence step of the source's block argument necessarily uses the
occupation/movement input `(lococc)`/`(locmove)`; a derivation from the compactness limit and
`(Rlower)` alone is impossible. -/
theorem fluid_facts_do_not_force_coincide :
    ¬ (∀ (x : Fin 2 → ℝ → ℝ) (q C s T : ℝ), 0 < q → q ≤ 1 → 1 ≤ C → 3 ≤ 8 * C * q →
        FluidOn x q →
        (∀ i : Fin 2, -1 ≤ x i 0 ∧ x i 0 ≤ 0) →
        (∀ u : ℝ, 0 ≤ u → 3 * u / (8 * C) - 3 ≤ R2 x (fun _ => 0) u) →
        x 0 s = x 1 s → s < T → CoincideOn x s T) := by
  intro H
  have hq : (0:ℝ) < 1 / 2 := by norm_num
  have hq1 : (1:ℝ) / 2 ≤ 1 := by norm_num
  have hC : (1:ℝ) ≤ 4 := by norm_num
  have hCq : (3:ℝ) ≤ 8 * 4 * (1 / 2) := by norm_num
  have hfluid : FluidOn (stall (1 / 2) 256) (1 / 2) := stall_fluid (by norm_num) 256
  have hstart : ∀ i : Fin 2, -1 ≤ stall (1 / 2) 256 i 0 ∧ stall (1 / 2) 256 i 0 ≤ 0 :=
    stall_start (by norm_num) (by norm_num)
  have hlower : ∀ u : ℝ, 0 ≤ u → 3 * u / (8 * 4) - 3 ≤ R2 (stall (1 / 2) 256) (fun _ => 0) u := by
    intro u hu
    rw [stall_R2 (by norm_num) (by norm_num) hu]
    nlinarith
  have hcoin : stall (1 / 2) 256 0 256 = stall (1 / 2) 256 1 256 :=
    stall_coincide_at (by norm_num)
  have hconcl : CoincideOn (stall (1 / 2) 256) 256 257 :=
    H (stall (1 / 2) 256) (1 / 2) 4 256 257 hq hq1 hC hCq hfluid hstart hlower hcoin
      (by norm_num : (256:ℝ) < 257)
  exact stall_not_coincide (by norm_num) (by norm_num : (256:ℝ) < 257) hconcl

end WCJFFluidCore
