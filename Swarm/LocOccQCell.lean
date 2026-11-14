/-
  # The `Qpl` two-sided window estimate and the concrete record cell for `(lococc)`

  `LocOcc.lococc_window_eighth` (public, `Swarm/LocOccProjected.lean`) is the paper's
  `(lococc)` display abstracted over its fields.  Two of those groups are *not* arithmetic:

  * `hQ : -(Q t - Q s) <= KQ * L34` — the one-sided window deviation of the adapted compensator
    `Qpl`, required simultaneously for **every** pair `s <= t` of the record window;
  * the five containments `hcont1..hcont5`, the record monotone/unit-step premises and the
    position-comparison premises `hXW, hMiw, hXMiS, hXtMi`, which all have to come from the
    concrete record geometry, plus `hocc`.

  This file discharges those two groups on the actual iid uniform array.

  ## 1. `hQ` for all pairs from a single-start maximal estimate

  `ShiftedQplResidual.measureReal_qpl_oscStartCell_le_shifted_window` controls, on a measurable
  start cell `A`, the single-start deviation `∃ k <= n, δ <= |Qpl (σ+k) - Qpl σ|`.  The paper
  needs `-(Q_t - Q_s) <= 2L^{3/4}` for *all* `σ <= s <= t <= σ + TL`, obtained by subtracting the
  common value at `σ`.  We make that reduction exact:

      qplDrop Q σ n (2δ) ⊆ OscStartCell Q (fun _ => σ) n δ σ,

  from `Q_s - Q_t = (Q_s - Q_σ) - (Q_t - Q_σ)` and the triangle inequality.  The all-pairs
  estimate therefore costs exactly one single-start maximal Azuma term, with the same start-cell
  weight and threshold `δ` half the final one.  Both residual defects
  (`shiftedContDefect`, `harmDefect`) are retained, weighted by the start cell.

  ## 2. The concrete adapted record cell

  `recCell p m i j r s L` is the actual geometric cell: at time `s` the running records of both
  walkers and walker `i`'s position lie in `[r-L, r]`.  It is `enlFilt p m s`-measurable
  (`measurableSet_recCell`) — exactly the measurability the shifted maximal Azuma and
  `M3Hosc.measureReal_recordCell_hosc_scale` consume.  Unit steps then give the whole window
  geometry, hence the five containments for the paper's window
  `A₀ = r-(T+2)L`, `Lw = (2T+2)L+1`, the ledger indicator `hocc`, `hMjmono`/`hMjstep` and
  `hXW`/`hMiw`/`hXMiS`/`hXtMi`.

  Everything below is a statement about the actual `Swarming.Uniform.arrayMeasure N` array with
  `1/2 < p < 1`; no future law, stationary measure or free parameter is introduced.

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Swarm.LocOccLedger
import Swarm.ShiftedQplResidual
import Swarm.M3Hosc
import Swarm.LocOccEndpoint
import Swarm.LocOccProjected

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.Enl.VdriftAssembly

namespace LocOccQ

variable {N : ℕ}

/-! ### 1. The one-sided drop of `Qpl` and the `hQ` field -/

/-- The set on which the adapted compensator `Qpl` **drops** by more than `δ` across some pair of
times `σ <= s <= t <= σ + n`.  Its complement is precisely the `hQ` field of
`LocOcc.lococc_window` on that window: `-(Q t - Q s) <= δ`. -/
def qplDrop (Q : ℕ → Array N → ℝ) (σ n : ℕ) (δ : ℝ) : Set (Array N) :=
  {U | ∃ s t : ℕ, σ ≤ s ∧ s ≤ t ∧ t ≤ σ + n ∧ δ < Q s U - Q t U}

/-- **`hQ` off `qplDrop`.**  Outside the drop set, the one-sided window bound holds for every pair
`σ <= s <= t <= σ + n` simultaneously. -/
theorem notMem_qplDrop {Q : ℕ → Array N → ℝ} {σ n : ℕ} {δ : ℝ} {U : Array N}
    (h : U ∉ qplDrop Q σ n δ) {s t : ℕ} (h1 : σ ≤ s) (h2 : s ≤ t) (h3 : t ≤ σ + n) :
    -(Q t U - Q s U) ≤ δ := by
  have h' : ¬ (δ < Q s U - Q t U) := fun hc => h ⟨s, t, h1, h2, h3, hc⟩
  have h2' : Q s U - Q t U ≤ δ := not_lt.mp h'
  linarith

/-- **All pairs from one start.**  A drop of `2δ` at some pair `σ <= s <= t <= σ + n` forces the
single-start deviation `δ <= |Q(σ+k) - Qσ|` at some `k <= n`.  This is the paper's
`|Q_t - Q_s| <= 2 max_{k<=TL} |Q̃_k|` reduction, made exact. -/
theorem qplDrop_subset_oscStartCell (Q : ℕ → Array N → ℝ) (σ n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    qplDrop Q σ n (2 * δ) ⊆ ShiftedAdvance.OscStartCell Q (fun _ => σ) n δ σ := by
  rintro U ⟨s, t, h1, h2, h3, hdev⟩
  have h1' : σ + (s - σ) = s := Nat.add_sub_cancel' h1
  have hts : σ ≤ t := le_trans h1 h2
  have ht' : σ + (t - σ) = t := Nat.add_sub_cancel' hts
  have ht : t - σ ≤ n := by omega
  set a : ℝ := Q s U - Q σ U with ha
  set b : ℝ := Q t U - Q σ U with hb
  have hdev' : 2 * δ < a - b := by
    have he : Q s U - Q t U = a - b := by rw [ha, hb]; ring
    linarith
  have hkey : 2 * δ < |a| + |b| := by
    have h3' : a ≤ |a| := le_abs_self a
    have h4' : -b ≤ |b| := neg_le_abs b
    linarith
  refine ⟨rfl, ?_⟩
  rcases le_or_gt δ |a| with hale | hagt
  · exact ⟨s - σ, by omega, by rw [h1']; exact hale⟩
  · have hb' : δ < |b| := by
      have := abs_nonneg a
      linarith
    exact ⟨t - σ, ht, by rw [ht']; exact le_of_lt hb'⟩

/-- **The `hQ` field, with the honest single-start maximal Azuma price.**

On any `enlFilt p m σ`-measurable start cell `A`, the measure of the pairs on which the adapted
`Qpl` drops by more than `KQ * L34` inside `[σ, σ+n]` is at most

  `μ A * 2(n+1) exp(-(KQ L34/2)² / (4 n C²))`

plus the two start-cell-weighted shifted residuals (`shiftedContDefect`, `harmDefect`) that the
accepted `ShiftedQplResidual` development isolates.  No residual is dropped, no future
independence is used and no unweighted substitution occurs: every term keeps the cell weight
`μ.real A`. -/
theorem measureReal_qplDrop_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (eps : ℝ) (i j : Fin N) (hε : 0 < eps) {σ n : ℕ} (hn : 1 ≤ n)
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m σ] A)
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {KQ L34 : ℝ} (hKQ : 0 < KQ) (hL34 : 0 < L34) :
    (arrayMeasure N).real
        (A ∩ qplDrop (ProjLedger.Qpl p m eps i j) σ n (KQ * L34)) ≤
      (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
            (4 * (n : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        ((arrayMeasure N).real
            (A ∩ ShiftedQplResidual.shiftedContDefect p m i j σ w M n) +
          (arrayMeasure N).real (A ∩ QplWindow.harmDefect p m j V w M)) := by
  have hδ : (0 : ℝ) < KQ * L34 / 2 := by positivity
  have hδeq : KQ * L34 = 2 * (KQ * L34 / 2) := by ring
  have hsub : A ∩ qplDrop (ProjLedger.Qpl p m eps i j) σ n (KQ * L34) ⊆
      A ∩ ShiftedAdvance.OscStartCell (ProjLedger.Qpl p m eps i j)
        (fun _ : Array N => σ) n (KQ * L34 / 2) σ :=
    Set.inter_subset_inter le_rfl (by
      have h := qplDrop_subset_oscStartCell (Q := ProjLedger.Qpl p m eps i j) σ n hδ
      rw [← hδeq] at h
      exact h)
  have hconst : MeasurableSet[enlFilt p m σ]
      {U : Array N | (fun _ : Array N => σ) U = σ} := by simp
  have hmain := ShiftedQplResidual.measureReal_qpl_oscStartCell_le_shifted_window
    (N := N) hp0 hp1 m eps i j hε (τ := fun _ : Array N => σ) (A := A)
    hA hconst hV1 (w := w) (M := M) hw (n := n) hn hδ
  simp only [Set.ofPred_true, Set.inter_univ] at hmain
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _)) hmain

/-- **Window form of the `hQ` conclusion.**  On the complement of `qplDrop` the `hQ` premise of
`LocOcc.lococc_window_eighth` holds for every pair of the window at once. -/
theorem hQ_of_notMem_qplDrop {Q : ℕ → Array N → ℝ} {σ n : ℕ} {δ : ℝ} {U : Array N}
    (h : U ∉ qplDrop Q σ n δ) :
    ∀ s t : ℕ, σ ≤ s → s ≤ t → t ≤ σ + n → -(Q t U - Q s U) ≤ δ :=
  fun s t h1 h2 h3 => notMem_qplDrop h h1 h2 h3

/-! ### 2. The concrete adapted record cell -/

/-- The actual record cell: at time `s` the running records of both walkers and walker `i`'s
position lie in `[r-L, r]`.  This is the paper's `{d_r <= L}` localisation in the form consumed by
the shifted maximal Azuma and by `M3Hosc.measureReal_recordCell_hosc_scale`. -/
def recCell (p : ℝ) (m : ℕ) (i j : Fin N) (r s L : ℕ) : Set (Array N) :=
  {U | (r : ℤ) - (L : ℤ) ≤ runMax p m U j s ∧ runMax p m U j s ≤ (r : ℤ) ∧
      (r : ℤ) - (L : ℤ) ≤ runMax p m U i s ∧ runMax p m U i s ≤ (r : ℤ) ∧
      (r : ℤ) - (L : ℤ) ≤ (trajectory p m U s).pos i ∧
      (trajectory p m U s).pos i ≤ (r : ℤ)}

/-- **The record cell is `enlFilt p m s`-measurable.**  This is the measurability gate the
start-cell-conditioned estimates need; it holds for the actual process with no extra hypothesis. -/
theorem measurableSet_recCell (p : ℝ) (m : ℕ) (i j : Fin N) (r s L : ℕ) :
    MeasurableSet[enlFilt p m s] (recCell p m i j r s L) := by
  have hMj : Measurable[enlFilt p m s] (fun U : Array N => runMax p m U j s) :=
    measurable_runMax_enl (N := N) p m s j
  have hMi : Measurable[enlFilt p m s] (fun U : Array N => runMax p m U i s) :=
    measurable_runMax_enl (N := N) p m s i
  have hX : Measurable[enlFilt p m s] (fun U : Array N => (trajectory p m U s).pos i) :=
    enl_pos_measurable p m s (k := s) le_rfl i
  have h1 : MeasurableSet[enlFilt p m s]
      {U : Array N | (r : ℤ) - (L : ℤ) ≤ runMax p m U j s} := hMj measurableSet_Ici
  have h2 : MeasurableSet[enlFilt p m s]
      {U : Array N | runMax p m U j s ≤ (r : ℤ)} := hMj measurableSet_Iic
  have h3 : MeasurableSet[enlFilt p m s]
      {U : Array N | (r : ℤ) - (L : ℤ) ≤ runMax p m U i s} := hMi measurableSet_Ici
  have h4 : MeasurableSet[enlFilt p m s]
      {U : Array N | runMax p m U i s ≤ (r : ℤ)} := hMi measurableSet_Iic
  have h5 : MeasurableSet[enlFilt p m s]
      {U : Array N | (r : ℤ) - (L : ℤ) ≤ (trajectory p m U s).pos i} := hX measurableSet_Ici
  have h6 : MeasurableSet[enlFilt p m s]
      {U : Array N | (trajectory p m U s).pos i ≤ (r : ℤ)} := hX measurableSet_Iic
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6))))

/-- Membership unpacking for the record cell. -/
theorem recCell_spec {p : ℝ} {m : ℕ} {i j : Fin N} {r s L : ℕ} {U : Array N}
    (h : U ∈ recCell p m i j r s L) :
    (r : ℤ) - (L : ℤ) ≤ runMax p m U j s ∧ runMax p m U j s ≤ (r : ℤ) ∧
      (r : ℤ) - (L : ℤ) ≤ runMax p m U i s ∧ runMax p m U i s ≤ (r : ℤ) ∧
      (r : ℤ) - (L : ℤ) ≤ (trajectory p m U s).pos i ∧
      (trajectory p m U s).pos i ≤ (r : ℤ) := h

/-! ### 3. Unit-step geometry on the record cell -/

/-- A running record with `M_s in [r-L, r]` stays in `[r-(T+1)L, r+TL]` throughout the window. -/
theorem recMax_bounds {p : ℝ} {m : ℕ} {k : Fin N} {r s L T : ℕ} {U : Array N}
    (h1 : (r : ℤ) - (L : ℤ) ≤ runMax p m U k s) (h2 : runMax p m U k s ≤ (r : ℤ))
    {u : ℕ} (hsu : s ≤ u) (huT : u ≤ s + T * L) :
    (r : ℤ) - ((T + 1) * L : ℕ) ≤ runMax p m U k u ∧
      runMax p m U k u ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
  have hmono : runMax p m U k s ≤ runMax p m U k u := by
    rw [runMax_eq_recVal, runMax_eq_recVal]
    exact QplWindow.recVal_mono_le (p := p) (m := m) (j := k) (U := U) hsu
  have hstep : runMax p m U k u ≤ runMax p m U k s + ((u - s : ℕ) : ℤ) := by
    rw [runMax_eq_recVal, runMax_eq_recVal]
    have := QplWindow.recVal_le_add_run (p := p) (m := m) (j := k) (U := U) s u hsu
    simpa using this
  have hcast : (((u - s : ℕ)) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    exact_mod_cast (by omega : u - s ≤ T * L)
  have hTL : (((T + 1) * L : ℕ) : ℤ) = (L : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h : ((T + 1) * L : ℕ) = L + T * L := by ring
    rw [h]; push_cast; ring
  constructor
  · rw [hTL]; linarith
  · linarith

/-- Walker `i`'s position stays in `[r-(T+1)L, r+TL]` throughout the window. -/
theorem recCell_pos_bounds {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ} {U : Array N}
    (hU : U ∈ recCell p m i j r s L) {u : ℕ} (hsu : s ≤ u) (huT : u ≤ s + T * L) :
    (r : ℤ) - ((T + 1) * L : ℕ) ≤ (trajectory p m U u).pos i ∧
      (trajectory p m U u).pos i ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
  obtain ⟨-, -, -, -, hp1, hp2⟩ := recCell_spec hU
  have hsub := QplWindow.pos_sub_run_le p m U i s (u - s)
  have hadd := QplWindow.pos_le_add_run p m U i s (u - s)
  rw [Nat.add_sub_cancel' hsu] at hsub hadd
  have hcast : (((u - s : ℕ)) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    exact_mod_cast (by omega : u - s ≤ T * L)
  have hTL : (((T + 1) * L : ℕ) : ℤ) = (L : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h : ((T + 1) * L : ℕ) = L + T * L := by ring
    rw [h]; push_cast; ring
  constructor
  · rw [hTL]; linarith
  · linarith

/-- In-window nonnegativity of walker `i`'s position: the paper's `X_u^i >= 2L > 0` on
`{d_r <= L}`, here from the record cell and `r >= (T+3)L`. -/
theorem recCell_pos_nonneg {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ}
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L)
    {u : ℕ} (hsu : s ≤ u) (huT : u ≤ s + T * L) :
    0 ≤ (trajectory p m U u).pos i := by
  have hb := (recCell_pos_bounds (T := T) hU hsu huT).1
  have h1 : ((T + 1) * L : ℕ) ≤ r := by
    have h2 : (T + 1) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    exact le_trans h2 hr
  have h2 : (((T + 1) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast h1
  linarith

/-- The window arithmetic: `A₀ + Lw = r + TL + 1` for the paper's `A₀ = r-(T+2)L`,
`Lw = (2T+2)L+1`. -/
theorem window_add {r T L : ℕ} (hr : (T + 3) * L ≤ r) :
    r - (T + 2) * L + ((2 * T + 2) * L + 1) = r + T * L + 1 := by
  have hsub : (T + 2) * L ≤ r := by
    have : (T + 2) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    exact le_trans this hr
  have hsplit : (2 * T + 2) * L = (T + 2) * L + T * L := by ring
  have hkey : r - (T + 2) * L + ((T + 2) * L + T * L) = r + T * L := by
    rw [← Nat.add_assoc, Nat.sub_add_cancel hsub]
  calc r - (T + 2) * L + ((2 * T + 2) * L + 1)
      = r - (T + 2) * L + ((T + 2) * L + T * L) + 1 := by rw [hsplit]; ring
    _ = r + T * L + 1 := by rw [hkey]

/-- `L <= (T+1)L` and `L <= (T+2)L` in the cast form used below. -/
theorem L_le_mul_T {L T : ℕ} (hT : 1 ≤ T) :
    ((L : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ)) ∧ ((L : ℤ) ≤ (((T + 1) * L : ℕ) : ℤ)) := by
  have h1 : L ≤ (T + 2) * L := by
    calc L = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (T + 2) := Nat.mul_le_mul_left L (by omega)
      _ = (T + 2) * L := Nat.mul_comm _ _
  have h2 : L ≤ (T + 1) * L := by
    calc L = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (T + 1) := Nat.mul_le_mul_left L (by omega)
      _ = (T + 1) * L := Nat.mul_comm _ _
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ### 4. The five containments -/

/-- `hcont2`: walker `j`'s record at the left endpoint is at least `A₀`. -/
theorem recCell_hcont2 {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L) :
    r - (T + 2) * L ≤ (runMax p m U j s).toNat := by
  obtain ⟨hr1, -, -, -, -, -⟩ := recCell_spec hU
  have h0 : 0 ≤ runMax p m U j s := zero_le_runMax p m U j s
  have hsub : (T + 2) * L ≤ r := by
    have : (T + 2) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    exact le_trans this hr
  rw [Int.le_toNat h0, Nat.cast_sub hsub]
  linarith [(L_le_mul_T (L := L) hT).1]

/-- `hcont1`: walker `i`'s position at the left endpoint is at least `A₀`. -/
theorem recCell_hcont1 {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L) :
    r - (T + 2) * L ≤ ((trajectory p m U s).pos i).toNat := by
  obtain ⟨-, -, -, -, hp1, -⟩ := recCell_spec hU
  have h0 : 0 ≤ (trajectory p m U s).pos i := by
    have hp := (recCell_pos_bounds (T := T) (u := s) hU (le_rfl : s ≤ s)
      (by omega : s ≤ s + T * L)).1
    have h2 : (((T + 1) * L : ℕ) : ℤ) ≤ (r : ℤ) := by
      have h3 : (T + 1) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
      exact_mod_cast le_trans h3 hr
    linarith
  have hsub : (T + 2) * L ≤ r := by
    have : (T + 2) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    exact le_trans this hr
  rw [Int.le_toNat h0, Nat.cast_sub hsub]
  linarith [(L_le_mul_T (L := L) hT).1]

/-- `hcont3`: walker `i`'s position at the right endpoint is at most `A₀ + Lw`. -/
theorem recCell_hcont3 {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L) :
    ((trajectory p m U (s + T * L)).pos i).toNat
      ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) := by
  have hb := (recCell_pos_bounds (T := T) (u := s + T * L) hU
    (Nat.le_add_right s (T * L)) le_rfl).2
  rw [window_add hr, Int.toNat_le]
  have : (((r + T * L + 1 : ℕ)) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [this]; linarith

/-- `hcont4`: walker `i`'s record at the right endpoint satisfies `Mi t + 1 <= A₀ + Lw`. -/
theorem recCell_hcont4 {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L) :
    (runMax p m U i (s + T * L)).toNat + 1
      ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) := by
  obtain ⟨-, -, hi1, hi2, -, -⟩ := recCell_spec hU
  have hrec : runMax p m U i (s + T * L) ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) :=
    (recMax_bounds (k := i) hi1 hi2 (Nat.le_add_right s (T * L)) le_rfl).2
  have hnn : 0 ≤ runMax p m U i (s + T * L) := zero_le_runMax p m U i (s + T * L)
  have hcast : ((runMax p m U i (s + T * L)).toNat : ℤ) = runMax p m U i (s + T * L) :=
    Int.toNat_of_nonneg hnn
  have hz : (((runMax p m U i (s + T * L)).toNat + 1 : ℕ) : ℤ)
      ≤ ((r + T * L + 1 : ℕ) : ℤ) := by
    have hrec' : runMax p m U i (s + T * L) ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := hrec
    push_cast at hrec' ⊢
    rw [hcast]; linarith
  have hfin : (runMax p m U i (s + T * L)).toNat + 1 ≤ r + T * L + 1 := by exact_mod_cast hz
  rwa [window_add hr]

/-- `hcont5`: walker `j`'s record at the right endpoint is at most `A₀ + Lw`. -/
theorem recCell_hcont5 {p : ℝ} {m : ℕ} {i j : Fin N} {r s L T : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L) :
    (runMax p m U j (s + T * L)).toNat ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) := by
  obtain ⟨hj1, hj2, -, -, -, -⟩ := recCell_spec hU
  have hb := (recMax_bounds (k := j) hj1 hj2 (Nat.le_add_right s (T * L)) le_rfl).2
  rw [window_add hr, Int.toNat_le]
  have : (((r + T * L + 1 : ℕ)) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [this]; linarith

/-! ### 5. Record monotonicity, the unit step and the position/record comparisons -/

/-- The running record is nondecreasing in time, at `toNat` level. -/
theorem runMax_toNat_mono (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) {a b : ℕ} (h : a ≤ b) :
    (runMax p m U j a).toNat ≤ (runMax p m U j b).toNat := by
  rw [runMax_eq_recVal, runMax_eq_recVal]
  exact Int.toNat_le_toNat (QplWindow.recVal_mono_le (p := p) (m := m) (j := j) (U := U) h)

/-- The `hMjmono` field. -/
theorem recCell_Mj_mono (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) (n : ℕ) :
    (runMax p m U j n).toNat ≤ (runMax p m U j (n + 1)).toNat :=
  runMax_toNat_mono p m j U (Nat.le_succ n)

/-- The `hMjstep` field: the record advances by at most one per step. -/
theorem recCell_Mj_step (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) (n : ℕ) :
    (runMax p m U j (n + 1)).toNat ≤ (runMax p m U j n).toNat + 1 := by
  have hstep : runMax p m U j (n + 1) ≤ runMax p m U j n + 1 := by
    rw [runMax_eq_recVal, runMax_eq_recVal]
    have h := QplWindow.recVal_le_add_run (p := p) (m := m) (j := j) (U := U) n (n + 1)
      (Nat.le_succ n)
    have hsub : (((n + 1) - n : ℕ) : ℤ) = 1 := by norm_num
    rw [hsub] at h
    exact h
  have h0 : 0 ≤ runMax p m U j n := zero_le_runMax p m U j n
  have hcast : ((runMax p m U j n).toNat : ℤ) = runMax p m U j n := Int.toNat_of_nonneg h0
  have hL : (((runMax p m U j n).toNat + 1 : ℕ) : ℤ) = runMax p m U j n + 1 := by
    push_cast
    rw [hcast]
  refine Int.toNat_le.mpr ?_
  calc runMax p m U j (n + 1) ≤ runMax p m U j n + 1 := hstep
    _ = (((runMax p m U j n).toNat + 1 : ℕ) : ℤ) := by rw [← hL]

/-- A position never exceeds the running record at a later time. -/
theorem pos_toNat_le_runMax {p : ℝ} {m : ℕ} {i : Fin N} {U : Array N} {n K : ℕ} (h : n ≤ K) :
    ((trajectory p m U n).pos i).toNat ≤ (runMax p m U i K).toNat :=
  Int.toNat_le_toNat (Finset.le_sup' (fun t => (trajectory p m U t).pos i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))

/-- **The five containments and the ledger side conditions, from the concrete record cell.**
All ten components are the exact premises `hcont1..hcont5`, `hMiw`, `hXMiS`, `hXtMi`, `hXW` and
in-window nonnegativity of `LocOcc.lococc_window_eighth`/`hocc`, at the paper's window
`A₀ = r-(T+2)L`, `Lw = (2T+2)L+1`. -/
theorem recCell_window_fields {p : ℝ} {m : ℕ} {i j : Fin N} {r s t T L : ℕ}
    (hT : 1 ≤ T) (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L)
    (hst : s ≤ t) (htT : t ≤ s + T * L) :
    (r - (T + 2) * L ≤ ((trajectory p m U s).pos i).toNat ∧
      r - (T + 2) * L ≤ (runMax p m U j s).toNat ∧
      ((trajectory p m U t).pos i).toNat
        ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) ∧
      (runMax p m U i t).toNat + 1 ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) ∧
      (runMax p m U j t).toNat ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) ∧
      (runMax p m U i s).toNat ≤ (runMax p m U i t).toNat ∧
      ((trajectory p m U s).pos i).toNat ≤ (runMax p m U i s).toNat ∧
      ((trajectory p m U t).pos i).toNat ≤ (runMax p m U i t).toNat ∧
      (∀ u : ℕ, s ≤ u → u < t → ((trajectory p m U (u + 1)).pos i).toNat
        ≤ (runMax p m U i t).toNat) ∧
      (∀ u : ℕ, s ≤ u → u ≤ s + T * L → 0 ≤ (trajectory p m U u).pos i)) := by
  obtain ⟨hj1, hj2, hi1, hi2, -, -⟩ := recCell_spec hU
  have hb := recCell_pos_bounds (T := T) hU hst htT
  have hc : (((r + T * L + 1 : ℕ)) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by push_cast; ring
  have h3 : ((trajectory p m U t).pos i).toNat
      ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) := by
    rw [window_add hr, Int.toNat_le, hc]; linarith [hb.2]
  have hnn : 0 ≤ runMax p m U i t := zero_le_runMax p m U i t
  have hcast : ((runMax p m U i t).toNat : ℤ) = runMax p m U i t := Int.toNat_of_nonneg hnn
  have hrec : runMax p m U i t ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) :=
    (recMax_bounds (k := i) hi1 hi2 hst htT).2
  have h4 : (runMax p m U i t).toNat + 1 ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) := by
    rw [window_add hr]
    have hrec' : runMax p m U i t ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := hrec
    have hz : (((runMax p m U i t).toNat + 1 : ℕ) : ℤ) ≤ ((r + T * L + 1 : ℕ) : ℤ) := by
      push_cast at hrec' ⊢
      rw [hcast]; linarith
    exact_mod_cast hz
  have h5 : (runMax p m U j t).toNat ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) := by
    have hb5 := (recMax_bounds (k := j) hj1 hj2 hst htT).2
    rw [window_add hr, Int.toNat_le, hc]; linarith
  exact ⟨recCell_hcont1 hT hr hU, recCell_hcont2 hT hr hU, h3, h4, h5,
    runMax_toNat_mono p m i U hst, pos_toNat_le_runMax (le_refl s),
    pos_toNat_le_runMax (le_refl t),
    fun u _ hu => pos_toNat_le_runMax (by omega),
    fun u hsu huT => recCell_pos_nonneg (T := T) hr hU hsu huT⟩

/-- **`hocc` on the record cell**: the paper's ledger indicator `1{0 <= X_u^i <= M_u^j}` is the
position comparison `1{X_u^i <= M_u^j}` of `(lococc)` at every time of the window. -/
theorem recCell_occInd {p : ℝ} {m : ℕ} {i j : Fin N} {r s T L : ℕ}
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ recCell p m i j r s L)
    {u : ℕ} (hsu : s ≤ u) (huT : u ≤ s + T * L) :
    SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
        (fun q => runMax p m U j q) u
      = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 :=
  LocOccEnd.occInd_eq_toNat_toNat m U (recCell_pos_nonneg (T := T) hr hU hsu huT)

end LocOccQ

namespace LocOccQ

variable {N : ℕ}

/-! ### 6. The record cost satisfies `hJstruct` globally, with no window restriction

`LocOcc.ae_step_ledger_actual` is a statement for **every** `u`, so the `J` fed into
`LocOcc.lococc_window_eighth` must be the global `Jcorr`.  `LocOccEnd.abs_Jcorr_le` assumes
`0 <= X_{n+1}^i`, which is false for early times.  The point of this section is that the
assumption is *free*: when the record-cost indicator is on, `M_n^j < X_{n+1}^i` forces
`X_{n+1}^i > 0`; when it is off, the record cost vanishes identically.  Hence the structural
`(Jbound)` holds globally on the actual array with no nonnegativity hypothesis.
-/

/-- **`Jcorr` vanishes off the `(Jbound)` support.**  This is the case analysis of the paper's
`|J_{t+1}| <= C h_j(r_t-1)^2 1{r_{t+1}=r_t+1, X_{t+1}^i > r_t}` with no positivity assumption on
`X_{n+1}^i`. -/
theorem Jcorr_eq_zero_of_not_indicator {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {ε : ℝ} (U : Array N) (n : ℕ)
    (hI : ¬ ((runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
      ((runMax p m U j n).toNat : ℤ) < (((trajectory p m U (n + 1)).pos i).toNat : ℤ))) :
    VdriftAssembly.Jcorr p m ε i j U n = 0 := by
  have hJ : VdriftAssembly.Jcorr p m ε i j U n
      = SwarmOcc.Fcorr (aRec p m) ε (bRec p m (n + 1) j U)
          ((trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1))
        - SwarmOcc.Fcorr (aRec p m) ε (bRec p m n j U)
          ((trajectory p m U (n + 1)).pos i - runMax p m U j n) := rfl
  have hmono := recCell_Mj_mono p m j U n
  have hstep := recCell_Mj_step p m j U n
  by_cases hA : (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1
  · -- record advanced but `X_{n+1} <= M_n`
    have hB : ¬ (((runMax p m U j n).toNat : ℤ)
        < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)) := fun hc => hI ⟨hA, hc⟩
    have hB2 : ((trajectory p m U (n + 1)).pos i).toNat ≤ (runMax p m U j n).toNat := by
      have h := not_lt.mp hB
      omega
    have hMn0 : 0 ≤ (runMax p m U j n).toNat := Nat.zero_le _
    have hXle : (trajectory p m U (n + 1)).pos i
        ≤ ((runMax p m U j n).toNat : ℤ) := by
      rcases le_or_gt 0 ((trajectory p m U (n + 1)).pos i) with hX | hX
      · have hXc : (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            = (trajectory p m U (n + 1)).pos i := Int.toNat_of_nonneg hX
        have h2 : (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            ≤ ((runMax p m U j n).toNat : ℤ) := by exact_mod_cast hB2
        linarith
      · have h1 : (0 : ℤ) ≤ ((runMax p m U j n).toNat : ℤ) := by exact_mod_cast hMn0
        linarith
    have hgap1 : (trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1) ≤ 0 := by
      have hrec1 : runMax p m U j (n + 1)
          = ((runMax p m U j (n + 1)).toNat : ℤ) :=
        (Int.toNat_of_nonneg (zero_le_runMax p m U j (n + 1))).symm
      rw [hrec1, hA]
      push_cast
      linarith
    have hgap0 : (trajectory p m U (n + 1)).pos i - runMax p m U j n ≤ 0 := by
      have hrec0 : runMax p m U j n = ((runMax p m U j n).toNat : ℤ) :=
        (Int.toNat_of_nonneg (zero_le_runMax p m U j n)).symm
      rw [hrec0]
      linarith
    rw [hJ, LocOccEnd.Fcorr_eq_zero_of_nonpos _ _ _ hgap1,
      LocOccEnd.Fcorr_eq_zero_of_nonpos _ _ _ hgap0]
    ring
  · -- record did not advance: the cost telescopes to zero
    have hA' : (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat := by omega
    have hr : runMax p m U j (n + 1) = runMax p m U j n := by
      have e1 : runMax p m U j (n + 1) = ((runMax p m U j (n + 1)).toNat : ℤ) :=
        (Int.toNat_of_nonneg (zero_le_runMax p m U j (n + 1))).symm
      have e0 : runMax p m U j n = ((runMax p m U j n).toNat : ℤ) :=
        (Int.toNat_of_nonneg (zero_le_runMax p m U j n)).symm
      rw [e1, e0, hA']
    have hb : bRec p m (n + 1) j U = bRec p m n j U := by
      have hrec : recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) := by
        rw [← runMax_eq_recVal, ← runMax_eq_recVal]; exact hr
      have hH : HprevAt p m (n + 1) j U = HprevAt p m n j U := by
        unfold HprevAt; rw [hrec]
      show HprevAt p m (n + 1) j U + 2 = HprevAt p m n j U + 2
      rw [hH]
    rw [hJ, hr, hb]
    ring

/-- **`hJstruct`, globally.**  The record-cost bound of `(lococc)` holds at every `n` on the
actual array, with `CJ = 2(p/(1-p)+4)^2 / (ε(1-a)^2)` and weight `wt = h_j^2`. -/
theorem Jcorr_struct {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {ε : ℝ} (hε : 0 < ε) (U : Array N) :
    ∀ n : ℕ,
      |VdriftAssembly.Jcorr p m ε i j U n|
        ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) *
          ((SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
              ((runMax p m U j n).toNat)) ^ 2
            + (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                ((runMax p m U j n).toNat + 1)) ^ 2) *
          (if (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
              ((runMax p m U j n).toNat : ℤ) <
                (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            then 1 else 0) := by
  intro n
  by_cases hI : (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
      ((runMax p m U j n).toNat : ℤ) < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
  · have hpos : 0 ≤ (trajectory p m U (n + 1)).pos i := by
      have h1 : (0 : ℤ) ≤ ((runMax p m U j n).toNat : ℤ) := by
        exact_mod_cast Nat.zero_le ((runMax p m U j n).toNat)
      have h2 : (((trajectory p m U (n + 1)).pos i).toNat : ℤ) ≤
          (trajectory p m U (n + 1)).pos i := by
        rcases le_or_gt 0 ((trajectory p m U (n + 1)).pos i) with hX | hX
        · rw [Int.toNat_of_nonneg hX]
        · have hz : ((trajectory p m U (n + 1)).pos i).toNat = 0 := by
            rw [Int.toNat_eq_zero]; omega
          omega
      linarith [hI.2]
    simpa only [if_pos hI] using
      LocOccEnd.abs_Jcorr_le hp0 hp1 hε U n hpos
        (recCell_Mj_mono p m j U n) (recCell_Mj_step p m j U n)
  · rw [if_neg hI, mul_zero,
      abs_eq_zero.mpr (Jcorr_eq_zero_of_not_indicator hp0 hp1 U n hI)]

end LocOccQ
namespace LocOccQ

variable {N : ℕ}

/-! ### 7. `(lococc)` on the record cell with the twelve model-side fields discharged -/

/-- **The literal `(lococc)` display on the actual adapted record cell.**

For `1/2 < p < 1`, `i ≠ j`, `T >= 1`, `r >= (T+3)L` and any `U` in the record cell
`recCell p m i j r s L`, the paper's display holds on `[s,t]` for every `s <= t <= s+TL`:

    `sum_{u=s}^{t-1} 1{X_u^i <= M_u^j} <= C(...) + (t-s)/8 + C_T L^{3/4}`,

with `C = (K+Kp) + 2 CJ K + 1`, `C_T = K + CH + 2 KF + 4 CJ K + 2 KQ + 1` and the actual record
cost coefficient `CJ = 2(p/(1-p)+4)^2/(ε(1-a)^2)`.

Discharged here from the actual model: `hocc`, `hZs`, `hZt`, `hh`, `hhw`, `hJstruct` (globally, see
`Jcorr_struct`), `hMjmono`, `hMjstep`, `hXW`, `hMiw`, `hXMiS`, `hXtMi`, `hcont1..hcont5` and `hQ`
(from `hQ_of_notMem_qplDrop`).

Remaining explicit hypotheses — each one exactly a proved public theorem away, none weakened:
`hled` (`LocOcc.ae_step_ledger_actual`, a.e. in `U`), `hslopeLo`/`hslopeHi` (the projected
potential slope, a.e. from `ProjLedger.projH_succ_sub` below the record), `hint`
(`LocSumR1.array_locsum_h_start` at scale `Lw`), `hosc` (`M3Hosc.measureReal_recordCell_hosc_scale`)
and `hFs`/`hFt` (`LocOccEnd.abs_Fcorr_endpoint_le` under the site cap). -/
theorem lococc_recCell_eighth {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {ε : ℝ} (hε : 0 < ε) {r s t T L : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    {U : Array N} (hU : U ∈ recCell p m i j r s L)
    {K β Kp CH KQ KF L34 : ℝ}
    (hled : ∀ u : ℕ,
      SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u - 1 / 8
        ≤ (Zproj p m ε i j U (u + 1) - Zproj p m ε i j U u)
          + VdriftAssembly.Jcorr p m ε i j U u
          - (ProjLedger.Qpl p m ε i j (u + 1) U - ProjLedger.Qpl p m ε i j u U))
    (hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ)
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)
    (hslopeHi : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ∧
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ≤ Kp)
    (hint : ∀ a b : ℕ, r - (T + 2) * L ≤ a →
      b ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) → a ≤ b →
      ∑ x ∈ Finset.Ico a b,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2
        ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hosc : projH p m j t U (((trajectory p m U s).pos i).toNat : ℤ)
        - projH p m j s U (((trajectory p m U s).pos i).toNat : ℤ) ≤ CH * L34)
    (hQd : U ∉ qplDrop (ProjLedger.Qpl p m ε i j) s (T * L) (KQ * L34))
    (hFs : |SwarmOcc.Fcorr (aRec p m) ε (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s)| ≤ KF * L34)
    (hFt : |SwarmOcc.Fcorr (aRec p m) ε (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)| ≤ KF * L34)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp) (hCH : 0 ≤ CH) (hKF : 0 ≤ KF)
    (hKQ : 0 ≤ KQ) (hL34 : 0 ≤ L34) (h1L34 : 1 ≤ L34) (hβL : β ≤ L34) :
    ∑ u ∈ Finset.Ico s t,
        SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u
      ≤ ((K + Kp) + 2 * (2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) * K + 1) *
          (((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ)
            + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
            + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
        + ((t : ℝ) - (s : ℝ)) / 8
        + (K + CH + 2 * KF
            + 4 * (2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) * K
            + 2 * KQ + 1) * L34 := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hMiw, hXMiS, hXtMi, hXW, _⟩ :=
    recCell_window_fields (T := T) hT hr hU hst htT
  have hposS : 0 ≤ (trajectory p m U s).pos i :=
    recCell_pos_nonneg (T := T) hr hU (le_rfl : s ≤ s) (by omega)
  have hcastS : ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ) = (trajectory p m U s).pos i :=
    Int.toNat_of_nonneg hposS
  have hposT : 0 ≤ (trajectory p m U t).pos i := recCell_pos_nonneg (T := T) hr hU hst htT
  have hcastT : ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ) = (trajectory p m U t).pos i :=
    Int.toNat_of_nonneg hposT
  have hocc : ∀ u : ℕ, s ≤ u → u < t →
      SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u
        = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 :=
    fun u hsu _ => recCell_occInd hr hU hsu (by omega)
  have hZs' : Zproj p m ε i j U s
      = projH p m j s U (((trajectory p m U s).pos i).toNat : ℤ)
        - SwarmOcc.Fcorr (aRec p m) ε (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s) := by
    unfold Zproj
    rw [hcastS]
  have hZt' : Zproj p m ε i j U t
      = projH p m j t U (((trajectory p m U t).pos i).toNat : ℤ)
        - SwarmOcc.Fcorr (aRec p m) ε (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t) := by
    unfold Zproj
    rw [hcastT]
  have hQst : -(ProjLedger.Qpl p m ε i j t U - ProjLedger.Qpl p m ε i j s U) ≤ KQ * L34 :=
    hQ_of_notMem_qplDrop hQd s t (le_refl s) hst htT
  have hCJ0 : (0 : ℝ) ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) := by
    have ha : aRec p m < 1 := aRec_lt_one hp0 hp1 m
    have hden : (0 : ℝ) < ε * (1 - aRec p m) ^ 2 := by
      have : (0 : ℝ) < 1 - aRec p m := by linarith
      positivity
    have : (0 : ℝ) ≤ (p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2) := by positivity
    linarith
  exact LocOcc.lococc_window_eighth
    (X := fun n => ((trajectory p m U n).pos i).toNat)
    (Mi := fun n => (runMax p m U i n).toNat)
    (Mj := fun n => (runMax p m U j n).toNat)
    (occ := fun u => SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
      (fun q => runMax p m U j q) u)
    (J := fun n => VdriftAssembly.Jcorr p m ε i j U n)
    (Z := fun n => Zproj p m ε i j U n)
    (Q := fun n => ProjLedger.Qpl p m ε i j n U)
    (H := fun n z => projH p m j n U z)
    (Fs := SwarmOcc.Fcorr (aRec p m) ε (bRec p m s j U)
      ((trajectory p m U s).pos i - runMax p m U j s))
    (Ft := SwarmOcc.Fcorr (aRec p m) ε (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t))
    (h := fun x => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)
    (wt := fun x => (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2)
    (A := r - (T + 2) * L) (Lw := (2 * T + 2) * L + 1)
    (K := K) (β := β) (Kp := Kp) (CH := CH) (KQ := KQ) (KF := KF)
    (CJ := 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) (L34 := L34)
    hst hocc hled hZs' hZt'
    (fun x => LocOccEnd.hof_nonneg hp0 hp1 _ x)
    (fun x => le_refl _)
    hslopeLo hslopeHi hint hosc hQst hFs hFt
    (Jcorr_struct hp0 hp1 hε U)
    (fun n => recCell_Mj_mono p m j U n)
    (fun n => recCell_Mj_step p m j U n)
    hXW hMiw hXMiS hXtMi hc1 hc2 hc3 hc4 hc5
    hK hβ hKp hCJ0 hCH hKF hKQ hL34 h1L34 hβL

end LocOccQ

namespace LocOccQ

variable {N : ℕ}

/-- **The measure form of the `hQ` field at a fixed pair `s <= t`.**

This is the exact quantity `LocOcc.lococc_window_eighth` needs at `(s,t)`, bounded on the actual
array by one single-start maximal Azuma term and the two start-cell-weighted shifted residuals.
Since `{-(Q_t - Q_s) > KQ L34} ⊆ qplDrop Q σ n (KQ L34)` for `σ <= s <= t <= σ+n`, the estimate
with the simultaneous (all-pairs) quantifier is at least as strong as the pointwise one used by
the display, so no union over pairs is charged twice. -/
theorem measureReal_not_hQ_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (eps : ℝ) (i j : Fin N) (hε : 0 < eps) {σ s t n : ℕ} (hn : 1 ≤ n)
    (hσs : σ ≤ s) (hst : s ≤ t) (htn : t ≤ σ + n)
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m σ] A)
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {KQ L34 : ℝ} (hKQ : 0 < KQ) (hL34 : 0 < L34) :
    (arrayMeasure N).real
        (A ∩ {U : Array N | ¬ (-(ProjLedger.Qpl p m eps i j t U
          - ProjLedger.Qpl p m eps i j s U) ≤ KQ * L34)}) ≤
      (arrayMeasure N).real A *
          (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
            (4 * (n : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        ((arrayMeasure N).real
            (A ∩ ShiftedQplResidual.shiftedContDefect p m i j σ w M n) +
          (arrayMeasure N).real (A ∩ QplWindow.harmDefect p m j V w M)) := by
  have hsub : A ∩ {U : Array N | ¬ (-(ProjLedger.Qpl p m eps i j t U
        - ProjLedger.Qpl p m eps i j s U) ≤ KQ * L34)}
      ⊆ A ∩ qplDrop (ProjLedger.Qpl p m eps i j) σ n (KQ * L34) := by
    rintro U ⟨hUA, hU⟩
    refine ⟨hUA, ?_⟩
    by_contra hcon
    exact hU (notMem_qplDrop hcon hσs hst htn)
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _))
    (measureReal_qplDrop_le (N := N) hp0 hp1 m eps i j hε hn hA hV1 hw hKQ hL34)

end LocOccQ

namespace LocOccQ

variable {N : ℕ}

/-- **The paper's `(lococc)` display in its literal indicator form on the actual record cell.**

Identical to `lococc_recCell_eighth` but with the summand written as the paper writes it,
`1{X_u^i <= M_u^j}` (as an `if` on the actual integer position and running record).  The passage
between the two is `recCell_occInd`, i.e. the paper's `X_u^i >= 0` on `{d_r <= L}`. -/
theorem lococc_recCell_indicator {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {ε : ℝ} (hε : 0 < ε) {r s t T L : ℕ} (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    {U : Array N} (hU : U ∈ recCell p m i j r s L)
    {K β Kp CH KQ KF L34 : ℝ}
    (hled : ∀ u : ℕ,
      SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u - 1 / 8
        ≤ (Zproj p m ε i j U (u + 1) - Zproj p m ε i j U u)
          + VdriftAssembly.Jcorr p m ε i j U u
          - (ProjLedger.Qpl p m ε i j (u + 1) U - ProjLedger.Qpl p m ε i j u U))
    (hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ)
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)
    (hslopeHi : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ∧
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ≤ Kp)
    (hint : ∀ a b : ℕ, r - (T + 2) * L ≤ a →
      b ≤ r - (T + 2) * L + ((2 * T + 2) * L + 1) → a ≤ b →
      ∑ x ∈ Finset.Ico a b,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2
        ≤ K * ((b : ℝ) - (a : ℝ)) + K * β)
    (hosc : projH p m j t U (((trajectory p m U s).pos i).toNat : ℤ)
        - projH p m j s U (((trajectory p m U s).pos i).toNat : ℤ) ≤ CH * L34)
    (hQd : U ∉ qplDrop (ProjLedger.Qpl p m ε i j) s (T * L) (KQ * L34))
    (hFs : |SwarmOcc.Fcorr (aRec p m) ε (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s)| ≤ KF * L34)
    (hFt : |SwarmOcc.Fcorr (aRec p m) ε (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)| ≤ KF * L34)
    (hK : 1 ≤ K) (hβ : 0 ≤ β) (hKp : 0 ≤ Kp) (hCH : 0 ≤ CH) (hKF : 0 ≤ KF)
    (hKQ : 0 ≤ KQ) (hL34 : 0 ≤ L34) (h1L34 : 1 ≤ L34) (hβL : β ≤ L34) :
    ∑ u ∈ Finset.Ico s t,
        (if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0)
      ≤ ((K + Kp) + 2 * (2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) * K + 1) *
          (((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ)
            + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
            + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
        + ((t : ℝ) - (s : ℝ)) / 8
        + (K + CH + 2 * KF
            + 4 * (2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2))) * K
            + 2 * KQ + 1) * L34 := by
  have hcongr : ∑ u ∈ Finset.Ico s t,
        (if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0)
      = ∑ u ∈ Finset.Ico s t,
        SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hu
    exact (recCell_occInd hr hU h1 (by omega)).symm
  rw [hcongr]
  exact lococc_recCell_eighth hp0 hp1 hε hT hr hst htT hU hled hslopeLo hslopeHi hint hosc hQd
    hFs hFt hK hβ hKp hCH hKF hKQ hL34 h1L34 hβL

end LocOccQ

namespace LocOccQ

variable {N : ℕ}

/-! ### 8. The pointwise ledger in the exact shape used, almost surely

`lococc_recCell_eighth` takes `hled` as a pointwise hypothesis with `Z` the *definitional*
`Swarming.Enl.Zproj = projH − Fcorr`.  The accepted `LocOcc.ae_step_ledger_actual` supplies the
same inequality with `Z` the optional projection `ProjLedger.Zproj = condExp Zpot`, which
`ProjLedgerBridge.Zproj_eq_optional_projection` identifies only almost surely.  A countable
intersection over `t` therefore converts one into the other, so `hled` holds
`arrayMeasure N`-almost surely with no extra hypothesis.  This is the honest status of the field:
not assumed, but a.e. rather than pointwise (the same status as `hslopeLo`/`hslopeHi`, which come
from `condExp` linearity below the record). -/

/-- The two projected `Z` processes agree at every time, almost surely. -/
theorem ae_Zproj_eq_ProjLedger_Zproj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ t : ℕ,
      Zproj p m ε i j U t = ProjLedger.Zproj p m ε i j t U := by
  rw [MeasureTheory.ae_all_iff]
  intro t
  exact ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp0 hp1 t i j hε

/-- **`hled` almost surely, in the exact shape of `lococc_recCell_eighth`.** -/
theorem ae_hled {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ u : ℕ,
      SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u - ε
        ≤ (Zproj p m ε i j U (u + 1) - Zproj p m ε i j U u)
          + VdriftAssembly.Jcorr p m ε i j U u
          - (ProjLedger.Qpl p m ε i j (u + 1) U - ProjLedger.Qpl p m ε i j u U) := by
  filter_upwards [LocOcc.ae_step_ledger_actual (N := N) hp0 hp1 hm hij hε,
    ae_Zproj_eq_ProjLedger_Zproj (N := N) hp0 hp1 (i := i) (j := j) hε] with U hU hZ
  intro u
  rw [hZ (u + 1), hZ u]
  exact hU u

/-- The `ε = 1/8` instance, i.e. the `hled` field of `LocOcc.lococc_window_eighth`, a.s. -/
theorem ae_hled_eighth {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ u : ℕ,
      SwarmOcc.occInd (fun q => (trajectory p m U q).pos i)
          (fun q => runMax p m U j q) u - 1 / 8
        ≤ (Zproj p m (1 / 8) i j U (u + 1) - Zproj p m (1 / 8) i j U u)
          + VdriftAssembly.Jcorr p m (1 / 8) i j U u
          - (ProjLedger.Qpl p m (1 / 8) i j (u + 1) U - ProjLedger.Qpl p m (1 / 8) i j u U) :=
  ae_hled hp0 hp1 hm hij (by norm_num)

end LocOccQ
