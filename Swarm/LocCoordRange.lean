/-
  **(loccoord) in the exact form used in the proof of `(locmove)`.**

  The paper's proof of `(locmove)` writes (main_1d_revised.tex, proof of Prop. `local`)

      (1/|A|) Σ_{i∈A} (H_t^A(X_t^i) - H_s^A(X_s^i))
        ≤ H_t^A(R_t^A) - H_t^A(min_{i∈A} X_s^i)
        ≤ C (R_t^A - min_{i∈A} X_s^i) + C_T L^{3/4},

  with `R_t^A = max_{i∈A} M_t^i` and `i ∈ A` chosen so that `M_t^i = R_t^A`.

  `Loccoord.loccoord_average` supplies this for an arbitrary interval `[a0,b0)` and arbitrary
  leader `i`.  This file closes the remaining index identifications:

  * `loccoord_range_of_hsum` — the deterministic reduction: `a0 := (min_{k∈B} X_s^k).toNat`,
    `b0 := (R_t^B).toNat`, leader `i` the `sup'` argument.  Hypotheses: nonnegativity of the
    two extremal positions and the `(locsum)` bound on the single interval `[min X_s, R_t^B)`.
  * `loccoord_record_window` — the same on the actual `(locsum)` event
    (`LocSumR1.array_locsum_h`), with the record-window start `A = r - (T+2)L` of
    Proposition `local` substituted.  The paper's side condition `r ≥ (T+3)L` is exactly what
    makes `A ≥ L`, the hypothesis of `array_locsum_h`.

  No `sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`.
-/
import Swarm.LocCoordActual

set_option linter.unusedVariables false

open Finset
open scoped BigOperators

namespace Loccoord

noncomputable section

variable {N : ℕ}

/-- `R_t^B = max_{k∈B} M_t^k`, the paper's `R_t^A`. -/
noncomputable def Rmax (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (B : Finset (Fin N))
    (hB : B.Nonempty) (t : ℕ) : ℤ :=
  B.sup' hB (fun k => Swarming.Trajectory.runMax p m U k t)

/-- `min_{k∈B} X_s^k`, the lower end of the interval in the paper's `(loccoord)`. -/
noncomputable def Xmin (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (B : Finset (Fin N))
    (hB : B.Nonempty) (s : ℕ) : ℤ :=
  B.inf' hB (fun k => SepGroup.Model.X p m U s k)

/-- `Xmin ≤ Rmax` for `s ≤ t`. -/
lemma Xmin_le_Rmax {p : ℝ} {m : ℕ} (U : Swarming.Uniform.Array N) {B : Finset (Fin N)}
    (hB : B.Nonempty) {s t : ℕ} (hst : s ≤ t) :
    Xmin p m U B hB s ≤ Rmax p m U B hB t := by
  have hne : B.Nonempty := hB
  obtain ⟨k, hk⟩ := hne
  have h1 : Xmin p m U B hB s ≤ SepGroup.Model.X p m U s k :=
    Finset.inf'_le (fun k => SepGroup.Model.X p m U s k) hk
  have h2 : SepGroup.Model.X p m U s k ≤ Swarming.Trajectory.runMax p m U k t :=
    SepGroup.Model.le_runMax_of_le p m U t k hst
  have h3 : Swarming.Trajectory.runMax p m U k t ≤ Rmax p m U B hB t :=
    Finset.le_sup' (fun k => Swarming.Trajectory.runMax p m U k t) hk
  linarith

/-- **`(loccoord)` with the paper's extremal endpoints.** -/
theorem loccoord_range_of_hsum {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (U : Swarming.Uniform.Array N) {B : Finset (Fin N)} (hB : B.Nonempty) {s t : ℕ}
    (hst : s ≤ t) (hX0 : 0 ≤ Xmin p m U B hB s)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hsum : ∀ i ∈ B,
      ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ K * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ)) + K * β) :
    Swarming.Group.average B (fun k =>
        SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
          - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
      ≤ ((K + 1) / 2) * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + (K / 2) * β := by
  obtain ⟨i, hiB, hieq⟩ := Finset.exists_mem_eq_sup' hB
    (fun k => Swarming.Trajectory.runMax p m U k t)
  set a0 : ℕ := (Xmin p m U B hB s).toNat with ha0
  set b0 : ℕ := (Rmax p m U B hB t).toNat with hb0
  have hca : ((a0 : ℕ) : ℤ) = Xmin p m U B hB s := Int.toNat_of_nonneg hX0
  have hR0 : 0 ≤ Rmax p m U B hB t := le_trans hX0 (Xmin_le_Rmax (p := p) (m := m) U hB hst)
  have hcb : ((b0 : ℕ) : ℤ) = Rmax p m U B hB t := Int.toNat_of_nonneg hR0
  have hcasta : ((a0 : ℕ) : ℝ) = ((Xmin p m U B hB s : ℤ) : ℝ) := by
    have h : ((a0 : ℕ) : ℤ) = Xmin p m U B hB s := hca
    exact_mod_cast h
  have hcastb : ((b0 : ℕ) : ℝ) = ((Rmax p m U B hB t : ℤ) : ℝ) := by
    have h : ((b0 : ℕ) : ℤ) = Rmax p m U B hB t := hcb
    exact_mod_cast h
  have hXa : ∀ k ∈ B, (a0 : ℤ) ≤ SepGroup.Model.X p m U s k := by
    intro k hk
    rw [hca]
    exact Finset.inf'_le (fun k => SepGroup.Model.X p m U s k) hk
  have hXb : ∀ k ∈ B, SepGroup.Model.X p m U t k ≤ (b0 : ℤ) := by
    intro k hk
    rw [hcb]
    exact le_trans (SepGroup.Model.le_runMax_pos p m U t k)
      (Finset.le_sup' (fun k => Swarming.Trajectory.runMax p m U k t) hk)
  have hbR : (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i t := by
    rw [hcb]
    exact hieq.le
  have hab : a0 ≤ b0 := by
    have h := Xmin_le_Rmax (p := p) (m := m) U hB hst
    rw [← hca, ← hcb] at h
    exact_mod_cast h
  have hsumI : ∑ x ∈ Finset.Ico a0 b0,
      (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ K * ((b0 : ℝ) - (a0 : ℝ)) + K * β := by
    have h := hsum i hiB
    calc ∑ x ∈ Finset.Ico a0 b0, (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
        ≤ K * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ)) + K * β := h
      _ = K * ((b0 : ℝ) - (a0 : ℝ)) + K * β := by rw [← hcastb, ← hcasta]
  have hmain := loccoord_average (p := p) (m := m) (N := N) hp hp1 U hst hB hiB hab
    hXa hXb hbR hK hβ hsumI
  have hgoal : ((K + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + (K / 2) * β
      = ((K + 1) / 2) * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + (K / 2) * β := by
    rw [hcastb, hcasta]
  rw [hgoal] at hmain
  exact hmain

/-- **(loccoord) from an explicit `(locsum)` event.**  Deterministic consumer of a
`(locsum)` display on the window `[A, A+Lw)`: off the bad set, for every group, every pair
`s ≤ t` and every interval `[a0,b0) ⊆ [A, A+Lw)` with `b0 ≤ R_t^B`,

    average_{k∈B} (H_t^B(X_t^k) - H_s^B(X_s^k))
      ≤ ((2C+1)/2)(R_t^B - min_{k∈B} X_s^k) + 3C β. -/
theorem loccoord_range_of_event {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (U : Swarming.Uniform.Array N) {C : ℝ} {Lw A : ℕ} {β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hbound : ∀ j : Fin N, ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + Lw → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0,
        (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x) ^ 2
        ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 6 * C * β)
    {B : Finset (Fin N)} (hB : B.Nonempty) {s t : ℕ} (hst : s ≤ t)
    (hX0 : 0 ≤ Xmin p m U B hB s) (hAle : A ≤ (Xmin p m U B hB s).toNat)
    (hLb : (Rmax p m U B hB t).toNat ≤ A + Lw) :
    Swarming.Group.average B (fun k =>
        SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
          - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
      ≤ ((2 * C + 1) / 2)
          * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
        + 3 * C * β := by
  have hp0 : p ≠ 0 := by linarith
  have hR0 : 0 ≤ Rmax p m U B hB t := le_trans hX0 (Xmin_le_Rmax (p := p) (m := m) U hB hst)
  have hcastR : (((Rmax p m U B hB t).toNat : ℕ) : ℝ) = ((Rmax p m U B hB t : ℤ) : ℝ) := by
    have h2 : (((Rmax p m U B hB t).toNat : ℕ) : ℤ) = Rmax p m U B hB t :=
      Int.toNat_of_nonneg hR0
    exact_mod_cast h2
  have hcastX : (((Xmin p m U B hB s).toNat : ℕ) : ℝ) = ((Xmin p m U B hB s : ℤ) : ℝ) := by
    have h2 : (((Xmin p m U B hB s).toNat : ℕ) : ℤ) = Xmin p m U B hB s :=
      Int.toNat_of_nonneg hX0
    exact_mod_cast h2
  have hab : (Xmin p m U B hB s).toNat ≤ (Rmax p m U B hB t).toNat :=
    Int.toNat_le_toNat (Xmin_le_Rmax (p := p) (m := m) U hB hst)
  have hsum : ∀ i ∈ B,
      ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ 2 * C * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 6 * C * β := by
    intro i hiB
    have hb := hbound i (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat hAle hLb hab
    rw [hcastR, hcastX] at hb
    have hbridge : ∀ x : ℕ, Cookie.hfix (SepGroup.Model.omegaN p m U i) x
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U i) x :=
      fun x => hfix_omegaN_eq_hof hp0 i x
    have hcongr : ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
        = ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U i) x) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [hbridge x]
    rw [hcongr]
    exact hb
  have hsum' : ∀ i ∈ B,
      ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ 2 * C * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 2 * C * (3 * β) := by
    intro i hiB
    have := hsum i hiB
    linarith [this]
  have hmain := loccoord_range_of_hsum (p := p) (m := m) (N := N) hp hp1 U hB hst hX0
    (K := 2 * C) (β := 3 * β) (by linarith) (by linarith) hsum'
  have harith : ((2 * C + 1) / 2)
      * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
      + ((2 * C) / 2) * (3 * β)
      = ((2 * C + 1) / 2)
        * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
        + 3 * C * β := by ring
  rw [harith] at hmain
  exact hmain

/-- **(loccoord) on the record window, on the actual `(locsum)` event.**

For `r ≥ (T+3)L` and `A = r - (T+2)L` (the window start of Proposition `local`), off an event
of `arrayMeasure` at most `exp(-c L^{1/16})`, every group `B` and every pair `s ≤ t` satisfies

    average_{k∈B} (H_t^B(X_t^k) - H_s^B(X_s^k))
      ≤ ((2C+1)/2)(R_t^B - min_{k∈B} X_s^k) + 3Cβ,     β = betaT (xOf L) ≈ L^{3/8},

provided the whole interval `[min_{k∈B} X_s^k, R_t^B)` lies in `[A, A+L)`. -/
theorem loccoord_record_window {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N (LocSumR1.LsBad N p m C L (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L)) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C L (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r - (T + 2) * L + L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf L) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := LocSumR1.array_locsum_h (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, L₀, ?_⟩
  intro L hLbig T r hr
  have hLle : L ≤ r - (T + 2) * L := by
    have hmul : (T + 2) * L + L = (T + 3) * L := by ring
    omega
  obtain ⟨hmeas, hbound⟩ := hL L hLbig (r - (T + 2) * L) hLle
  exact ⟨hmeas, fun U hU B hB s t hst hX0 hAle hLb =>
    loccoord_range_of_event (p := p) (m := m) (N := N) (le_of_lt hp1) (le_of_lt hp2) U
      (C := C) (Lw := L) (A := r - (T + 2) * L) (β := ((LocSumAct.betaT (LocSumAct.xOf L) : ℝ)))
      (by linarith) (by positivity)
      (fun j a0 b0 ha hb hab => hbound U hU j a0 b0 ha hb hab) hB hst hX0 hAle hLb⟩

/-- **(loccoord) on the full record window.**  Same, but with the `(locsum)` window enlarged to
length `(2T+4)L`, which covers the **whole** interval range of Proposition `local`,
`r-(T+2)L ≤ a0 ≤ b0 ≤ r + (T+2)L` (the paper needs `b0 ≤ R_n^A ≤ r+TL`).  `array_locsum_h`
requires its window start to be at least the window length, which is why the side condition on
`r` becomes `(3T+6)L ≤ r` here; the paper's `r ≥ (T+3)L` suffices for its own `(locsum)` on
`[r-(T+3)L, r+(T+3)L]`, whose start is not constrained to exceed the length. -/
theorem loccoord_full_window {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := LocSumR1.array_locsum_h (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, L₀, ?_⟩
  intro L hLbig T r hr
  have hLw : L₀ ≤ (2 * T + 4) * L := by
    have h1 : 1 ≤ 2 * T + 4 := by omega
    calc L₀ ≤ L := hLbig
      _ = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L h1
      _ = (2 * T + 4) * L := Nat.mul_comm _ _
  have hAle : (2 * T + 4) * L ≤ r - (T + 2) * L := by
    have hmul : (T + 2) * L + (2 * T + 4) * L = (3 * T + 6) * L := by ring
    omega
  obtain ⟨hmeas, hbound⟩ := hL ((2 * T + 4) * L) hLw (r - (T + 2) * L) hAle
  refine ⟨hmeas, ?_⟩
  intro U hU B hB s t hst hX0 hXmin hRmax
  have hconv : (Rmax p m U B hB t).toNat ≤ r - (T + 2) * L + (2 * T + 4) * L := by
    have he : (2 * T + 4) * L = 2 * ((T + 2) * L) := by ring
    have hsum' : (T + 2) * L + (2 * T + 4) * L = (3 * T + 6) * L := by ring
    have h2 : (T + 2) * L ≤ r := by omega
    omega
  exact loccoord_range_of_event (p := p) (m := m) (N := N) (le_of_lt hp1) (le_of_lt hp2) U
    (C := C) (Lw := (2 * T + 4) * L) (A := r - (T + 2) * L)
    (β := ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)))
    (by linarith) (by positivity)
    (fun j a0 b0 ha hb hab => hbound U hU j a0 b0 ha hb hab) hB hst hX0 hXmin hconv

end

end Loccoord
