/-
  # Squeezing the `Qpl` residual budget at the paper's record carrier

  The accepted `SummedSlope.Carrier.lococc_actual_carrier_summed` and
  `LocOccRecordCarrier.measureReal_recordCarrier_qplDrop_le` carry two *separately named* residual
  masses on the record carrier:

  * `ShiftedQplResidual.shiftedContDefect` — the failure, at some future time `s + k`, of the
    record/position window (the "geometric" half of the deterministic `Qpl` window), and
  * `QplWindow.harmDefect` — the failure of the harmonic site cap `h_j ≤ V` on an interval of
    sites.

  The summed-slope carrier separately assumes `(locmax)`, the cap `h_j ≤ Lw^{1/16}` on
  `[A - 1, A + Lw)`, in order to absorb the additive seed defect `e_0/(1-a)`.

  This file proves that, **at the paper's own carrier parameters**

      A = r - (T+2)L,      Lw = (2T+2)L + 1,

  the first residual never occurs at all (`shiftedContDefect` is *identically empty* on the
  record carrier), and that the second residual at the slightly longer window
  `M = Lw + 1 = (2T+2)L + 2` is *the same event* whose complement gives `(locmax)` on the paper's
  interval `[A - 1, A + Lw)`, hence also absorbs the `e_0/(1-a)` seed.

  Nothing is dropped: the geometric residual is *proved* to have measure zero on the carrier, and
  the harmonic residual is *identified* with the `(locmax)` premise.  Then, composing with the
  public `WideRepair.array_locmax_bound_paper_window` (which does allow an arbitrary site window
  `[A - M, A + Up)`), that single residual is bounded by `exp (-c * Lw^{1/16})`, so the `Qpl` book-
  keeping on the record carrier becomes fully quantitative:

      mu(carrier ∩ qplDrop(Qpl, s, n, KQ L34))
        <= mu(carrier) * (maximal-Azuma price at V = Lw^{1/16})  +  exp (-c * Lw^{1/16}),

  for `L >= L_0`, `n <= T L`, `(T+3)L <= r`, with no unnamed residual and no joint-probability
  claim.

  The strengthened window containment used here (`X^i`, `M^j <= r + TL`, i.e. strictly below
  `A + Lw`) is a two-line sharpening of `LocOccRecordCarrier.carrier_window_containment`, whose
  upper bound there is `r + TL + 1`; it is what makes the paper's interval `[A-1, A+Lw)` the
  correct harmonic window rather than one site short.

  No `sorry`, no `axiom`, no `native_decide`; axiom closures are checked externally in
  `CarrierQplResidualAudit.lean`.
-/
import Swarm.LocOccRecordCarrier
import Swarm.SummedSlope
import Swarm.ShiftedQplResidual

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.Enl.VdriftAssembly Swarming.Enl.ProjLedger
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier

namespace CarrierQplResidual

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The paper's window parameters at the record carrier

`A = r - (T+2)L` and `Lw = (2T+2)L + 1` are the parameters used by the accepted summed-slope
carrier; `cM = Lw + 1` is the one-site-longer harmonic window forced by the `Qpl` site condition
`X^i + 2 ≤ A + M`. -/

/-- The paper's `A = r - (T+2)L`. -/
def cA (r T L : ℕ) : ℕ := r - (T + 2) * L

/-- The paper's `Lw = (2T+2)L + 1`. -/
def cLw (T L : ℕ) : ℕ := (2 * T + 2) * L + 1

/-- The harmonic window length needed by the `Qpl` site window: `cM = Lw + 1 = (2T+2)L + 2`. -/
def cM (T L : ℕ) : ℕ := (2 * T + 2) * L + 2

/-- The integer cast of `A` in the paper's regime. -/
theorem cA_cast {r T L : ℕ} (h : (T + 2) * L ≤ r) :
    ((cA r T L : ℕ) : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) := by
  unfold cA
  exact Nat.cast_sub h

/-- `A + Lw = r + TL + 1`. -/
theorem cA_add_cLw {r T L : ℕ} (h : (T + 2) * L ≤ r) :
    cA r T L + cLw T L = r + T * L + 1 := by
  have h2 : (2 * T + 2) * L = (T + 2) * L + T * L := by ring
  unfold cA cLw
  rw [h2]
  omega

/-- `A + cM = r + TL + 2`. -/
theorem cA_add_cM {r T L : ℕ} (h : (T + 2) * L ≤ r) :
    cA r T L + cM T L = r + T * L + 2 := by
  have h2 : (2 * T + 2) * L = (T + 2) * L + T * L := by ring
  unfold cA cM
  rw [h2]
  omega

/-- `Lw <= Lw + 1`. -/
theorem cLw_le_cM (T L : ℕ) : cLw T L ≤ cM T L := by
  unfold cLw cM
  omega

/-- `cM = Lw + 1` exactly, which is what the `Qpl` site condition `X + 2 ≤ A + M` costs. -/
theorem cLw_succ (T L : ℕ) : cLw T L + 1 = cM T L := by
  unfold cLw cM
  ring

/-- `1 <= Lw`, so the paper's harmonic cap level `xOf Lw` is at least `1`. -/
theorem one_le_cLw (T L : ℕ) : 1 ≤ cLw T L := by
  unfold cLw
  omega

/-- `1 ≤ A` as soon as `(T+2)L + 1 ≤ r`. -/
theorem one_le_cA {r T L : ℕ} (h : (T + 2) * L + 1 ≤ r) : 1 ≤ cA r T L := by
  unfold cA
  omega

/-! ### 2. The sharp window containment at the paper's window

`LocOccRecordCarrier.carrier_window_containment` gives `X^i, M^j ≤ r + TL + 1`.  Unit steps from
the first-record prefix give the sharp bound `≤ r + TL`, which is exactly `A + Lw - 1`: the paper's
half-open site interval `[A - 1, A + Lw)` therefore covers the whole window. -/

/-- **Sharp window containment.**  On the record carrier, every walker position and running record
in the window `[s, s + TL]` lies in `[r - (T+2)L, r + TL]`, i.e. in `[A, A + Lw)`. -/
theorem carrier_window_sharp {p : ℝ} {m r s L T : ℕ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (i j : Fin N) {s' : ℕ} (h1 : s ≤ s') (h2 : s' ≤ s + T * L) :
    (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ (trajectory p m U s').pos i ∧
      (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ runMax p m U j s' ∧
      (trajectory p m U s').pos i ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) ∧
      runMax p m U j s' ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
  obtain ⟨hloX, hloMj, -, -, -⟩ :=
    LocOccRecordCarrier.carrier_window_containment (N := N) hU i j h1 h2
  have hel : ((s' - s : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    exact_mod_cast (show s' - s ≤ T * L by omega)
  have hMj := LocOccRecordCarrier.runMax_le_add (N := N) hU j h1
  have hMi := LocOccRecordCarrier.runMax_le_add (N := N) hU i h1
  have hposX : (trajectory p m U s').pos i ≤ runMax p m U i s' :=
    Finset.le_sup' (s := Finset.range (s' + 1))
      (f := fun t => (trajectory p m U t).pos i) (Finset.mem_range.mpr (Nat.lt_succ_self s'))
  exact ⟨hloX, hloMj, by linarith, by linarith⟩

/-! ### 3. The geometric `Qpl` residual is identically empty on the carrier -/

/-- **Per-time window at the paper's parameters.**

On the record carrier, at every time `u` of the window `[s, s + TL]`, both walker `i`'s position and
walker `j`'s running record lie in the integer interval `[A, A + Lw)`, and walker `i`'s running
record satisfies `A ≤ M^i` and `M^i + 1 ≤ A + Lw`.  These are exactly the three geometric
premises `hcellX`, `hcellMj`, `hcellMi` of
`SummedSlope.Carrier.lococc_actual_carrier_summed`, at `A = r - (T+2)L` and `Lw = (2T+2)L + 1`. -/
theorem carrier_time_window {p : ℝ} {m r s L T u : ℕ} (hA0 : (T + 2) * L ≤ r)
    {U : Array N} (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (i j : Fin N) (hsu : s ≤ u) (huT : u ≤ s + T * L) :
    (cA r T L ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < cA r T L + cLw T L) ∧
      (cA r T L ≤ (runMax p m U j u).toNat ∧
        (runMax p m U j u).toNat < cA r T L + cLw T L) ∧
      (cA r T L ≤ (runMax p m U i u).toNat ∧
        (runMax p m U i u).toNat + 1 ≤ cA r T L + cLw T L) := by
  obtain ⟨hloX, hloMj, hupX, hupMj⟩ := carrier_window_sharp hU i j hsu huT
  have hupMi := LocOccRecordCarrier.runMax_le_add (N := N) hU i hsu
  have hcastA : ((cA r T L : ℕ) : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) := cA_cast hA0
  have hcastLw : ((cA r T L + cLw T L : ℕ) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by
    rw [cA_add_cLw hA0]
    push_cast
    ring
  have hcastTL : ((r + T * L : ℕ) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) := by push_cast; ring
  have hneg : (0 : ℤ) ≤ (cA r T L : ℤ) := by exact_mod_cast (Nat.zero_le _)
  -- walker `i`'s position lies in `[A, A + Lw)`
  have hpos : cA r T L ≤ ((trajectory p m U u).pos i).toNat ∧
      ((trajectory p m U u).pos i).toNat < cA r T L + cLw T L := by
    have hAc : ((cA r T L : ℕ) : ℤ) ≤ (trajectory p m U u).pos i := by
      rw [hcastA]; exact hloX
    have hz : (0 : ℤ) ≤ (trajectory p m U u).pos i := le_trans hneg hAc
    have hAlw : (trajectory p m U u).pos i < ((cA r T L + cLw T L : ℕ) : ℤ) := by
      rw [hcastLw]; linarith
    exact ⟨(Int.le_toNat hz).mpr hAc, (Int.toNat_lt hz).mpr hAlw⟩
  -- walker `j`'s running record lies in `[A, A + Lw)`
  have hrecj : cA r T L ≤ (runMax p m U j u).toNat ∧
      (runMax p m U j u).toNat < cA r T L + cLw T L := by
    have hz : (0 : ℤ) ≤ runMax p m U j u := by
      rw [Swarming.Enl.runMax_eq_recVal]
      exact zero_le_recVal_prefOf p m U j u
    have hAc : ((cA r T L : ℕ) : ℤ) ≤ runMax p m U j u := by
      rw [hcastA]; exact hloMj
    have hAlw : runMax p m U j u < ((cA r T L + cLw T L : ℕ) : ℤ) := by
      rw [hcastLw]; linarith
    exact ⟨(Int.le_toNat hz).mpr hAc, (Int.toNat_lt hz).mpr hAlw⟩
  -- walker `i`'s running record satisfies `A <= M^i` and `M^i + 1 <= A + Lw`
  have hreci : cA r T L ≤ (runMax p m U i u).toNat ∧
      (runMax p m U i u).toNat + 1 ≤ cA r T L + cLw T L := by
    have hz : (0 : ℤ) ≤ runMax p m U i u := by
      rw [Swarming.Enl.runMax_eq_recVal]
      exact zero_le_recVal_prefOf p m U i u
    have hle : (runMax p m U i u).toNat ≤ r + T * L := by
      refine (Int.toNat_le).mpr ?_
      rw [hcastTL]
      have hcast2 : (((u - s : ℕ)) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
        exact_mod_cast (show u - s ≤ T * L by omega)
      linarith
    have hAc : ((cA r T L : ℕ) : ℤ) ≤ runMax p m U i u := by
      rw [hcastA]
      refine le_trans hloX ?_
      exact Finset.le_sup' (s := Finset.range (u + 1))
        (f := fun t => (trajectory p m U t).pos i) (Finset.mem_range.mpr (Nat.lt_succ_self u))
    refine ⟨(Int.le_toNat hz).mpr hAc, ?_⟩
    have := cA_add_cLw hA0
    omega
  exact ⟨hpos, hrecj, hreci⟩

/-- **The three geometric window premises of the summed-slope carrier, discharged by the record
carrier at the paper's parameters.**

These are literally `hcellX`, `hcellMj`, `hcellMi` of
`SummedSlope.Carrier.lococc_actual_carrier_summed` with `s0 := s`, `n := T * L`, `A := cA r T L`,
`Lw := cLw T L`.  They are the only geometric inputs of that theorem; its remaining inputs are
`(locsum)`, the projected `Qpl` window, the projected oscillation window and the endpoint data. -/
theorem carrier_window_hypotheses_summed {p : ℝ} {m r s L T : ℕ} (hA0 : (T + 2) * L ≤ r)
    {U : Array N} (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (i j : Fin N) {t : ℕ} (hst : s ≤ t) (htT : t ≤ s + T * L) :
    (∀ u : ℕ, s ≤ u → u ≤ s + T * L →
        cA r T L ≤ ((trajectory p m U u).pos i).toNat ∧
          ((trajectory p m U u).pos i).toNat < cA r T L + cLw T L) ∧
      (∀ u : ℕ, s ≤ u → u ≤ s + T * L →
        cA r T L ≤ (runMax p m U j u).toNat ∧
          (runMax p m U j u).toNat < cA r T L + cLw T L) ∧
      (cA r T L ≤ (runMax p m U i t).toNat ∧
        (runMax p m U i t).toNat + 1 ≤ cA r T L + cLw T L) :=
  ⟨fun _ h1 h2 => (carrier_time_window hA0 hU i j h1 h2).1,
    fun _ h1 h2 => (carrier_time_window hA0 hU i j h1 h2).2.1,
    (carrier_time_window hA0 hU i j hst htT).2.2⟩

/-- **The record/position window of the accepted `Qpl` estimate holds identically**, for every
future time `s + k`, `k < n`, at the paper's parameters `A = r - (T+2)L` and `M = Lw + 1`. -/
theorem carrier_geom_window {p : ℝ} {m r s L T n : ℕ} (hA0 : (T + 2) * L ≤ r)
    (hn : n ≤ T * L) {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) (i j : Fin N) :
    (∀ k < n, cA r T L ≤ (recVal j (prefOf p m (s + k) U)).toNat ∧
        (recVal j (prefOf p m (s + k) U)).toNat < cA r T L + cM T L) ∧
      (∀ k < n, cA r T L ≤ ((trajectory p m U (s + k)).pos i).toNat ∧
        ((trajectory p m U (s + k)).pos i).toNat + 2 ≤ cA r T L + cM T L) := by
  constructor
  · intro k hk
    obtain ⟨-, ⟨hlo, hup⟩, -⟩ :=
      carrier_time_window hA0 hU i j (Nat.le_add_right s k) (by omega)
    rw [← Swarming.Enl.runMax_eq_recVal]
    exact ⟨hlo, by have := cLw_le_cM T L; omega⟩
  · intro k hk
    obtain ⟨⟨hlo, hup⟩, -, -⟩ :=
      carrier_time_window hA0 hU i j (Nat.le_add_right s k) (by omega)
    exact ⟨hlo, by have := cLw_succ T L; omega⟩

/-- **The geometric `Qpl` residual never occurs on the paper's record carrier.**

`shiftedContDefect p m i j s A (Lw+1) n` consists exactly of the negations of the two window
clauses just proved, so its intersection with the carrier is *empty*, not merely small. -/
theorem carrier_inter_shiftedContDefect_eq_empty {p : ℝ} {m r s L T n : ℕ}
    (hA0 : (T + 2) * L ≤ r) (hn : n ≤ T * L) (i j : Fin N) :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        ShiftedQplResidual.shiftedContDefect p m i j s (cA r T L) (cM T L) n = ∅ := by
  ext U
  constructor
  · rintro ⟨hU, hdef⟩
    obtain ⟨h1, h2⟩ := carrier_geom_window (p := p) (m := m) (r := r) (s := s) (L := L)
      (T := T) (n := n) hA0 hn hU i j
    unfold ShiftedQplResidual.shiftedContDefect at hdef
    rcases hdef with ⟨k, hk, hbad⟩ | ⟨k, hk, hbad⟩
    · exact hbad ⟨(h1 k hk).1, (h1 k hk).2⟩
    · exact hbad ⟨(h2 k hk).1, (h2 k hk).2⟩
  · intro h0
    simp at h0

/-- **The deterministic window is available on the carrier as soon as the single harmonic cap
holds.**  This is `ShiftedQplResidual.shiftedQplWindow` at the paper's parameters. -/
theorem carrier_mem_shiftedQplWindow {p : ℝ} {m r s L T n : ℕ} (hA0 : (T + 2) * L ≤ r)
    (hn : n ≤ T * L) {i j : Fin N} {V : ℝ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hV : U ∉ QplWindow.harmDefect p m j V (cA r T L) (cM T L)) :
    U ∈ ShiftedQplResidual.shiftedQplWindow p m i j V s (cA r T L) (cM T L) n := by
  obtain ⟨h1, h2⟩ := carrier_geom_window hA0 hn hU i j
  have hh : ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cM T L),
      hof p (siteMarks p m U j) y ≤ V := by
    have hV' := hV
    unfold QplWindow.harmDefect at hV'
    simp only [Set.mem_ofPred_eq] at hV'
    exact not_not.mp hV'
  exact ⟨h1, hh, h2⟩

/-! ### 4. The `Qpl` mass estimate with one residual instead of two

The accepted `LocOccRecordCarrier.measureReal_recordCarrier_qplDrop_le` charges the carrier-weighted
`shiftedContDefect` mass.  Section 3 shows that mass is zero at the paper's parameters, so the
estimate survives with the harmonic residual only. -/

/-- The carrier-weighted `shiftedContDefect` mass is exactly zero at the paper's parameters. -/
theorem measureReal_carrier_inter_shiftedContDefect {p : ℝ} {m r s L T n : ℕ}
    (hA0 : (T + 2) * L ≤ r) (hn : n ≤ T * L) (i j : Fin N) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          ShiftedQplResidual.shiftedContDefect p m i j s (cA r T L) (cM T L) n) = 0 := by
  rw [MeasureTheory.Measure.real_def,
    carrier_inter_shiftedContDefect_eq_empty (p := p) (m := m) hA0 hn i j, measure_empty,
    ENNReal.toReal_zero]

/-- **The adapted `Qpl` window estimate on the record carrier, with the geometric residual proved
zero rather than estimated.**

Only the harmonic residual `carrier ∩ harmDefect p m j V A (Lw+1)` remains in addition to the
maximal-Azuma price.  No residual is dropped: the geometric one is shown identically absent. -/
theorem measureReal_recordCarrier_qplDrop_singleResidual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N) (hε : 0 < eps) {r s T L n : ℕ}
    (hn : 1 ≤ n) (hnTL : n ≤ T * L) (hA0 : (T + 2) * L ≤ r) (hA1 : 1 ≤ cA r T L)
    {V : ℝ} (hV1 : 1 ≤ V) {KQ L34 : ℝ} (hKQ : 0 < KQ) (hL34 : 0 < L34) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m eps i j) s n (KQ * L34)) ≤
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
            (4 * (n : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j V (cA r T L) (cM T L)) := by
  have hmain := LocOccRecordCarrier.measureReal_recordCarrier_qplDrop_le (N := N) hp0 hp1 m eps i j
    hε (r := r) (s := s) (n := n) hn hV1 (w := cA r T L) (M := cM T L) hA1 hKQ hL34 L
  have hzero := measureReal_carrier_inter_shiftedContDefect (N := N) (p := p) (m := m)
    (r := r) (s := s) (L := L) (T := T) (n := n) hA0 hnTL i j
  rw [hzero, zero_add] at hmain
  exact hmain

/-! ### 5. The harmonic residual is the `(locmax)` event of the summed-slope carrier -/

/-- **The single remaining residual supplies `(locmax)`.**

If the carrier point avoids the harmonic defect on the slightly longer window
`[A - 1, A + Lw + 1)`, then the paper's `(locmax)` cap holds on its own interval `[A - 1, A + Lw)`
— the exact hypothesis `hloc` of `SummedSlope.Carrier.lococc_actual_carrier_summed`. -/
theorem not_harmDefect_imp_locmax {p : ℝ} {m r T L : ℕ}
    {U : Array N} {j : Fin N} {V : ℝ}
    (hV : U ∉ QplWindow.harmDefect p m j V (cA r T L) (cM T L)) :
    ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
      hof p (siteMarks p m U j) y ≤ V := by
  have hV' := hV
  unfold QplWindow.harmDefect at hV'
  simp only [Set.mem_ofPred_eq] at hV'
  have hh : ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cM T L),
      hof p (siteMarks p m U j) y ≤ V := not_not.mp hV'
  intro y hy
  exact hh y (Finset.Ico_subset_Ico_right (Nat.add_le_add_left (cLw_le_cM T L) _) hy)

/-- The `(locmax)`-failure event on the paper's interval is contained in the harmonic residual. -/
theorem carrier_locmaxFail_subset_harmDefect {p : ℝ} {m r s L T : ℕ} {j : Fin N} {V : ℝ} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U | ¬ ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
          hof p (siteMarks p m U j) y ≤ V} ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        QplWindow.harmDefect p m j V (cA r T L) (cM T L) := by
  rintro U ⟨hU, hbad⟩
  refine ⟨hU, ?_⟩
  intro hcon
  exact hbad (fun y hy =>
    hcon y (Finset.Ico_subset_Ico_right (Nat.add_le_add_left (cLw_le_cM T L) _) hy))

/-- **One event, one residual mass.**  The `(locmax)`-failure mass on the carrier is no more than
the harmonic residual mass already charged by the `Qpl` estimate: the two named inputs are not
independent budgets. -/
theorem measureReal_carrier_locmaxFail_le_harmDefect {p : ℝ} (m r s L T : ℕ) (j : Fin N) (V : ℝ) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U | ¬ ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
            hof p (siteMarks p m U j) y ≤ V}) ≤
      (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          QplWindow.harmDefect p m j V (cA r T L) (cM T L)) :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (carrier_locmaxFail_subset_harmDefect (p := p) (m := m) (r := r) (s := s)
      (L := L) (T := T) (j := j) (V := V)))

/-- **The harmonic residual is the `(locmax)` failure plus exactly one site.**

At the paper's parameters the `Qpl` harmonic window is `[A - 1, A + Lw + 1)`, i.e. one site longer
than the `(locmax)` interval `[A - 1, A + Lw)`.  Consequently, on the carrier, failing the harmonic
cap means failing `(locmax)` on its own interval *or* failing the cap at the single site `A + Lw`.
The extra site is not an artefact of the proof: the `Qpl` site condition `X^i + 2 ≤ A + M` together
with the sharp bound `X^i ≤ r + TL = A + Lw - 1` forces `M ≥ Lw + 1`. -/
theorem carrier_harmDefect_subset_locmaxFail_union_top {p : ℝ} {m r s L T : ℕ} {j : Fin N}
    {V : ℝ} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        QplWindow.harmDefect p m j V (cA r T L) (cM T L) ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        ({U | ¬ ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
            hof p (siteMarks p m U j) y ≤ V} ∪
          {U | ¬ hof p (siteMarks p m U j) (cA r T L + cLw T L) ≤ V}) := by
  rintro U ⟨hU, hbad⟩
  refine ⟨hU, ?_⟩
  have hne : ∃ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cM T L),
      V < hof p (siteMarks p m U j) y := by
    by_contra hcon
    refine hbad ?_
    intro y hy
    exact not_lt.mp fun hlt => hcon ⟨y, hy, hlt⟩
  obtain ⟨y, hy, hlt⟩ := hne
  have hy' := Finset.mem_Ico.mp hy
  have hsucc : cA r T L + cM T L = cA r T L + cLw T L + 1 := by
    have := cLw_succ T L
    omega
  rw [hsucc] at hy'
  rcases lt_or_ge y (cA r T L + cLw T L) with hlt' | hge'
  · left
    intro hcon
    exact absurd (hcon y (Finset.mem_Ico.mpr ⟨hy'.1, hlt'⟩)) (not_le_of_gt hlt)
  · right
    have hyy : y = cA r T L + cLw T L := by omega
    rw [hyy] at hlt
    exact not_le_of_gt hlt

/-- **The residual mass is a `(locmax)` mass plus a one-site mass.** -/
theorem measureReal_carrier_harmDefect_le_locmaxFail_add_top {p : ℝ}
    {m r s L T : ℕ} {j : Fin N} {V : ℝ} :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          QplWindow.harmDefect p m j V (cA r T L) (cM T L)) ≤
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U | ¬ ∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
              hof p (siteMarks p m U j) y ≤ V}) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U | ¬ hof p (siteMarks p m U j) (cA r T L + cLw T L) ≤ V}) := by
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (carrier_harmDefect_subset_locmaxFail_union_top (p := p) (m := m) (r := r)
      (s := s) (L := L) (T := T) (j := j) (V := V)))) ?_
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  rintro U ⟨hU, h1 | h2⟩
  · exact Or.inl ⟨hU, h1⟩
  · exact Or.inr ⟨hU, h2⟩

/-! ### 6. The seed defect `e_0/(1-a)` is absorbed on the same event -/

/-- The record value at a time `t` of the window, at the paper's parameters: it lies in
`[A, A + Lw)`. -/
theorem carrier_recVal_window {p : ℝ} {m r s L T : ℕ} (hA0 : (T + 2) * L ≤ r)
    {U : Array N} (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (j : Fin N) {t : ℕ} (hst : s ≤ t) (htT : t ≤ s + T * L) :
    cA r T L ≤ (recVal j (prefOf p m t U)).toNat ∧
      (recVal j (prefOf p m t U)).toNat < cA r T L + cLw T L := by
  obtain ⟨-, ⟨hlo, hup⟩, -⟩ :=
    carrier_time_window hA0 hU (Classical.arbitrary (Fin N)) j hst htT
  rw [← Swarming.Enl.runMax_eq_recVal]
  exact ⟨hlo, hup⟩

/-- **The additive seed defect is absorbed by the paper-scale remainder on the same event.**

On the record carrier, if the single harmonic residual does not occur at the cap level
`V = xOf Lw`, then the summed-slope additive defect `b_n/(1-a) ≥ e_0/(1-a)` is at most
`(4/(1-a)) L34 L Lw`.  This is the `(locmax)` discharge of
`SummedSlope.Carrier.lococc_actual_carrier_summed`, obtained here from `¬ harmDefect`. -/
theorem carrier_seed_absorbed_of_not_harmDefect {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m r s L T : ℕ} (hA0 : (T + 2) * L ≤ r) (hA1 : 1 ≤ cA r T L)
    {U : Array N} (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (j : Fin N) {t : ℕ} (hst : s ≤ t) (htT : t ≤ s + T * L)
    (hV : U ∉ QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L)) :
    bRec p m t j U / (1 - aRec p m) ≤ (4 / (1 - aRec p m)) * LocOccCarrier.L34 L (cLw T L) := by
  have hrec := carrier_recVal_window (p := p) (m := m) (r := r) (s := s) (L := L) (T := T)
    hA0 hU j hst htT
  have hV1 : (1 : ℝ) ≤ xOf (cLw T L) := by
    rw [xOf]
    exact Real.one_le_rpow (by exact_mod_cast (one_le_cLw T L)) (by norm_num)
  have hcap := not_harmDefect_imp_locmax (p := p) (m := m) (r := r) (T := T) (L := L)
    (U := U) (j := j) (V := xOf (cLw T L)) hV
  have hb : bRec p m t j U ≤ xOf (cLw T L) + 2 :=
    SummedSlope.Model.bRec_le_succ_cap (N := N) hp1 hp2 hA1 hV1 hrec hcap
  exact SummedSlope.Model.bRec_div_le_L34 (N := N) (p := p) hp1 hp2 L (one_le_cLw T L) hb

/-! ### 7. The single-event interface

The three facts above are consequences of *one* event: on the carrier, avoiding
`harmDefect p m j (xOf Lw) A (Lw+1)` simultaneously gives the deterministic `Qpl` window, the
paper's `(locmax)` cap, and the absorption of the additive seed defect.  No joint probability of
these fields is asserted; what is asserted is that they share one exception set. -/

/-- **One event, three fields.**  On the paper's record carrier, outside the single harmonic-defect
event: (a) the deterministic record/position window of the `Qpl` estimate holds for the whole
window, (b) the `(locmax)` cap holds on `[A-1, A+Lw)` — the exact `hloc` of
`SummedSlope.Carrier.lococc_actual_carrier_summed` — and (c) the seed defect is absorbed by
`(4/(1-a)) L34 L Lw` at every time of the window. -/
theorem carrier_single_event_good {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m r s L T n : ℕ} (hA0 : (T + 2) * L ≤ r) (hA1 : 1 ≤ cA r T L) (hn : n ≤ T * L)
    {i j : Fin N} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hH : U ∉ QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L)) :
    U ∈ ShiftedQplResidual.shiftedQplWindow p m i j (xOf (cLw T L)) s (cA r T L) (cM T L) n ∧
      (∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
        hof p (siteMarks p m U j) y ≤ xOf (cLw T L)) ∧
      (∀ t : ℕ, s ≤ t → t ≤ s + T * L →
        bRec p m t j U / (1 - aRec p m) ≤
          (4 / (1 - aRec p m)) * LocOccCarrier.L34 L (cLw T L)) := by
  refine ⟨carrier_mem_shiftedQplWindow hA0 hn hU hH,
    not_harmDefect_imp_locmax (p := p) (m := m) (r := r) (T := T) (L := L) (U := U)
      (j := j) (V := xOf (cLw T L)) hH, ?_⟩
  intro t hst htT
  exact carrier_seed_absorbed_of_not_harmDefect (N := N) hp1 hp2 hA0 hA1 hU j hst htT hH

/-! ### 7b. The single residual is quantitatively `exp(-c * Lw^{1/16})`

The public `WideRepair.array_locmax_bound_paper_window` bounds the `(locmax)`-type cap failure on an
*arbitrary* site window `[A - M, A + Up)` by `exp (-c * L^{1/16})`.  Composing it with the exact
identification of section 5 turns the remaining harmonic residual mass into an explicit exponential
at the paper's scale, and hence makes the `Qpl` residual budget fully quantitative. -/

/-- The harmonic residual is the capped wide-locmax event, at `L = Lw`, `M = 1`, `Up = M`. -/
theorem harmDefect_subset_HMaxBadW {p : ℝ} {m r T L : ℕ} {j : Fin N} :
    QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L) ⊆
      {U : Array N | WideRepair.HMaxBadW p m (cLw T L) 1 (cM T L) (cA r T L) U} := by
  intro U hU
  simp only [QplWindow.harmDefect, Set.mem_ofPred_eq, WideRepair.HMaxBadW] at hU ⊢
  push Not at hU
  obtain ⟨y, hy, hgt⟩ := hU
  exact ⟨j, y, hy, le_of_lt hgt⟩

/-- **The carrier-weighted harmonic residual is `exp (-c * xOf Lw)`.** -/
theorem measureReal_carrier_harmDefect_le_exp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ {r s L : ℕ} {j : Fin N}, L₀ ≤ L → 1 ≤ cA r T L →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L)) ≤
        Real.exp (-c * xOf (cLw T L)) := by
  obtain ⟨c, hc, L₀, hb⟩ :=
    WideRepair.array_locmax_bound_paper_window (N := N) (p := p) hp1 hp2 hm T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro r s L j hL hA1
  have hMU : 1 + cM T L ≤ 2 * (T + 3) * (cLw T L) := by
    unfold cM cLw
    have h1 : (2 * T + 2) * L + 3 ≤ 4 * ((2 * T + 2) * L + 1) := by omega
    have h2 : 4 ≤ 2 * (T + 3) := by omega
    have h3 : 4 * ((2 * T + 2) * L + 1) ≤ 2 * (T + 3) * ((2 * T + 2) * L + 1) :=
      Nat.mul_le_mul_right _ h2
    have h4 : 1 + ((2 * T + 2) * L + 2) = (2 * T + 2) * L + 3 := by omega
    rw [h4]
    exact le_trans h1 h3
  have hL' : L₀ ≤ cLw T L := by
    have hlen : L ≤ (2 * T + 2) * L := Nat.le_mul_of_pos_left L (by omega)
    unfold cLw
    omega
  have hbnd := hb (cLw T L) hL' (cA r T L) 1 (cM T L) hA1 hMU
  have hmono : (arrayMeasure N)
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L))
      ≤ (arrayMeasure N)
        {U : Array N | WideRepair.HMaxBadW p m (cLw T L) 1 (cM T L) (cA r T L) U} :=
    measure_mono fun _ hU => harmDefect_subset_HMaxBadW hU.2
  rw [Measure.real_def]
  calc ((arrayMeasure N)
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L))).toReal
      ≤ ((arrayMeasure N)
          {U : Array N | WideRepair.HMaxBadW p m (cLw T L) 1 (cM T L) (cA r T L) U}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hmono
    _ ≤ (ENNReal.ofReal (Real.exp (-c * xOf (cLw T L)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    _ = Real.exp (-c * xOf (cLw T L)) := ENNReal.toReal_ofReal (Real.exp_pos _).le

/-- **The `Qpl` window estimate on the record carrier with *no* unnamed residual.**

The geometric residual is empty (section 3) and the harmonic residual is at most
`exp (-c * xOf Lw)` (section 7b), so the whole `Qpl` exception on the carrier costs the
maximal-Azuma price plus one explicit exponential at the paper's scale. -/
theorem measureReal_recordCarrier_qplDrop_exp_bound {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ {r s L n : ℕ} (eps : ℝ), 0 < eps → L₀ ≤ L → 1 ≤ n →
      n ≤ T * L → (T + 2) * L ≤ r → 1 ≤ cA r T L → ∀ (i j : Fin N) {KQ L34 : ℝ},
      0 < KQ → 0 < L34 →
        (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              LocOccQ.qplDrop (ProjLedger.Qpl p m eps i j) s n (KQ * L34)) ≤
          (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
              (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
                (4 * (n : ℝ) *
                  (QplPredEnv.envB p m (xOf (cLw T L))
                    (QplWindow.envC p m (xOf (cLw T L)))) ^ 2))) +
            Real.exp (-c * xOf (cLw T L)) := by
  obtain ⟨c, hc, L₀, hb⟩ := measureReal_carrier_harmDefect_le_exp (N := N) hp0 hp1 hm T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro r s L n eps hε hL hn hnTL hA0 hA1 i j KQ L34 hKQ hL34
  have hV1 : (1 : ℝ) ≤ xOf (cLw T L) := LocSumAct.one_le_xOf (one_le_cLw T L)
  have hsingle := measureReal_recordCarrier_qplDrop_singleResidual (N := N) hp0 hp1 m eps i j hε
    (r := r) (s := s) (T := T) (L := L) (n := n) hn hnTL hA0 hA1
    (V := xOf (cLw T L)) hV1 hKQ hL34
  have hharm := hb (r := r) (s := s) (L := L) (j := j) hL hA1
  linarith [hsingle, hharm]

/-- **Ledger plus `Qpl` at the record carrier, with no unnamed residual.**

The public `LocOccRecordCarrier.measureReal_recordCarrier_ledger_hQ_le` bounds the joint exception of
the step ledger (`LedgerShape`, at `eps = 1/8`) and of the `Qpl` drop by the Azuma price plus the two
carrier-weighted residuals.  At the paper's parameters the geometric residual is empty and the
harmonic one is `exp (-c * xOf Lw)`, so the joint exception of these two fields is bounded by

  `mu(carrier) * Azuma + exp (-c * Lw^{1/16})`.

This is a bound for the *two named fields* only; it is not a joint bound over all `(lococc)` fields. -/
theorem measureReal_recordCarrier_ledger_qpl_exp_bound {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ {r s L n : ℕ}, L₀ ≤ L → 1 ≤ n → n ≤ T * L →
      (T + 2) * L ≤ r → 1 ≤ cA r T L → ∀ {KQ L34 : ℝ}, 0 < KQ → 0 < L34 →
        (arrayMeasure N).real
            ((ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
                {U : Array N | ¬ LocOccRecordCarrier.LedgerShape p m i j U}) ∪
              (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
                LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s n (KQ * L34))) ≤
          (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
              (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
                (4 * (n : ℝ) *
                  (QplPredEnv.envB p m (xOf (cLw T L))
                    (QplWindow.envC p m (xOf (cLw T L)))) ^ 2))) +
            Real.exp (-c * xOf (cLw T L)) := by
  obtain ⟨c, hc, L₀, hb⟩ := measureReal_carrier_harmDefect_le_exp (N := N) hp0 hp1 hm T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro r s L n hL hn hnTL hA0 hA1 KQ L34 hKQ hL34
  have hV1 : (1 : ℝ) ≤ xOf (cLw T L) := LocSumAct.one_le_xOf (one_le_cLw T L)
  have hmain := LocOccRecordCarrier.measureReal_recordCarrier_ledger_hQ_le (N := N) hp0 hp1 hm hij
    (r := r) (s := s) (n := n) (L := L) hn hV1 (w := cA r T L) (M := cM T L) hA1 hKQ hL34
  have hzero := measureReal_carrier_inter_shiftedContDefect (N := N) (p := p) (m := m)
    (r := r) (s := s) (L := L) (T := T) (n := n) hA0 hnTL i j
  have hharm := hb (r := r) (s := s) (L := L) (j := j) hL hA1
  rw [hzero, zero_add] at hmain
  linarith [hmain, hharm]

/-! ### 8. The paper's hypotheses `(T+3)L ≤ r`, `1 ≤ T`, `1 ≤ L` suffice

The interface above takes `(T+2)L ≤ r` and `1 ≤ A`; both follow from the paper's own
`(T+3)L ≤ r` with `L ≥ 1`, so no extra hypothesis is introduced. -/

theorem cA_hyp_of_paper {r T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) :
    (T + 2) * L ≤ r ∧ 1 ≤ cA r T L := by
  have h1 : (T + 2) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
  have h2 : (T + 2) * L + 1 ≤ (T + 3) * L := by
    have h3 : (T + 3) * L = (T + 2) * L + L := by ring
    omega
  refine ⟨le_trans h1 hr, ?_⟩
  unfold cA
  omega

/-- **The `Qpl` estimate with one residual, under the paper's hypotheses.** -/
theorem measureReal_recordCarrier_qplDrop_singleResidual_paper {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N) (hε : 0 < eps)
    {r s T L n : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r)
    (hn : 1 ≤ n) (hnTL : n ≤ T * L) {V : ℝ} (hV1 : 1 ≤ V) {KQ L34 : ℝ}
    (hKQ : 0 < KQ) (hL34 : 0 < L34) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m eps i j) s n (KQ * L34)) ≤
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
            (4 * (n : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j V (cA r T L) (cM T L)) := by
  obtain ⟨hA0, hA1⟩ := cA_hyp_of_paper hT hL hr
  exact measureReal_recordCarrier_qplDrop_singleResidual (N := N) hp0 hp1 m eps i j hε hn hnTL
    hA0 hA1 hV1 hKQ hL34

/-- **The fully quantitative `Qpl` budget under the paper's hypotheses.**

For `1/2 < p < 1`, `m ≥ 2`, `T ≥ 1`, `L ≥ L₀` and `(T+3)L ≤ r`, the `Qpl` drop over the window
`[s, s + n]`, `n ≤ TL`, on the record carrier costs at most the carrier-weighted maximal-Azuma
price plus `exp (-c * Lw^{1/16})`.  There is no unnamed residual left in the `Qpl` field. -/
theorem measureReal_recordCarrier_qplDrop_exp_bound_paper {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ {r s L n : ℕ} (eps : ℝ), 0 < eps → L₀ ≤ L → 1 ≤ L →
      1 ≤ n → n ≤ T * L → (T + 3) * L ≤ r → ∀ (i j : Fin N) {KQ L34 : ℝ},
      0 < KQ → 0 < L34 →
        (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              LocOccQ.qplDrop (ProjLedger.Qpl p m eps i j) s n (KQ * L34)) ≤
          (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
              (2 * ((n : ℝ) + 1) * Real.exp (-((KQ * L34 / 2) ^ 2) /
                (4 * (n : ℝ) *
                  (QplPredEnv.envB p m (xOf (cLw T L))
                    (QplWindow.envC p m (xOf (cLw T L)))) ^ 2))) +
            Real.exp (-c * xOf (cLw T L)) := by
  obtain ⟨c, hc, L₀, hb⟩ := measureReal_recordCarrier_qplDrop_exp_bound (N := N) hp0 hp1 hm T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro r s L n eps hε hL hL1 hn hnTL hr i j KQ L34 hKQ hL34
  obtain ⟨hA0, hA1⟩ := cA_hyp_of_paper hT hL1 hr
  exact hb (r := r) (s := s) (L := L) (n := n) eps hε hL hn hnTL hA0 hA1 i j hKQ hL34

/-- **One event, three fields, under the paper's hypotheses.** -/
theorem carrier_single_event_good_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m r s L T n : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) (hn : n ≤ T * L)
    {i j : Fin N} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hH : U ∉ QplWindow.harmDefect p m j (xOf (cLw T L)) (cA r T L) (cM T L)) :
    U ∈ ShiftedQplResidual.shiftedQplWindow p m i j (xOf (cLw T L)) s (cA r T L) (cM T L) n ∧
      (∀ y ∈ Finset.Ico (cA r T L - 1) (cA r T L + cLw T L),
        hof p (siteMarks p m U j) y ≤ xOf (cLw T L)) ∧
      (∀ t : ℕ, s ≤ t → t ≤ s + T * L →
        bRec p m t j U / (1 - aRec p m) ≤
          (4 / (1 - aRec p m)) * LocOccCarrier.L34 L (cLw T L)) := by
  obtain ⟨hA0, hA1⟩ := cA_hyp_of_paper hT hL hr
  exact carrier_single_event_good (N := N) hp1 hp2 hA0 hA1 hn hU hH

/-! ### 9. Non-vacuity and the concrete arithmetic

The emptiness of the geometric residual is not an artefact of an empty carrier: at the level
`r = s = (T+2)L + 1` the carrier has strictly positive `arrayMeasure N`-measure (the accepted
all-rise cylinder) while its intersection with `shiftedContDefect` is empty. -/

/-- **The carrier is nonempty *and* misses the geometric residual.** -/
theorem carrier_pos_and_defect_empty (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (T L : ℕ) (hL : 1 ≤ L) :
    0 < arrayMeasure N
        (ActualRecordFiltration.recordPrefixBand (N := N) p m ((T + 2) * L + 1) ((T + 2) * L + 1)
          L) ∧
      ActualRecordFiltration.recordPrefixBand (N := N) p m ((T + 2) * L + 1) ((T + 2) * L + 1) L ∩
          ShiftedQplResidual.shiftedContDefect p m
            (Classical.arbitrary (Fin N)) (Classical.arbitrary (Fin N)) ((T + 2) * L + 1)
            (cA ((T + 2) * L + 1) T L) (cM T L) (T * L) = ∅ := by
  have hs : 1 ≤ (T + 2) * L + 1 := by omega
  refine ⟨LocOccRecordCarrier.recordPrefixBand_pos (N := N) p hp m _ L hs, ?_⟩
  refine carrier_inter_shiftedContDefect_eq_empty (p := p) (m := m) (r := (T + 2) * L + 1)
    (s := (T + 2) * L + 1) (L := L) (T := T) (n := T * L) (by omega) le_rfl _ _

/-- The paper's parameter identity, kernel-checked on a concrete instance:
`T = 2`, `L = 1`, `r = 10` give `A = 6`, `Lw = 7`, `M = 8` and `A + Lw = r + TL + 1 = 13`. -/
example : cA 10 2 1 = 6 ∧ cLw 2 1 = 7 ∧ cM 2 1 = 8 ∧ cA 10 2 1 + cLw 2 1 = 10 + 2 * 1 + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cA, cLw, cM]

end CarrierQplResidual
