/-
# The literal block estimate `(blkprob)`: `BadBlk ⊆ badEventLocal ∪ martClauseBadCTfin`

## What is proved here

`HblkFinal.record_tightness_of_two` (and hence the paper's Theorem 1.1) reduces to the two
array-side bad-block bounds `h₁` (`(time)` fails) and `h₂` (`(half)` fails), or, in the single
event form of `M4Term.PaperBadBlockProfile`, to one bound on

  `{U | HblkTwo.BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}`.

This file proves that bound **unconditionally** for every `N ≥ 2`, `m ≥ 2` and `1/2 < p < 1`,
at explicit constants.  The proof is a *set inclusion onto already measured events*:

  `BadBlk B C₀ T (arrQ p m U) r L  ⊆ᵐ  badEventLocal r T L ∪ martClauseBadCTfin T L r`,

for `L` above an explicit threshold and `r ≥ C₀ L`.  Both members of the union carry the paper's
own profile `C exp (-c L^{1/16})`:

* `WindowPosLocal.exists_badEventLocal_blockClauses` gives the block clauses
  `BlkCoin.BlockClauses` off `badEventLocal` (the minimal *local* finite-run event on
  `[Astar r T L, r + T·L + 1]`, measured with no `r` in the profile), and
* `M1DMart.martClauseBadCTfin_subset_locMartBad` gives the `(locmart)` clause off the measured
  `RecordClock.locMartBad` event.

Off those two events, on the record carrier, the paper's two block inequalities are *theorems*:

* `(time)`: `M3C.exists_L0_timeSharp` from the `(lococc)` clause `hBC.base.occ`;
* `(half)`: `M1C.half_from_clauses_sharp`, which needs no coalescence time and no local field,
  only `BlockClauses` + `MartClause` + `Numerics` + one vanishing allowance.

`HblkTwo.himpl_of_record` then turns `(time) ∧ (half)` into `GoodSeq`, i.e. into `¬ BadBlk`.
The two profiles are merged by `LocalGoodAll.exf_two` into `paperProfile (CT+1) (min cT cM)`.

## What is not used

No `UniformHalfClause`, no `KnotCoalesceAll`, no `FluidHalfDataAll`, no `PaperBlock.MoveCarrier`
(the windowed move carrier is *derived* from `¬ badEventLocal` and the local run event), no
stationary starting law, no coalescence event, no `2m < N`, no global prefix `RunsOK`, and no
assumption on `T` other than the paper's `(BTchoice)` order: `B` from the geometric bound, then
`T` above `8C(B+5)/3` and `64⌈C⌉`.
-/
import Swarm.RunLocal
import Swarm.HalvingCTfin
import Swarm.ClockSharpCTfin
import Swarm.M1Sharp
import Swarm.ProfileBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open SwarmRec SimJump SimJump.RecKernel SwarmRecordMeas.StartLaw

namespace M4Blk

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The vanishing allowance `ε_L = (C_T + 1) L^{-1/4}` -/

/-- The paper's vanishing allowance at the actual error coefficient: `η = ⌈C_T L^{3/4}⌉` obeys
`η ≤ ε_L L` with `ε_L = (C_T + 1) L^{-1/4} → 0`. -/
noncomputable def blkEps (p : ℝ) (m T : ℕ) (Cerr : ℝ) (L : ℕ) : ℝ :=
  (LocOccDerived.CTfin p m T Cerr + 1) * (L : ℝ) ^ (-(1 / 4) : ℝ)

/-- `ε_L → 0`. -/
theorem blkEps_tendsto (p : ℝ) (m T : ℕ) (Cerr : ℝ) :
    Tendsto (fun L : ℕ => blkEps p m T Cerr L) atTop (𝓝 0) := by
  have h := M1C.tendsto_rpow_neg_quarter (scale := fun L : ℕ => L) tendsto_id
    (LocOccDerived.CTfin p m T Cerr + 1)
  simpa only [blkEps] using h

/-- The allowance dominates the integer `η = ⌈C_T L^{3/4}⌉`. -/
theorem blkEps_spec {p : ℝ} {m T : ℕ} {Cerr : ℝ} {L : ℕ} (hL : 1 ≤ L) :
    ((⌈LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
      ≤ blkEps p m T Cerr L * (L : ℝ) := by
  set CT : ℝ := LocOccDerived.CTfin p m T Cerr with hCTdef
  have hCT0 : 0 ≤ CT := (LocOccDerived.CTfin_pos p m T Cerr).le
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hpow1 : (1 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have hrpow : (L : ℝ) ^ (-(1 / 4) : ℝ) * (L : ℝ) = (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h1 : (L : ℝ) ^ (-(1 / 4) + 1 : ℝ)
        = (L : ℝ) ^ (-(1 / 4) : ℝ) * (L : ℝ) ^ (1 : ℝ) := Real.rpow_add hLpos _ _
    rw [Real.rpow_one] at h1
    have h2 : (-(1 / 4) + 1 : ℝ) = 3 / 4 := by norm_num
    rw [h2] at h1
    exact h1.symm
  have hmul : blkEps p m T Cerr L * (L : ℝ) = (CT + 1) * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [blkEps, hCTdef, mul_assoc, hrpow]
  have hceil : ((⌈CT * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
      ≤ CT * (L : ℝ) ^ ((3 : ℝ) / 4) + 1 := by
    have h := Nat.ceil_lt_add_one (a := CT * (L : ℝ) ^ ((3 : ℝ) / 4))
      (mul_nonneg hCT0 (Real.rpow_nonneg hLpos.le _))
    linarith
  have hkey : CT * (L : ℝ) ^ ((3 : ℝ) / 4) + 1 ≤ (CT + 1) * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    nlinarith [hpow1, hCT0]
  rw [hmul]
  linarith

/-! ## 2. The inclusion of the literal bad block event in two measured events -/

/-- **`BadBlk` is contained in `badEventLocal ∪ martClauseBadCTfin`.**

The three analytic inputs are exactly the *outputs* of the public theorems at the same constants
`C = Cfin`, `CT = CTfin p m T Cerr`:

* `hblk` — the paper's block clauses off `badEventLocal`
  (`WindowPosLocal.exists_badEventLocal_blockClauses`);
* `htime` — `(time)` from `(lococc)` off the record carrier (`M3C.exists_L0_timeSharp`);
* `hhalf` — `(half)` from the clauses and the numerics (`M1C.half_from_clauses_sharp`), stated
  in its own `∀`-form so that no coalescence time is needed;
* `hnum` — `Numerics` for all large `L` (`M1DNum.exists_halving_thresholds`).

Everything else is logic: `HblkTwo.himpl_of_record` turns the two block inequalities into
`GoodSeq` and hence rules out `BadBlk`. -/
theorem badBlk_ae_subset {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) {Cerr : ℝ} {T : ℕ} {B C₀ : ℕ} (hC₀g : B + T + 1 ≤ C₀) (hC₀t : T + 3 ≤ C₀)
    {Lb Lt Lh Ln : ℕ}
    (hblk : ∀ (L : ℕ), Lb ≤ L → ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Uniform.Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ WindowPosLocal.badEventLocal (N := N) p m Cerr r T L →
      BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (PaperBlock.Hc p m U)
        (PaperBlock.Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r)
    (htime : ∀ (L : ℕ), Lt ≤ L → ∀ r : ℕ,
      ∀ U ∈ RecClockLG.recordCarrier (N := N) p m r L,
      LocalFluid.LocOcc (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (PaperBlock.Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r →
      PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L)
    (hhalf : ∀ (L : ℕ), Lh ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
      ∀ (X : Fin N → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset (Fin N) → ℕ → ℤ → ℤ)
        (A : Fin N → ℕ → ℕ) (η : ℕ),
      RecordDefect.IsRecord X τ → (∀ (i : Fin N) (n : ℕ), |X i (n + 1) - X i n| = 1) →
      RecordDefect.defect X τ r ≤ (L : ℤ) → τ (r + B * L) - τ r ≤ T * L →
      BlkCoin.BlockClauses X τ H (PaperBlock.Cfin (N := N) p m)
        (LocOccDerived.CTfin p m T Cerr) T L r →
      JoinStep.MartClause X τ A (2 * p - 1) (LocOccDerived.CTfin p m T Cerr) T L r →
      1 ≤ L → JoinStep.Numerics (PaperBlock.Cfin (N := N) p m)
        (LocOccDerived.CTfin p m T Cerr) L →
      LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) →
      (η : ℝ) ≤ blkEps p m T Cerr L * (L : ℝ) →
      2 * RecordDefect.defect X τ (r + B * L) ≤ (L : ℤ))
    (hnum : ∀ (L : ℕ), Ln ≤ L → JoinStep.Numerics (PaperBlock.Cfin (N := N) p m)
      (LocOccDerived.CTfin p m T Cerr) L)
    {L r : ℕ} (hL1 : 1 ≤ L) (hLb : Lb ≤ L) (hLt : Lt ≤ L) (hLh : Lh ≤ L) (hLn : Ln ≤ L)
    (hr : C₀ * L ≤ r) :
    {U : Uniform.Array N | HblkTwo.BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}
      ≤ᵐ[arrayMeasure N]
      (Set.union (WindowPosLocal.badEventLocal (N := N) p m Cerr r T L)
        (M1DMart.martClauseBadCTfin (N := N) p m T L r Cerr)) := by
  filter_upwards [M4D.ae_reach (N := N) hp0 hp1 hm hN] with U hreach hbad
  by_contra hcon
  have hnotLocal : U ∉ WindowPosLocal.badEventLocal (N := N) p m Cerr r T L :=
    fun h => hcon (Or.inl h)
  have hnotMart : U ∉ M1DMart.martClauseBadCTfin (N := N) p m T L r Cerr :=
    fun h => hcon (Or.inr h)
  have hMart : JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (fun i n => excitedSteps p m U n i) (2 * p - 1)
      (LocOccDerived.CTfin p m T Cerr) T L r := Classical.not_not.mp hnotMart
  -- `BadBlk`'s defect bound is exactly the record carrier
  have hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L :=
    ⟨hreach, by
      simpa only [HblkFinal.arrQ, RecordDefect.defect, Set.mem_ofPred_eq] using hbad.1⟩
  have hdr : RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ) := by
    rw [M4D.Xa_eq_actX, M4D.tauA_eq]
    exact LocCoordGeomCarrier.defect_le_of_carrier (N := N) hcarr
  have hrTL : (T + 3) * L ≤ r := le_trans (Nat.mul_le_mul_right L hC₀t) hr
  have hbc := hblk L hLb r hrTL U hcarr hnotLocal
  -- the paper's `(time)`
  have htim : PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L :=
    htime L hLt r U hcarr hbc.base.occ
  have htimZ : PaperBlock.tauA p m U (r + B * L) - PaperBlock.tauA p m U r ≤ T * L := by omega
  -- the paper's `(half)`
  have hhalfL : 2 * RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (r + B * L) ≤ (L : ℤ) :=
    hhalf L hLh r hr (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (PaperBlock.Hc p m U)
      (fun i n => excitedSteps p m U n i)
      ⌈LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ (3 / 4 : ℝ)⌉₊
      (M1D.isRecord_Xa hcarr) (PaperBlock.Xa_step p m U) hdr htimZ hbc hMart hL1
      (hnum L hLn) (Nat.le_ceil _) (blkEps_spec hL1)
  -- `(time)` is not violated
  have htimeNot : ¬ HblkTwo.BadTime B T (HblkFinal.arrQ p m U) r L := by
    rintro ⟨-, hlt⟩
    have htimE : recTimeA p m U (r + B * L) ≤ recTimeA p m U r + T * L := by
      have h := htim
      rw [M4D.tauA_eq] at h
      exact h
    simp only [HblkFinal.arrQ] at hlt
    omega
  -- `(half)` is not violated
  have hhalfNot : ¬ HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r L := by
    rintro ⟨-, hlt⟩
    have hnn : 0 ≤ RecordDefect.defect (actX p m U) (recTimeA p m U) (r + B * L) := by
      have h := RecordDefect.defect_nonneg (M1D.isRecord_Xa (p := p) (m := m) hcarr) (r + B * L)
      rwa [M4D.Xa_eq_actX, M4D.tauA_eq] at h
    have h2 : (2 : ℤ) * (RecordDefect.defect (actX p m U) (recTimeA p m U) (r + B * L)).toNat
        ≤ (L : ℤ) := by
      have hcast : ((RecordDefect.defect (actX p m U) (recTimeA p m U) (r + B * L)).toNat : ℤ)
          = RecordDefect.defect (actX p m U) (recTimeA p m U) (r + B * L) :=
        Int.toNat_of_nonneg hnn
      rw [hcast]
      have h := hhalfL
      rwa [M4D.Xa_eq_actX, M4D.tauA_eq] at h
    have hle : (RecordDefect.defect (actX p m U) (recTimeA p m U) (r + B * L)).toNat ≤ L / 2 := by
      have h2' : 2 * (RecordDefect.defect (actX p m U) (recTimeA p m U) (r + B * L)).toNat
          ≤ L := by omega
      refine (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr ?_
      omega
    simp only [HblkFinal.arrQ] at hlt
    exact absurd hle (not_le.mpr hlt)
  -- the two block inequalities give `GoodSeq`
  have hdrNat : (fun u : ℕ =>
      (RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) u).toNat) r ≤ L := by
    simpa only [M4D.Xa_eq_actX, M4D.tauA_eq, HblkFinal.arrQ] using hbad.1
  have hdouble : (fun u : ℕ =>
      (RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) u).toNat)
      (r + B * L) ≤ L / 2 := by
    have hnn : 0 ≤ RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) :=
      RecordDefect.defect_nonneg (M1D.isRecord_Xa (p := p) (m := m) hcarr) (r + B * L)
    have hcast : ((RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (r + B * L)).toNat : ℤ)
        = RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) :=
      Int.toNat_of_nonneg hnn
    have h2 : 2 * (RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (r + B * L)).toNat ≤ L := by omega
    have hkey : (RecordDefect.defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (r + B * L)).toNat ≤ L / 2 := by
      refine (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr ?_
      omega
    exact hkey
  have hgood : SwarmM4C.LawBridge.GoodSeq B C₀ T (HblkFinal.arrQ p m U).1
      (HblkFinal.arrQ p m U).2 r L := by
    have h := HblkTwo.himpl_of_record (X := PaperBlock.Xa p m U) (τ := PaperBlock.tauA p m U)
      (M1D.isRecord_Xa (p := p) (m := m) hcarr) (PaperBlock.Xa_step p m U) hC₀g
      hdrNat htim hdouble
    simpa only [HblkFinal.arrQ, M4D.Xa_eq_actX, M4D.tauA_eq] using h
  exact absurd hgood hbad.2

/-! ## 3. The literal `(blkprob)` at explicit constants -/

/-- **The paper's block estimate `(blkprob)` for the actual array, unconditionally.**

For every `N ≥ 2`, `m ≥ 2` and `1/2 < p < 1` there are explicit integers `B ≥ 1`, `T`, `C₀` and
constants `C_T ≥ 0`, `c_T > 0`, `L₀` such that for every `L ≥ max 1 L₀` and every record level
`r ≥ C₀ L` the literal bad block event of `HblkFinal.arrQ` has `arrayMeasure N`-probability at
most `C_T exp (-c_T L^{1/16})`.

The constants, at `C = Cfin` and `CT = CTfin`:

* `B = ⌈(1 + 64⌈C⌉)(1 + 2C²)^{N-1}⌉₊ + 2` (the paper's `B`-first choice, meeting
  `D(1+b)^{card-1} - 1 < B - 2` with `b = 2C²`);
* `T = max (64⌈C⌉) ⌈8C(B+5)/3⌉₊ + 1` (above the paper's `(BTchoice)` `8C(B+5)/3`);
* `C₀ = B + T + 3`;
* `C_T = CTfin + 1`, `c_T = min cT cM`. -/
theorem paperBadBlockProfile (p : ℝ) (m : ℕ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) : M4Term.PaperBadBlockProfile p m := by
  intro N inst hN
  letI : Nonempty (Fin N) := inst
  -- the actual constants
  set C : ℝ := PaperBlock.Cfin (N := N) p m with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; exact PaperBlock.one_le_Cfin (N := N) p m
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  set H : ℝ := (1 + 64 * ((⌈C⌉₊ : ℕ) : ℝ)) * (1 + 2 * C ^ 2) ^ (N - 1) with hHdef
  set B : ℕ := ⌈H⌉₊ + 2 with hBdef
  set M : ℕ := max (64 * ⌈C⌉₊) (⌈8 * C * ((B : ℝ) + 5) / 3⌉₊) with hMdef
  set T : ℕ := M + 1 with hTdef
  set C₀ : ℕ := B + T + 3 with hC₀def
  have hB1 : 1 ≤ B := by omega
  have hbt1 : B + T + 1 ≤ C₀ := by omega
  have hbt3 : T + 3 ≤ C₀ := by omega
  have hT1 : 1 ≤ T := by omega
  -- the paper's `B`-first margin, in the `2C²` form of `M1C.half_from_clauses_sharp`
  have hbb : (1 + 64 * ((⌈C⌉₊ : ℕ) : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card (Fin N) - 1) - 1
      < (B : ℝ) - 2 := by
    rw [Fintype.card_fin]
    have hBcast : (B : ℝ) - 2 = ((⌈H⌉₊ : ℕ) : ℝ) := by
      rw [hBdef]; push_cast; ring
    rw [hBcast]
    linarith [Nat.le_ceil H]
  have hB1R : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
  -- `T` above `B - 2`
  have hBT : (B : ℝ) - 2 < (T : ℝ) := by
    have hM1 : ⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ ≤ M := by
      rw [hMdef]; exact Nat.le_max_right _ _
    have hTL : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ) := by
      have h1 : 8 * C * ((B : ℝ) + 5) / 3 ≤ ((⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      have h2 : ((⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      have h3 : (M : ℝ) < (T : ℝ) := by rw [hTdef]; push_cast; linarith
      linarith
    have hB5 : (0 : ℝ) < (B : ℝ) + 5 := by linarith
    nlinarith [hTL, hC1, hB1R]
  -- the paper's `(BTchoice)` and `64⌈C⌉ ≤ T`
  have hTL : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ) := by
    have hM1 : ⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ ≤ M := by
      rw [hMdef]; exact Nat.le_max_right _ _
    have h1 : 8 * C * ((B : ℝ) + 5) / 3 ≤ ((⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    have h3 : (M : ℝ) < (T : ℝ) := by rw [hTdef]; push_cast; linarith
    linarith
  have hT64 : 64 * ⌈C⌉₊ ≤ T := by
    have hM2 : 64 * ⌈C⌉₊ ≤ M := by rw [hMdef]; exact Nat.le_max_left _ _
    omega
  -- the three measured / analytic inputs at the same `Cerr`, `T`
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, Lb, hmeas, hblk⟩ :=
    WindowPosLocal.exists_badEventLocal_blockClauses (N := N) hp0 hp1 hm hN (T := T) hT1
  obtain ⟨cM, hcM, Lm, hmart⟩ :=
    M1DMart.exists_martClauseBadCTfin_le (N := N) hp0 hp1 hm hN T hT1 Cerr
  obtain ⟨Lt, -, htime⟩ :=
    M3C.exists_L0_timeSharp (N := N) (p := p) (m := m) (C := C)
      (CT := LocOccDerived.CTfin p m T Cerr) (B := B) (T := T) hN hCpos hB1 hTL
  obtain ⟨Lh, hhalfL⟩ :=
    M1C.half_from_clauses_sharp (ι := Fin N) C₀ B T (by positivity) (by positivity) hC1
      (LocOccDerived.CTfin_pos p m T Cerr).le hT64 hbt3 hbb hBT (by simpa using hN)
      (2 * p - 1) (blkEps_tendsto p m T Cerr)
  obtain ⟨Ln, hLn⟩ :=
    M1DNum.exists_halving_thresholds (C := C) (CT := LocOccDerived.CTfin p m T Cerr) hCpos
      (Finset.univ : Finset (Fin N)).card
  have hnumF : ∀ (L : ℕ), Ln ≤ L →
      JoinStep.Numerics (PaperBlock.Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) L := by
    intro L hL
    have h := (hLn L hL).1
    rwa [hCdef] at h
  refine ⟨B, T, C₀, hB1, CT + 1, min cT cM,
    max (max (max Lb Lt) (max Lh Ln)) (max Lm 1), by linarith, lt_min hcT hcM, ?_⟩
  intro L hL1 hL r hr
  have hLall := hL
  simp only [Nat.max_le] at hLall
  obtain ⟨⟨⟨hLb, hLt⟩, ⟨hLh, hLn'⟩⟩, ⟨hLm, hL1'⟩⟩ := hLall
  have hrTL : (T + 3) * L ≤ r := le_trans (Nat.mul_le_mul_right L hbt3) hr
  -- the inclusion
  have hsub := badBlk_ae_subset (N := N) hp0 hp1 hm hN hbt1 hbt3 hblk htime hhalfL hnumF
    hL1 hLb hLt hLh hLn' hr
  -- the two profiles
  have hm1 : (arrayMeasure N) (WindowPosLocal.badEventLocal (N := N) p m Cerr r T L)
      ≤ ENNReal.ofReal (CT * LocalGoodAll.exf cT L) :=
    M4D.measure_le_ofReal_of_measureReal_le M4D.arrayMeasure_ne_top (hmeas L hLb r hrTL)
  have hm2 : (arrayMeasure N) (M1DMart.martClauseBadCTfin (N := N) p m T L r Cerr)
      ≤ ENNReal.ofReal (1 * LocalGoodAll.exf cM L) := by
    refine M4D.measure_le_ofReal_of_measureReal_le M4D.arrayMeasure_ne_top ?_
    have h := hmart L hLm r
    have hxOf : LocSumAct.xOf L = RecordClock.xOf L := by
      simp only [LocSumAct.xOf, RecordClock.xOf]
    have hx : Real.exp (-cM * RecordClock.xOf L) = LocalGoodAll.exf cM L := by
      rw [LocalGoodAll.exf, hxOf, neg_mul]
    rw [hx] at h
    simpa using h
  calc (arrayMeasure N)
        {U : Uniform.Array N | HblkTwo.BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}
      ≤ (arrayMeasure N)
          (Set.union (WindowPosLocal.badEventLocal (N := N) p m Cerr r T L)
            (M1DMart.martClauseBadCTfin (N := N) p m T L r Cerr)) := measure_mono_ae hsub
    _ ≤ (arrayMeasure N) (WindowPosLocal.badEventLocal (N := N) p m Cerr r T L)
          + (arrayMeasure N) (M1DMart.martClauseBadCTfin (N := N) p m T L r Cerr) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (CT * LocalGoodAll.exf cT L)
          + ENNReal.ofReal (1 * LocalGoodAll.exf cM L) := add_le_add hm1 hm2
    _ = ENNReal.ofReal (CT * LocalGoodAll.exf cT L + 1 * LocalGoodAll.exf cM L) := by
        rw [ENNReal.ofReal_add]
        · exact mul_nonneg hCT.le (le_of_lt (by unfold LocalGoodAll.exf; exact Real.exp_pos _))
        · exact mul_nonneg (by norm_num) (le_of_lt (by unfold LocalGoodAll.exf; exact Real.exp_pos _))
    _ ≤ ENNReal.ofReal ((CT + 1) * LocalGoodAll.exf (min cT cM) L) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h := LocalGoodAll.exf_two (C₁ := CT) (C₂ := 1) (c₁ := cT) (c₂ := cM)
          hCT.le (by norm_num) hcT hcM L
        linarith
    _ = TightAvail.paperProfile (CT + 1) (min cT cM) L :=
        (M4D.paperProfile_eq_exf (CT + 1) (min cT cM) L).symm

/-! ## 4. The literal target -/

/-- **Theorem 1.1 for the literal array, unconditionally.**

There is `κ > 0` (chosen before `N`) such that for every `N ≥ 2` one deterministic speed
`v ∈ [κ, 2p-1]` is such that almost every walker on `Swarming.Uniform.arrayMeasure N` has
`trajectory.pos i (n)/n → v`.  This is
`M4Term.main_claim_of_paper_badblock_profile` applied to the profile proved above. -/
theorem main_claim (p : ℝ) (m : ℕ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) :=
  M4Term.main_claim_of_paper_badblock_profile hp0 hp1 hm (paperBadBlockProfile p m hp0 hp1 hm)


/-! ## 5. The `d_T` closure, and the second (direct) route to the main claim -/

/-- **The `d_T` tightness consequence of the proved profile.**

At the *actual* zero-state Dirac start of the stopped-record path law, and for every `N ≥ 2`,
the record defect `dT` is tight.  This is
`SourceTightAvail.record_tightness_of_block_clauses_at` fed with the two clauses extracted from
`paperBadBlockProfile` by `M4Term.cubicBlockClauses_of_paper` (which converts the paper's single
bad block event into `AdvanceClauseAt`/`HalfClauseAt` and absorbs the `L₀` threshold into the
cubic majorant), with the engine's own `T = max T₀ (⌈2B/κ⌉₊+2)` and `C = max C₀ (B+T+1)` supplied
by monotonicity. -/
theorem dT_tight (p : ℝ) (m : ℕ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) :
    ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε := by
  intro N inst hN ε hε
  letI : Nonempty (Fin N) := inst
  obtain ⟨B, T₀, C₀, hB, K₁, K₂, hK₁, hK₂, h₁, h₂⟩ :=
    M4Term.cubicBlockClauses_of_paper (paperBadBlockProfile p m hp0 hp1 hm) N hN
  obtain ⟨κ, hκ, H⟩ :=
    SourceTightAvail.record_tightness_of_block_clauses_at (N := N) (m := m) hp0 hp1 hm hN B hB
  let T : ℕ := max T₀ (⌈2 * (B : ℝ) / κ⌉₊ + 2)
  let C : ℕ := max C₀ (B + T + 1)
  have hT : ⌈2 * (B : ℝ) / κ⌉₊ + 2 ≤ T := le_max_right _ _
  have hTB : T₀ ≤ T := le_max_left _ _
  have hC : B + T + 1 ≤ C := le_max_right _ _
  have hCC : C₀ ≤ C := le_max_left _ _
  have h₁' : SourceTightAvail.AdvanceClauseAt (N := N) p m B T C (M4Term.cubicProfile K₁) :=
    M3Advance.advanceClauseAt_mono_C₀ hCC (M4Term.advanceClauseAt_mono_T (N := N) hTB h₁)
  have h₂' : SourceTightAvail.HalfClauseAt (N := N) p m B C (M4Term.cubicProfile K₂) :=
    M3Advance.halfClauseAt_mono_C₀ hCC h₂
  exact H T C hT hC _ _ K₁ K₂ hK₁ hK₂ (fun ℓ => le_rfl) (fun ℓ => le_rfl) h₁' h₂' ε hε

/-- **The literal target, second route.**

`SwarmDTR.main_claim_of_dT_tight` applied to `dT_tight`: the same statement as `main_claim`,
reached without passing through `M4Term.main_claim_of_paper_badblock_profile`.  The two proofs
therefore cross-check the whole downstream chain. -/
theorem main_claim_direct (p : ℝ) (m : ℕ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) :=
  SwarmDTR.main_claim_of_dT_tight hp0 hp1 hm (dT_tight p m hp0 hp1 hm)

end M4Blk
