/-
# The paper's `(time)` clause, at the paper's own `(BTchoice)` schedule

## The defect this file repairs

`Swarm/BlockAssembly.lean` states the paper's first block inequality (the display `(time)`
of the proof of Proposition `tight`)

  `PaperTimeClause` : `tau (r + B*L) - tau r <= T*L`

with the schedule constraints

  `64 * Cfin <= T`,  `(1+64Cfin)(1+b)^(N-1) - 1 < T - 3`,  `B + T + 3 <= C0`,
  `(1+64Cfin)(1+b)^(N-1) - 1 < B - 2`,  `B - 2 < T`.

The paper's `(BTchoice)` is instead

  `B > (1+64C)(1+b)^N + 2`,  `T > max { 4B/kappa(m,p), 8C(B+5)/3 }`,  `C0 > B + T + 3`.

The two differ in *order and size*: the paper chooses `B` first, from the geometric bound, and
then `T` **much larger** than `B` (`T > 8C(B+5)/3`).  `BlockAssembly` chooses `T` first
(`exists_schedule_T`) and only asks `B < T + 2`.  That is not a cosmetic difference.  The only
finite-`L` route to `(time)` from the paper's `(lococc)` is the paper's `(Rlower)`

  `R(u) >= 3u/(8C) - 3`,

i.e. the record advances at per-unit-time rate `3/(8C)`, and `T > 8C(B+5)/3` is exactly
`3T/(8C) - 3 - B > 2 > 0`, the condition that rate `3/(8C)` exceeds the needed rate `B/T`.  With
`C = Cfin >= 1` (`PaperBlock.one_le_Cfin`) and `B = T + 1` the rate `3T/(8Cfin)` is at most
`3T/8 < B`, so the `(Rlower)` route cannot possibly yield `(time)` for a `T` chosen as in
`exists_schedule_T`.  This file

* `not_sharpSchedule_of_T_le` : proves the obstruction — if `T <= G + 7` (which is the size of
  the `T` produced by `exists_schedule_T`, whose definition is `⌈max (64 Cfin) (G+5)⌉₊ + 1` and
  whose `G = (1+64Cfin)(1+b)^(N-1)` is at least `1 + 64Cfin >= 65`) then **no** admissible `B`
  (`G - 1 < B - 2`) satisfies the paper's `T > 8C(B+5)/3`.  So the `T`-first order must be
  replaced by the paper's `B`-first order;
* `exists_rpow_quarter_ge` : the Archimedean fact supplying the `L0` threshold;
* `blt_of_sharpSchedule` : `B - 2 < T` follows from the paper's `T > 8C(B+5)/3` at `C >= 1`,
  `B >= 1`, so the sharp schedule is a *strengthening* of the old conjunct and the geometric
  part of the assembly is untouched;
* `timeSharp_carrier` : **the `(time)` clause proved**, on `recordCarrier`, from
  `(lococc)` alone, at the paper's schedule.  This is `LocalFluid.tau_advance_of_locOcc`
  (the finite-`L` `(Rlower)`) fed with the `L0` threshold above;
* `timeSharp_block` : the same at `BlkCoin.BlockClauses`, i.e. with `hocc` read off
  `.base.occ` — the only clause of `BlockClauses` that `(time)` uses;
* `PaperTimeClauseSharp` / `paperTimeClauseSharp` : the `M4D.PaperTimeClause` shape with the
  paper's schedule, **proved unconditionally**;
* `exists_schedule_BT` : the paper-order witness `B` then `T`, so the sharp statement is
  non-vacuous at every `b >= 0`, `N >= 2`.

## Exact boundary

No probability, no measure, no coalescence, no stationarity.  `(time)` is a deterministic
consequence of `(lococc)`, exactly as in the paper.  `(half)` and `(diam)` are not touched, and
no velocity or `MainClaim` claim is made.  `CTfin = max CTtot CTocc` does not appear: the clock
step reads only `C` and `CT`, so it is valid at any `CT` the caller passes (in particular at
`PaperBlock.CTtot` or at `LocOccDerived`'s `CTfin`).
-/
import Swarm.PaperBlock
import Swarm.LocalFluidAdvance
import Swarm.LocCoordGeomCarrier

open Finset
open scoped BigOperators

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M3C

open RecordDefect RecordoSupply

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The `L^(1/4)` threshold is eventually met -/

/-- **The Archimedean threshold.**  For `d > 0` and any `x` there is `L0` with
`x <= d * L^(1/4)` for all `L >= L0`.  This is exactly the passage from the paper's
`L^{-1/4}` loss in `(Rlower)` to its stated form: the paper says "for all sufficiently large
`L`", and this is that quantifier. -/
theorem exists_rpow_quarter_ge {d x : ℝ} (hd : 0 < d) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → x ≤ d * (L : ℝ) ^ ((1 : ℝ) / 4) := by
  have htend : Filter.Tendsto (fun L : ℕ => (L : ℝ) ^ ((1 : ℝ) / 4)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop (x / d))
  refine ⟨L₀, fun L hL => ?_⟩
  have h1 : x / d ≤ (L : ℝ) ^ ((1 : ℝ) / 4) := hL₀ L hL
  have h2 : x / d * d ≤ (L : ℝ) ^ ((1 : ℝ) / 4) * d :=
    mul_le_mul_of_nonneg_right h1 hd.le
  rw [div_mul_cancel₀ x hd.ne'] at h2
  linarith

/-! ## 2. The paper's `T > 8C(B+5)/3` implies the old conjunct `B - 2 < T` -/

/-- **`B - 2 < T` from the paper's `(BTchoice)` bound `T > 8C(B+5)/3`.**  At `C >= 1` and
`B >= 1`, `B - 2 < 8(B+5)/3 <= 8C(B+5)/3 < T`.  So replacing the old conjunct `B - 2 < T` by
the paper's `8C(B+5)/3 < T` is a strengthening of the schedule, and every downstream use of
`B - 2 < T` survives unchanged. -/
theorem blt_of_sharpSchedule {B T C : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (h : 8 * C * (B + 5) / 3 < T) : B - 2 < T := by
  have hB5 : (0 : ℝ) ≤ B + 5 := by linarith
  have h1 : B - 2 < 8 * (B + 5) / 3 := by linarith
  have h2 : 8 * (B + 5) / 3 ≤ 8 * C * (B + 5) / 3 := by
    have : 8 * (B + 5) / 3 ≤ 8 * (C * (B + 5)) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    calc 8 * (B + 5) / 3 = 8 * (B + 5) / 3 := rfl
      _ ≤ 8 * (C * (B + 5)) / 3 := this
      _ = 8 * C * (B + 5) / 3 := by ring
  linarith

/-! ## 3. The obstruction: a `T` of size `G + 7` admits no `B` at the paper's schedule -/

/-- **The `T`-first order is not merely inconvenient: it is incompatible with `(Rlower)`.**

Let `G = (1+64Cfin)(1+b)^(N-1) >= 0` be the geometric bound (so an admissible `B` satisfies
`G - 1 < B - 2`).  If `T <= G + 7` then **no** admissible `B` satisfies the paper's
`8C(B+5)/3 < T` at any `C >= 1`.  Indeed `B > G + 1` forces `8C(B+5)/3 >= 8(G+6)/3 >= G + 7`.

The `T` constructed by `BlockAssembly.exists_schedule_T` is `⌈max (64 Cfin) (G+5)⌉₊ + 1`,
which is `<= G + 7` because `G >= 1 + 64 Cfin` makes the `G + 5` branch dominate.  So that `T`
cannot be used by any proof that starts from `(lococc)`; the paper's order (fix `B` from the
geometric bound, then take `T` above `8C(B+5)/3`) is forced. -/
theorem not_sharpSchedule_of_T_le {C G B T : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hB : 1 ≤ B)
    (hBG : G - 1 < B - 2) (hT : T ≤ G + 7) : ¬ (8 * C * (B + 5) / 3 < T) := by
  intro h
  have hB5 : (0 : ℝ) ≤ B + 5 := by linarith
  have h1 : B + 5 > G + 6 := by linarith
  have h2 : 8 * C * (B + 5) / 3 ≥ 8 * (B + 5) / 3 := by
    have h3 : (8 : ℝ) * (B + 5) / 3 ≤ 8 * C * (B + 5) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    linarith
  have h4 : 8 * (B + 5) / 3 > G + 7 := by linarith
  linarith

/-- `exists_schedule_T`'s `T` really has size at most `G + 7` when `G = (1+64Cfin)(1+b)^(N-1)`
and `64Cfin <= G` (which holds with room to spare: `G >= 1 + 64Cfin`).  Then the `G + 5`
branch of the `max` dominates `64Cfin`, and `Nat.ceil_lt_add_one` gives
`T = ⌈m⌉₊ + 1 < m + 2 <= G + 7`. -/
theorem scheduleT_le_of_geometric {C G : ℝ} (hCG : 64 * C ≤ G) (hG : 0 ≤ G) :
    ((⌈max (64 * C) (G + 5)⌉₊ : ℝ) + 1) ≤ G + 7 := by
  have hm : max (64 * C) (G + 5) = G + 5 := max_eq_right (by linarith)
  rw [hm]
  have h0 : (0 : ℝ) ≤ G + 5 := by linarith
  have hc := Nat.ceil_lt_add_one h0
  linarith

/-! ## 4. `(time)` at the paper's schedule, from `(lococc)` -/

/-- **The record clock advances `B L` levels within `T L` steps**, on the record carrier, from
`(lococc)` alone, at the paper's `(BTchoice)` bound `T > 8C(B+5)/3`.

This is the paper's display `(time)`.  Its proof in the paper is `(Rlower)`
(`R(u) >= 3u/(8C) - 3`, itself the limit of `(lococc)`), which for `u = T` exceeds `B + 2`
by `(BTchoice)`.  `LocalFluid.tau_advance_of_locOcc` is the finite-`L` form of exactly that
argument; the only thing it leaves open is the paper's "for all sufficiently large `L`",
which is the explicit `L0` returned here. -/
theorem exists_L0_timeSharp {p : ℝ} {m : ℕ} {C CT : ℝ} {B T : ℕ} (hN : 2 ≤ N)
    (hC : 0 < C) (hB : 1 ≤ B) (hTL : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ)) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ,
      ∀ U : Swarming.Uniform.Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        LocalFluid.LocOcc (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) C CT T L r →
        PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L := by
  have h8C : (0 : ℝ) < 8 * C := by linarith
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  -- `(Rlower)` rate exceeds the needed rate `B/T`
  have hrate : (B : ℝ) + 5 < 3 * (T : ℝ) / (8 * C) := by
    rw [lt_div_iff₀ h8C]
    nlinarith [hTL]
  have hd : 0 < 3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ) := by linarith
  obtain ⟨L₁, hL₁⟩ := exists_rpow_quarter_ge (d := 3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ))
    (x := CT / C) hd
  refine ⟨max L₁ 1, le_max_right _ _, ?_⟩
  intro L hL r U hcarr hocc
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLge : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hnum : (3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 4) ≥ CT / C :=
    hL₁ L hL1
  -- two distinct indices exist because `N >= 2`
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  exact LocalFluid.tau_advance_of_locOcc (PaperBlock.Xa p m U)
    (LocCoordGeomCarrier.isRecord_recTimeA_of_carrier hcarr)
    (fun i n => PaperBlock.Xa_step p m U i n)
    (fun i => RecordoSupply.actX_zero p m U i)
    hC hocc (LocCoordGeomCarrier.defect_le_of_carrier hcarr) hLge h01 hnum

/-- **`(time)` from `BlkCoin.BlockClauses`.**  `(time)` uses exactly one clause of
`BlockClauses`, namely `(lococc)` (`.base.occ`); `(loccoord)`, `(locmove)`, `(locgroup)` and the
potential axioms are not read.  So the clause holds at `CTfin`, at `CTtot`, or at any other
error coefficient the caller passes, and in particular the `CTfin` change of
`LocOccDerived` is immaterial to it. -/
theorem timeSharp_of_blockClauses {p : ℝ} {m : ℕ} {C CT : ℝ} {B T : ℕ} {r L : ℕ} (hN : 2 ≤ N)
    (hC : 0 < C) (hB : 1 ≤ B) (hTL : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ))
    (hL : Classical.choose (exists_L0_timeSharp (N := N) (p := p) (m := m)
      (C := C) (CT := CT) (B := B) (T := T) hN hC hB hTL) ≤ L)
    {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hBC : BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (PaperBlock.Hc p m U) C CT T L r) :
    PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L :=
  (Classical.choose_spec (exists_L0_timeSharp (N := N) (p := p) (m := m)
    (C := C) (CT := CT) (B := B) (T := T) hN hC hB hTL)).2 L hL r U hcarr hBC.base.occ

/-! ## 5. The sharp clause in the shape of `M4D.PaperTimeClause` -/

/-- **The paper's `(time)` clause at the paper's `(BTchoice)` schedule, at an arbitrary error
coefficient `CTf T Cerr`.**

Same shape as `M4D.PaperTimeClause`, with

* the schedule conjunct `B - 2 < T` replaced by the paper's `8 Cfin (B+5)/3 < T` (which
  *implies* `B - 2 < T` by `blt_of_sharpSchedule`, so every downstream use of the old conjunct
  survives), and
* the extra hypothesis `8 Cfin (⌈G⌉₊ + 7)/3 < T` on `T`, where `G = (1+64Cfin)(1+b)^(N-1)`.
  This is exactly the paper's `T > 8C(B+5)/3` at the witness `B = ⌈G⌉₊ + 2`, i.e. the smallest
  `B` meeting the geometric bound.  It is necessary, not cosmetic (`not_sharpSchedule_of_T_le`),
  and `exists_schedule_BT` shows it is satisfiable.

`CTf` is kept abstract because `(time)` reads only `(lococc)`, whose error coefficient may be
`PaperBlock.CTtot` or the sharper common `LocOccDerived.CTfin = max CTtot CTocc`; both instances
are below and neither needs a separate proof. -/
def PaperTimeClauseSharpAt (CTf : ℕ → ℝ → ℝ) (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (T : ℕ) (Cerr : ℝ),
    0 ≤ b → 1 ≤ T → 1 ≤ Cerr →
    64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
    (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (T : ℝ) - 3 →
    8 * PaperBlock.Cfin (N := N) p m *
        (((⌈(1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1)⌉₊ : ℕ) : ℝ) + 7)
        / 3 < (T : ℝ) →
    ∃ (B C₀ L₀ : ℕ), 1 ≤ B ∧ B + T + 3 ≤ C₀ ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 ∧
      8 * PaperBlock.Cfin (N := N) p m * ((B : ℝ) + 5) / 3 < (T : ℝ) ∧
      ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
        ∀ U : Swarming.Uniform.Array N,
          U ∈ RecClockLG.recordCarrier (N := N) p m r L →
          BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
              (PaperBlock.Hc p m U) (PaperBlock.Cfin (N := N) p m)
              (CTf T Cerr) T L r →
          PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L

/-- The `M4D.PaperTimeClause` instance: the error coefficient is the paper's `CTtot`. -/
def PaperTimeClauseSharp (p : ℝ) (m : ℕ) : Prop :=
  PaperTimeClauseSharpAt (fun T Cerr => PaperBlock.CTtot p m T Cerr) p m

/-- **`(time)` is proved, at every error coefficient.**  The witnesses are `B = ⌈G⌉₊ + 2`
(`G = (1+64Cfin)(1+b)^(N-1)`), `C₀ = B + T + 3`, and the threshold `max L₁ 1` of
`exists_L0_timeSharp`, whose only inputs are `(lococc)` and the paper's `T > 8C(B+5)/3`. -/
theorem paperTimeClauseSharpAt (CTf : ℕ → ℝ → ℝ) (p : ℝ) (m : ℕ) :
    PaperTimeClauseSharpAt CTf p m := by
  intro N inst hN b T Cerr hb hT1 _hCerr _h64 _hsch hsharp
  set C : ℝ := PaperBlock.Cfin (N := N) p m with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact PaperBlock.Cfin_pos (N := N) p m
  have hC1 : 1 ≤ C := by rw [hCdef]; exact PaperBlock.one_le_Cfin (N := N) p m
  set G : ℝ := (1 + 64 * C) * (1 + b) ^ (N - 1) with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    have h1 : (0 : ℝ) ≤ 1 + 64 * C := by linarith
    have h2 : (0 : ℝ) ≤ 1 + b := by linarith
    exact mul_nonneg h1 (pow_nonneg h2 _)
  set B : ℕ := ⌈G⌉₊ + 2 with hBdef
  have hB1 : 1 ≤ B := by omega
  have hBcast : (B : ℝ) + 5 = ((⌈G⌉₊ : ℕ) : ℝ) + 7 := by
    rw [hBdef]; push_cast; ring
  -- the paper's `T > 8C(B+5)/3` at this `B`
  have hTL : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ) := by
    rw [hBcast]; exact hsharp
  obtain ⟨L₁, -, hL₁⟩ := exists_L0_timeSharp (N := N) (p := p) (m := m) hN hCpos hB1 hTL
  refine ⟨B, B + T + 3, max L₁ 1, hB1, by omega, ?_, hTL, ?_⟩
  · -- the paper's geometric bound at the witness `B = ⌈G⌉₊ + 2`
    have hGle : G ≤ ((⌈G⌉₊ : ℕ) : ℝ) := Nat.le_ceil G
    rw [hBdef]
    push_cast
    linarith
  · intro L hL r _hr U hcarr hBC
    exact hL₁ L (le_trans (le_max_left _ _) hL) r U hcarr hBC.base.occ

/-- The `PaperBlock.CTtot` instance of `paperTimeClauseSharpAt`. -/
theorem paperTimeClauseSharp (p : ℝ) (m : ℕ) : PaperTimeClauseSharp p m :=
  paperTimeClauseSharpAt (fun T Cerr => PaperBlock.CTtot p m T Cerr) p m

/-! ## 6. Non-vacuity: the paper's order `B` then `T` always has a solution -/

/-- **The paper's `(BTchoice)` is satisfiable, in the paper's order.**  For every `b >= 0` there
are `B`, `T`, `C₀` with `B > (1+64Cfin)(1+b)^(N-1) + 1`, `T > 8 Cfin (B+5)/3`,
`T >= 64 Cfin`, `B - 2 < T` and `C₀ >= B + T + 3`.

So the sharp schedule of `PaperTimeClauseSharp` is inhabited at every `b >= 0`: the extra
hypothesis on `T` is not vacuous.  This is the witness the assembly should use in place of
`BlockAssembly.exists_schedule_T`; see `not_sharpSchedule_of_T_le` for why the latter's `T`
cannot be used. -/
theorem exists_schedule_BT {p : ℝ} {m : ℕ} (b : ℝ) (hb : 0 ≤ b) :
    ∃ B C₀ T : ℕ, 1 ≤ B ∧ 1 ≤ T ∧
      64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (T : ℝ) - 3 ∧
      8 * PaperBlock.Cfin (N := N) p m * ((B : ℝ) + 5) / 3 < (T : ℝ) ∧
      (B : ℝ) - 2 < (T : ℝ) ∧ B + T + 3 ≤ C₀ := by
  set C : ℝ := PaperBlock.Cfin (N := N) p m with hCdef
  set G : ℝ := (1 + 64 * C) * (1 + b) ^ (N - 1) with hG
  have hCpos : 0 < C := by rw [hCdef]; exact PaperBlock.Cfin_pos (N := N) p m
  have hC1 : 1 ≤ C := by rw [hCdef]; exact PaperBlock.one_le_Cfin (N := N) p m
  have hG0 : 0 ≤ G := by
    rw [hG]
    have h1 : (0 : ℝ) ≤ 1 + 64 * C := by linarith
    have h2 : (0 : ℝ) ≤ 1 + b := by linarith
    exact mul_nonneg h1 (pow_nonneg h2 _)
  set M : ℝ := max (64 * C) (8 * C * (((⌈G⌉₊ : ℕ) : ℝ) + 7) / 3) with hM
  set B : ℕ := ⌈G⌉₊ + 2 with hBdef
  set T : ℕ := ⌈M⌉₊ + 1 with hTdef
  have hB1 : 1 ≤ B := by omega
  have hT1 : 1 ≤ T := by omega
  have hBcast : (B : ℝ) + 5 = ((⌈G⌉₊ : ℕ) : ℝ) + 7 := by
    rw [hBdef]; push_cast; ring
  have hMle : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
  have hMlt : ((⌈M⌉₊ : ℕ) : ℝ) + 1 = (T : ℝ) := by
    rw [hTdef]; push_cast; ring
  have h64 : 64 * C ≤ (T : ℝ) := by
    have h1 : 64 * C ≤ M := le_max_left _ _
    have : (⌈M⌉₊ : ℝ) < (T : ℝ) := by rw [← hMlt]; linarith
    linarith
  have hTL : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ) := by
    rw [hBcast]
    have h2 : 8 * C * (((⌈G⌉₊ : ℕ) : ℝ) + 7) / 3 ≤ M := le_max_right _ _
    have : (⌈M⌉₊ : ℝ) < (T : ℝ) := by rw [← hMlt]; linarith
    linarith
  have hB2 : (B : ℝ) - 2 < (T : ℝ) :=
    blt_of_sharpSchedule (B := (B : ℝ)) (T := (T : ℝ)) (C := C) hC1
      (by exact_mod_cast hB1) hTL
  have hTge : G + 2 < (T : ℝ) := by
    have h2 : 8 * C * (((⌈G⌉₊ : ℕ) : ℝ) + 7) / 3 ≤ M := le_max_right _ _
    have h3 : G ≤ ((⌈G⌉₊ : ℕ) : ℝ) := Nat.le_ceil G
    have h4 : (8 : ℝ) ≤ 8 * C := by linarith
    have h5 : (0 : ℝ) ≤ ((⌈G⌉₊ : ℕ) : ℝ) + 7 := by positivity
    have h6 : 8 * (((⌈G⌉₊ : ℕ) : ℝ) + 7) / 3 ≤ 8 * C * (((⌈G⌉₊ : ℕ) : ℝ) + 7) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    have h7 : (⌈M⌉₊ : ℝ) < (T : ℝ) := by rw [← hMlt]; linarith
    nlinarith
  refine ⟨B, B + T + 3, T, hB1, hT1, h64, ?_, ?_, hTL, hB2, le_refl _⟩
  · have hGle : G ≤ ((⌈G⌉₊ : ℕ) : ℝ) := Nat.le_ceil G
    rw [hBdef]
    push_cast
    linarith
  · linarith
