/-
# Fixed-constant `hterm` for the actual interacting array

`areas/recordo/RecordoSupply.hterm_actual` proves the block/doubling form of the paper's
`(recordo)` for the actual array, but with `∃ T C₀` **inside** the almost-sure quantifier: `T`
and `C₀` may depend on the array `U`.  `SimJump.RecKernel.probCtxRT` and `SwarmM4.PCtxR`
instead fix `B`, `C₀`, `T` before their path-law hypotheses, so that shape is not matched.

Using `FixedBlocks.hterm_fixed`, the constants become

  `T = ⌈2 B / κ⌉ + 2`,   `C₀ = B + T + 1`,

where `κ` is the fixed ballistic constant of `RecordoSupply.speed_actual` (a function of `m, p`
only).  Hence `T`, `C₀` depend on `p`, `m`, `B` and on nothing else — in particular not on the
array, on the walker count `N`, or on the chosen record sequence.

The residual hypothesis is exactly the paper's diameter estimate `(diam)`, entering only through
the defect limit.  This is still a statement about the array's *own* record data; the separate
stopped-record-path law identification is isolated in `LawBridge.lean`.
-/
import Swarm.FixedBlocks
import Swarm.RecordoSupply

open Filter Topology MeasureTheory
open scoped BigOperators

namespace SwarmM4C

namespace ActualFixed

open RecordDefect RecordoSupply SwarmM4C.FixedConst

/-- **Fixed-constant `hterm` for every record sequence of the actual array.**

For every block coefficient `B ≥ 1` there are constants `T = ⌈2B/κ⌉+2`, `C₀ = B+T+1`, determined
by the fixed ballistic constant `κ(p,m)` and `B` alone, such that almost surely every record
sequence `τ` of the actual trajectory satisfies the paper's doubling block form at those
constants, whenever the diameter estimate `(diam)` holds. -/
theorem hterm_actual_fixed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (B : ℕ), 1 ≤ B → ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ (τ : ℕ → ℕ),
        IsRecord (actX p m U) τ →
        Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0) →
          ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ,
            GoodBlock (defect (actX p m U) τ) τ (⌈2 * (B : ℝ) / κ⌉₊ + 2)
              (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L) := by
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  refine ⟨κ, hκ, fun B hB N _inst hN => ?_⟩
  filter_upwards [hspeed N hN] with U hU τ hτ hspread
  have hspd := hU (Classical.arbitrary (Fin N))
  exact hterm_fixed hτ (actX_step p m U) (actX_zero p m U) hκ hspd
    (defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd hspread)
    B hB

/-- **The same at constructed record times.**  There is an almost-sure record sequence
(`Nat.find` of the first hitting time of each level) satisfying the fixed-constant doubling block
form, so the statement is non-vacuous. -/
theorem hterm_actual_fixed_exists {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (B : ℕ), 1 ≤ B → ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
        Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0) →
          ∃ τ : ℕ → ℕ, IsRecord (actX p m U) τ ∧
            ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ,
              GoodBlock (defect (actX p m U) τ) τ (⌈2 * (B : ℝ) / κ⌉₊ + 2)
                (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L) := by
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  refine ⟨κ, hκ, fun B hB N _inst hN => ?_⟩
  filter_upwards [hspeed N hN] with U hU hspread
  have hspd := hU (Classical.arbitrary (Fin N))
  have hreach : ∀ r : ℕ, ∃ n, runMax (actX p m U) n = (r : ℤ) := by
    intro r
    obtain ⟨n, hn⟩ := exists_runMax_ge (actX p m U) hκ hspd r
    obtain ⟨m', -, hm'⟩ := exists_runMax_eq (actX p m U) (actX_step p m U) (actX_zero p m U) hn
    exact ⟨m', hm'⟩
  have hτ : IsRecord (actX p m U) (recTime (actX p m U) hreach) :=
    isRecord_recTime _ (actX_step p m U) (actX_zero p m U) hreach
  refine ⟨recTime (actX p m U) hreach, hτ, ?_⟩
  exact hterm_fixed hτ (actX_step p m U) (actX_zero p m U) hκ hspd
    (defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd hspread)
    B hB

end ActualFixed

end SwarmM4C


