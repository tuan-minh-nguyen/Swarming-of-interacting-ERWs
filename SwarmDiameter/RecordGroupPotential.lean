import SwarmDiameter.MarkedSpatialTail
import Swarm.RecClockLocgroup
import Swarm.LocCoordRange
import Swarm.GammaSigma

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl SwarmRecordMeas.Actual SepGroup.Model
open LocGroupSimul SwarmMarks
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- The spatial increment of the group potential is bounded by a linear
function of the interval length plus `ε * L`, uniformly over all groups,
times and sites in the record interval except on an event of probability
at most `exp (-c * L ^ (1 / 3))`. -/
theorem record_group_potential_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N T : ℕ) [Nonempty (Fin N)] {ε : ℝ}, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ (A : Finset (Fin N)) (hA : A.Nonempty) (n a b : ℕ),
            recTimeA p m U r ≤ n ∧ n ≤ recTimeA p m U r + T * L ∧
            r - (T + 2) * L ≤ a ∧ a ≤ b ∧ (b : ℤ) ≤ runMaxA p m U hA n ∧
            C * ((b : ℝ) - (a : ℝ)) + ε * L <
              HA p m U n A (b : ℤ) - HA p m U n A (a : ℤ)})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hlocal⟩ := arrayMeasure_local_hof_estimates hp₀ hp₁ hm
  refine ⟨K + 1, by linarith, ?_⟩
  intro N T _ ε hε
  obtain ⟨c, hc, h⟩ := hlocal N (2 * T + 2) hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with L hL
  intro r hr
  let a₀ := r - (T + 2) * L
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hL a₀)
  rintro U ⟨hU, A, hA, n, a, b, hs, ht, ha, hab, hb, hbad⟩
  obtain ⟨i, hi, hiMax⟩ := Finset.exists_mem_eq_sup' hA
    (fun j => Swarming.Trajectory.runMax p m U j n)
  have hbR : (b : ℤ) ≤ Swarming.Trajectory.runMax p m U i n := hb.trans_eq hiMax
  have hrec := RecClockLG.recHyp_at_record hU
  have hiR := (RecHyp_runMax_bounds hrec hs ht i).2
  have hab₀ : a₀ ≤ a := ha
  have hwidth : a - a₀ ≤ (2 * T + 2) * L := by
    have hsum : (2 * T + 2) * L = (T + 2) * L + T * L := by ring
    dsimp only [a₀]
    rw [hsum]
    have hr' : (T + 2) * L ≤ r :=
      (Nat.mul_le_mul_right L (by omega : T + 2 ≤ T + 3)).trans hr
    omega
  have hlen : b - a ≤ (2 * T + 2) * L + 1 := by
    have hsum : (2 * T + 2) * L = (T + 2) * L + T * L := by ring
    rw [hsum]
    dsimp only [a₀] at hab₀
    omega
  refine Or.inr ⟨i, a - a₀, b - a, hwidth, hlen, ?_⟩
  rw [Nat.add_sub_of_le hab₀, Nat.add_sub_of_le hab]
  by_contra! hgood
  have hsum : ∑ x ∈ Finset.Ico a b, (Cookie.hfix (omegaN p m U i) x) ^ 2
      ≤ K * ((b : ℝ) - (a : ℝ)) + K * (ε * L / K) := by
    simp only [Loccoord.hfix_omegaN_eq_hof (show p ≠ 0 by linarith)]
    push_cast [Nat.cast_sub hab] at hgood
    have he : K * (ε * (L : ℝ) / K) = ε * L := by field_simp
    rwa [he]
  have hβ : 0 ≤ ε * (L : ℝ) / K := by positivity
  have hdiff := Loccoord.loccoord_fixed hp₀.le hp₁.le U hi hab hbR hK.le hβ hsum
  have hle : (a : ℝ) ≤ b := by exact_mod_cast hab
  have he : K / 2 * (ε * (L : ℝ) / K) = ε * L / 2 := by field_simp
  rw [he] at hdiff
  nlinarith [mul_nonneg (show 0 ≤ K + 1 by positivity) (sub_nonneg.mpr hle)]

end Swarming.Diameter
