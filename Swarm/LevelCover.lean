/-
# The covering lemma with `C₀ ℓ ≤ r` on every certificate

`TightCover.Ctx.exists_certificate` produces, for every index `u` past the random transient whose
record distance exceeds `C₀ K`, a certificate `(r, ℓ)`: a failing block at level `ℓ ≥ K` started at
`r`, with `d r ≤ ℓ` and `u ∈ [r, r + 4Bℓ]`.  `Tightness.lean` then bounds the probability of each
certificate event using `hblk`, which is only available for `C₀ ℓ ≤ r`; in `Tightness.lean` that
inequality comes from the hypothesis `hR`.

This file proves that the inequality is a *property of the certificates the procedure produces*,
not an independent almost-sure statement: under the single-level goodness hypothesis of
`LevelBound.lean` (a good level `2 ^ g r * K` at every start `r ≥ r₀`, a scale that drops by at
most a factor two between starts, and a starting level inside the scale), every certificate
satisfies `C₀ ℓ ≤ r`.

Consequently `hR` can be dropped from `ProbCtx` and replaced by the scale hypotheses
(`PCtx.measure_gt_le` in `ScaleTight.lean`).
-/
import Swarm.LevelBound

open Classical
open scoped BigOperators

namespace RecordTight

namespace Ctx

/-- **Covering by certificates, with the level bound.**  Every index `u` past the initial
transient `r₀ + 2 B L₀` whose distance below the record exceeds `C₀ K` carries a certificate
`(r, ℓ)` with `ℓ ≥ K`, `d r ≤ ℓ`, a failing block `¬ Good r ℓ`, `u ∈ [r, r + 4Bℓ]`, and
`C₀ ℓ ≤ r`.

The last conjunct is what the union bound of `Tightness.lean` needs from `hR`. -/
theorem exists_certificate_le (c : Ctx) (g : ℕ → ℕ)
    (hgood : ∀ r, c.r₀ ≤ r → c.Good r (2 ^ g r * c.K))
    (hg : ∀ r r', c.r₀ ≤ r → r ≤ r' → g r ≤ g r' + 1)
    (h₀ : ∃ b, c.L₀ = 2 ^ b * c.K ∧ b ≤ g c.r₀)
    (hscale : ∀ r, c.r₀ ≤ r → 2 * c.C₀ * (2 ^ g r * c.K) ≤ r)
    {u : ℕ} (hu : c.r₀ + 2 * c.B * c.L₀ ≤ u) (hdu : c.C₀ * c.K < c.d u) :
    ∃ r ℓ, c.K ≤ ℓ ∧ c.d r ≤ ℓ ∧ ¬ c.Good r ℓ ∧ c.r₀ ≤ r ∧ r ≤ u ∧
      u ≤ r + 4 * c.B * ℓ ∧ c.C₀ * ℓ ≤ r := by
  have hKL₀ : c.K ≤ c.L₀ := le_trans (le_max_left _ _) c.hstart
  have hlvv : c.lv 0 = c.L₀ := by rw [lv_zero, max_eq_right hKL₀]
  -- the block containing `u`
  have hex : ∃ n, u < c.ps (n + 1) := ⟨u, by have := c.le_ps_add (u + 1); omega⟩
  obtain ⟨n, hn, hnmin⟩ : ∃ n, u < c.ps (n + 1) ∧ ∀ m < n, c.ps (m + 1) ≤ u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_lt.1 (Nat.find_min hex hm)⟩
  have hpsn_le : c.ps n ≤ u := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, ps_zero]; omega
    · simpa [Nat.sub_add_cancel h] using hnmin (n - 1) (by omega)
  have hblock : c.d u ≤ c.C₀ * c.Mlv n := c.d_le_of_mem_block n u hpsn_le hn.le
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- the first block
    subst hn0
    have hn1 : u < c.ps 1 := by simpa using hn
    have hk0 : 1 ≤ c.kf 0 := by
      rcases Nat.eq_zero_or_pos (c.kf 0) with h | h
      · exfalso
        have hps1 : c.ps 1 = c.r₀ + c.B * c.L₀ := by
          rw [ps_succ, ps_zero, c.Mlv_eq_of_kf_zero h, hlvv]
        have h1 : c.ps 1 ≤ u := by rw [hps1]; nlinarith
        omega
      · exact h
    refine ⟨c.ps 0, 2 ^ (c.kf 0 - 1) * c.lv 0, ?_, ?_, c.fail_not_good hk0, ?_, ?_, ?_,
      c.cert_level_le g hgood hg h₀ hscale hk0⟩
    · exact le_trans (c.le_lv 0) (c.le_pow_mul_lv hk0)
    · exact le_trans (c.d_ps_le_lv 0) (c.le_pow_mul_lv hk0)
    · rw [ps_zero]
    · rw [ps_zero]; exact le_trans (Nat.le_add_right _ _) hu
    · rw [ps_succ, c.Mlv_eq_two_mul hk0] at hn
      have h1 : c.B * (2 * (2 ^ (c.kf 0 - 1) * c.lv 0)) ≤
          4 * c.B * (2 ^ (c.kf 0 - 1) * c.lv 0) := by
        nlinarith [Nat.zero_le (c.B * (2 ^ (c.kf 0 - 1) * c.lv 0))]
      omega
  · -- later blocks: the last failing block index at or before `n`
    set P : ℕ → Prop := fun i => 1 ≤ c.kf i with hP
    set j := Nat.findGreatest P n with hj
    have hj_le : j ≤ n := Nat.findGreatest_le n
    by_cases hfail : P j
    · have hsucc : ∀ i, j < i → i ≤ n → c.kf i = 0 := by
        intro i hi1 hi2
        have h := Nat.findGreatest_is_greatest (P := P) hi1 hi2
        simp only [hP] at h ⊢
        omega
      have hgt : ∀ i, j < i → i ≤ n → c.K < c.lv i := by
        intro i hi1 hi2
        by_contra hle
        push_neg at hle
        have hik : c.lv i = c.K := le_antisymm hle (c.le_lv i)
        have hkfn : c.kf n = 0 := hsucc n (by omega) le_rfl
        have hlvn : c.lv n ≤ c.lv i :=
          c.lv_le_of_successes hi2 (fun k hk1 hk2 => hsucc k (by omega) (by omega))
        refine absurd hdu (not_lt.2 ?_)
        refine le_trans hblock ?_
        rw [c.Mlv_eq_of_kf_zero hkfn]
        exact Nat.mul_le_mul_left _ (le_trans hlvn (le_of_eq hik))
      have hchain := c.chain_bound hsucc hgt
      have hpsj1 : c.ps (j + 1) = c.ps j + c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j)) := by
        rw [ps_succ, c.Mlv_eq_two_mul hfail]
      have hlvj1 : c.lv (j + 1) = 2 ^ (c.kf j - 1) * c.lv j := c.lv_succ_eq_of_fail hfail
      refine ⟨c.ps j, 2 ^ (c.kf j - 1) * c.lv j, ?_, ?_, c.fail_not_good hfail, ?_, ?_, ?_,
        c.cert_level_le g hgood hg h₀ hscale hfail⟩
      · exact le_trans (c.le_lv j) (c.le_pow_mul_lv hfail)
      · exact le_trans (c.d_ps_le_lv j) (c.le_pow_mul_lv hfail)
      · exact le_trans (Nat.le_add_right _ _) (le_ps_add c j)
      · exact le_trans (c.ps_mono hj_le) hpsn_le
      · have hb : c.ps (n + 1) ≤
            c.ps j + 2 * (c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) := by
          rw [hpsj1, hlvj1] at hchain
          calc c.ps (n + 1) ≤ (c.ps j + c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) +
                c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j)) := hchain
            _ = c.ps j + 2 * (c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) := by ring
        have h4 : 2 * (c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) =
            4 * c.B * (2 ^ (c.kf j - 1) * c.lv j) := by ring
        omega
    · -- no failing block at all
      have hkfz : ∀ i, i ≤ n → c.kf i = 0 := by
        intro i hi
        have hPi : ¬ P i := by
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · rcases Nat.eq_zero_or_pos i with hi0 | hipos
            · rw [hi0]; exact hj0 ▸ hfail
            · have hfg : Nat.findGreatest P n = 0 := hj.symm.trans hj0
              exact Nat.findGreatest_eq_zero_iff.1 hfg hipos hi
          · exact absurd (Nat.findGreatest_of_ne_zero hj.symm hjpos.ne') hfail
        simp only [hP] at hPi
        omega
      have hgt : ∀ i, 0 < i → i ≤ n → c.K < c.lv i := by
        intro i hi1 hi2
        by_contra hle
        push_neg at hle
        have hik : c.lv i = c.K := le_antisymm hle (c.le_lv i)
        have hlvn : c.lv n ≤ c.lv i :=
          c.lv_le_of_successes hi2 (fun k _ _ => hkfz k (by omega))
        refine absurd hdu (not_lt.2 ?_)
        refine le_trans hblock ?_
        rw [c.Mlv_eq_of_kf_zero (hkfz n le_rfl)]
        exact Nat.mul_le_mul_left _ (le_trans hlvn (le_of_eq hik))
      have hchain := c.chain_bound (j := 0) (n := n)
        (fun i _ hi2 => hkfz i hi2) hgt
      have hps1 : c.ps 1 = c.r₀ + c.B * c.L₀ := by
        rw [ps_succ, ps_zero, c.Mlv_eq_of_kf_zero (hkfz 0 (by omega)), hlvv]
      have hlv1 : c.lv 1 = c.L₀ / 2 := by
        rw [lv_succ_eq_div (hkf := hkfz 0 (by omega)) (h := hgt 1 (by omega) hnpos), hlvv]
      rw [hps1, hlv1] at hchain
      have h2 : 2 * (c.L₀ / 2) ≤ c.L₀ := by
        have := Nat.div_mul_le_self c.L₀ 2
        omega
      have h3 : c.ps (n + 1) ≤ c.r₀ + 2 * c.B * c.L₀ := by nlinarith
      omega

end Ctx

end RecordTight

