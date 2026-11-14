/-
# `HcompA` proved at the actual array

The paper's `hcomp` at the reset time of a separated leading block, `DiamAssembly.HcompA`,
with the sharp constant `(1+a)/(1-a)` (depending only on `m` and `p`).

The proof chain, at the reset time `s = resetTime (XA p m U) A n`:

1. `W_s^{A,A^c} ≤ H_s^{A}(max_A X_s) - H_s^{A}(max_{A^c} X_s)`   (`WA_le_HZ_diff`, monotonicity);
2. `H_s^{A}(y) - H_s^{A}(x) ≤ H_i(y) - H_i(x)` for a walker `i ∈ A` whose running maximum
   dominates the block (`HZ_group_diff_le`: the paper's `(hcomp)` summed over `u ∈ [x,y)`);
3. `H_i(y) - H_i(x) ≤ c (y-x) + 2 ε n` (`HZ_individual_diff_le`: `(spav)`/`(compare)`);
4. `y - x = spread_A(s) + gap_A(s)` exactly (`max_sub_max_eq_spread_add_gap`);
5. `gap_A(s) ≤ 4 + deficit_s + ε n` (`gapAt_reset_le_deficit_const`, the reset descent);
6. arithmetic, using `4 ≤ 2 + (2/ε)…`, i.e. the constant `4c` is absorbed into `ε n`.
-/
import Swarm.HcompGroup
import Swarm.FrozenBadTime
import Swarm.DiamAssemblyHpos

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie
open DiamAssembly

namespace DiamAssemblyHcomp

variable {N : ℕ}

/-- Every index has a distinct partner as soon as there are at least two. -/
theorem exists_ne_fin {N : ℕ} (hN : 2 ≤ N) (i : Fin N) : ∃ j : Fin N, j ≠ i := by
  by_cases hi : i = ⟨0, by omega⟩
  · exact ⟨⟨1, by omega⟩, by rw [hi]; simp⟩
  · exact ⟨⟨0, by omega⟩, fun h => hi h.symm⟩

/-- **Eventual nonnegativity of every actual walker**, from the accepted a.e. transience
(`SwarmBad.ae_transience_actual`). -/
theorem hpos_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ t : ℕ in atTop, ∀ i : Fin N, 0 ≤ XA p m U i t := by
  have htr : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => XA p m U i n) atTop atTop := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne_fin hN i
    have h := SwarmBad.ae_transience_actual (N := N) hp0 hp1 hm i j hji.symm
    simpa [XA_apply, Finset.compl_eq_univ_sdiff] using h
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n => XA p m U i n) atTop atTop := MeasureTheory.ae_all_iff.mpr htr
  filter_upwards [hall] with U hU
  exact Filter.eventually_all.mpr (fun i => (tendsto_atTop.mp (hU i)) 0)

/-- **The paper's `hcomp` at the reset time: `DiamAssembly.HcompA` with the sharp constant.** -/
theorem hcompA_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) [Nonempty (Fin N)] :
    HcompA (N := N) p m (SwarmSpatial.targetParam p m) := by
  have hp : (1 / 2 : ℝ) ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hm1 : 1 ≤ m := by omega
  set c : ℝ := SwarmSpatial.targetParam p m with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, SwarmSpatial.targetParam]
    exact div_pos (by linarith [SwarmSpatial.aParam_nonneg hp0 hp1 hm1])
      (SwarmSpatial.one_sub_target_pos hp0 hp1 hm1)
  have hcpos' : 0 < SwarmSpatial.targetParam p m := by rw [← hcdef]; exact hcpos
  unfold HcompA
  filter_upwards [spav_uniform_array' (N := N) hp0 hp1 hm,
      hpos_actual (N := N) hp0 hp1 hm hN] with U hspav hposU
  intro ε hε
  set e : ℝ := ε / (2 * (c + 2)) with hedef
  have hc2 : (0 : ℝ) < c + 2 := by linarith
  have hepos : 0 < e := by rw [hedef]; positivity
  have heval : (c + 2) * e = ε / 2 := by
    rw [hedef]
    field_simp
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hspav e hepos)
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
    (NestedLeaderPot.gapAt_reset_le_deficit_const (XA p m U) (unitStep_XA p m U)
      (zero_XA p m U) hposU e hepos)
  obtain ⟨M₃, hM₃⟩ := exists_nat_gt (4 * c / ε)
  filter_upwards [Filter.eventually_ge_atTop M₁, Filter.eventually_ge_atTop M₂,
    Filter.eventually_ge_atTop M₃] with n hn1 hn2 hn3
  intro A hA hAc hlead hsep
  -- the reset time and its deterministic properties
  have hsn : LeaderDescent.resetTime (XA p m U) A n ≤ n :=
    LeaderDescent.resetTime_minimal (XA p m U) A n (fun t h1 h2 => by
      have htn : t = n := le_antisymm h2 h1
      rw [htn]
      exact hsep)
  have hsep_s : LeaderDescent.SepMax (XA p m U) A (LeaderDescent.resetTime (XA p m U) A n) :=
    LeaderDescent.resetTime_spec (XA p m U) A n _ le_rfl hsn
  have hnn_s : ∀ i, 0 ≤ XA p m U i (LeaderDescent.resetTime (XA p m U) A n) := hsep_s.1
  have hlead_s : NestedLeader.Leading
      (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) A :=
    LeaderDescent.leading_of_sepMax (X := XA p m U) hsep_s
  -- the two block maxima
  have hy0 : 0 ≤ A.sup' hA
      (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) := by
    obtain ⟨a, ha⟩ := hA
    exact le_trans (hnn_s a) (Finset.le_sup' (fun i => XA p m U i _) ha)
  have hys : A.sup' hA (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n))
      ≤ ((LeaderDescent.resetTime (XA p m U) A n : ℕ) : ℤ) := by
    refine Finset.sup'_le hA _ (fun k hk => ?_)
    exact le_trans (LeaderDescent.le_runMax (XA p m U) k _)
      (runMax_XA_le p m U k (LeaderDescent.resetTime (XA p m U) A n))
  have hyn : (A.sup' hA
      (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n))).toNat ≤ n := by
    have h1 : (A.sup' hA
        (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n))).toNat
        ≤ ((LeaderDescent.resetTime (XA p m U) A n : ℕ) : ℤ).toNat := Int.toNat_le_toNat hys
    have h2 : ((LeaderDescent.resetTime (XA p m U) A n : ℕ) : ℤ).toNat
        = LeaderDescent.resetTime (XA p m U) A n := Int.toNat_natCast _
    omega
  have hx0 : 0 ≤ (univ \ A).sup' hAc
      (fun j => XA p m U j (LeaderDescent.resetTime (XA p m U) A n)) := by
    obtain ⟨b, hb⟩ := hAc
    exact le_trans (hnn_s b) (Finset.le_sup' (fun j => XA p m U j _) hb)
  have hxy : (univ \ A).sup' hAc
        (fun j => XA p m U j (LeaderDescent.resetTime (XA p m U) A n))
      ≤ A.sup' hA (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) := by
    refine Finset.sup'_le hAc _ (fun j hj => ?_)
    have hjA : j ∉ A := (Finset.mem_sdiff.mp hj).2
    obtain ⟨a, ha⟩ := hA
    exact le_trans (hlead_s a ha j hjA) (Finset.le_sup' (fun i => XA p m U i _) ha)
  have hyR : A.sup' hA (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n))
      ≤ A.sup' hA (fun k => LeaderDescent.runMax (XA p m U) k
          (LeaderDescent.resetTime (XA p m U) A n)) := by
    refine Finset.sup'_le hA _ (fun k hk => ?_)
    exact le_trans (LeaderDescent.le_runMax (XA p m U) k _)
      (Finset.le_sup' (fun k => LeaderDescent.runMax (XA p m U) k _) hk)
  -- the group comparison, and the individual comparison for the walker it selects
  obtain ⟨i, hiA, hgi⟩ := HZ_group_diff_le hp hp1' U (s := LeaderDescent.resetTime (XA p m U) A n)
    hA hx0 hxy hyR
  have hind : HZ (omegaN p m U i) (A.sup' hA
        (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)))
      - HZ (omegaN p m U i) ((univ \ A).sup' hAc
        (fun j => XA p m U j (LeaderDescent.resetTime (XA p m U) A n)))
      ≤ c * (((A.sup' hA (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) : ℤ) : ℝ)
        - (((univ \ A).sup' hAc
            (fun j => XA p m U j (LeaderDescent.resetTime (XA p m U) A n)) : ℤ) : ℝ))
        + 2 * e * (n : ℝ) :=
    HZ_individual_diff_le hp hp1' (m := m) (c := c) (ε := e) (n := n) U i
      (fun t ht => hM₁ n hn1 i t ht) hx0 hxy hyn
  -- the potential at the reset time
  have hW : Wtot p m U (LeaderDescent.resetTime (XA p m U) A n) A
      ≤ HZ (wA p m U (LeaderDescent.resetTime (XA p m U) A n) Aᶜᶜ) (A.sup' hA
          (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)))
        - HZ (wA p m U (LeaderDescent.resetTime (XA p m U) A n) Aᶜᶜ) ((univ \ A).sup' hAc
          (fun j => XA p m U j (LeaderDescent.resetTime (XA p m U) A n))) := by
    rw [Wtot_eq p m U _ hA hAc]
    have h := WA_le_HZ_diff (p := p) (m := m) hp hp1' U
      (s := LeaderDescent.resetTime (XA p m U) A n) (I := A) (J := Aᶜ) hA hAc hxy
    simpa [XA_apply, Finset.compl_eq_univ_sdiff] using h
  -- assemble: `W_s ≤ c (y - x) + 2 e n`
  have hchain : Wtot p m U (LeaderDescent.resetTime (XA p m U) A n) A
      ≤ c * (((A.sup' hA
            (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) : ℤ) : ℝ)
          - (((univ \ A).sup' hAc
            (fun j => XA p m U j (LeaderDescent.resetTime (XA p m U) A n)) : ℤ) : ℝ))
        + 2 * e * (n : ℝ) := by
    linarith [hW, hgi, hind]
  rw [NestedLeaderPot.max_sub_max_eq_spread_add_gap (X := XA p m U) hA hAc
    (LeaderDescent.resetTime (XA p m U) A n)] at hchain
  -- the reset descent
  have hgap := hM₂ n hn2 A hA hAc hlead hsep
  have hcgap : c * ((LeaderDescent.gapAt
        (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) A : ℤ) : ℝ)
      ≤ c * (4 + ((NestedLeader.deficit (XA p m U)
          (LeaderDescent.resetTime (XA p m U) A n) : ℤ) : ℝ) + e * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap hcpos.le
  have hconst : 2 * c ≤ ε * (n : ℝ) / 2 := by
    have h4 : 4 * c / ε < (n : ℝ) := by
      have h1 : (M₃ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      linarith
    rw [div_lt_iff₀ hε] at h4
    linarith
  have heval' : (c + 2) * e * (n : ℝ) = ε / 2 * (n : ℝ) := by rw [heval]
  set S : ℝ := ((NestedLeader.blockSpread
    (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) A : ℤ) : ℝ) with hSdef
  set G : ℝ := ((LeaderDescent.gapAt
    (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) A : ℤ) : ℝ) with hGdef
  set D : ℝ := ((NestedLeader.deficit (XA p m U)
    (LeaderDescent.resetTime (XA p m U) A n) : ℤ) : ℝ) with hDdef
  have h4c : 4 * c ≤ ε * (n : ℝ) := by linarith
  calc Wtot p m U (LeaderDescent.resetTime (XA p m U) A n) A
      ≤ c * (S + G) + 2 * e * (n : ℝ) := hchain
    _ = (c * S + c * G) + 2 * e * (n : ℝ) := by ring
    _ ≤ (c * S + c * (4 + D + e * (n : ℝ))) + 2 * e * (n : ℝ) := by linarith
    _ = c * (S + D + 2) + ((c + 2) * e * (n : ℝ)) + 2 * c := by ring
    _ = c * (S + D + 2) + ε / 2 * (n : ℝ) + 2 * c := by rw [heval']
    _ ≤ c * (S + D + 2) + ε / 2 * (n : ℝ) + ε / 2 * (n : ℝ) := by linarith
    _ = c * (S + D + 2) + ε * (n : ℝ) := by ring

/-- **The sharp constant is positive** (and independent of `N`). -/
theorem targetParam_pos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m) :
    0 < SwarmSpatial.targetParam p m := by
  rw [SwarmSpatial.targetParam]
  exact div_pos (by linarith [SwarmSpatial.aParam_nonneg hp0 hp1 hm])
    (SwarmSpatial.one_sub_target_pos hp0 hp1 hm)

/-- For `N ≤ 1` a block and its complement cannot both be nonempty, so `HcompA` holds
vacuously for every constant, in particular for the sharp one. -/
theorem hcompA_vacuous {p : ℝ} {m : ℕ} [Nonempty (Fin N)] (hN : N ≤ 1) (K : ℝ) :
    HcompA (N := N) p m K := by
  unfold HcompA
  filter_upwards with U ε hε
  refine Filter.Eventually.of_forall (fun n => ?_)
  intro A hA hAc hlead hsep
  have hcard : Fintype.card (Fin N) ≤ 1 := by simpa using hN
  have hsub : Subsingleton (Fin N) := Fintype.card_le_one_iff_subsingleton.mp hcard
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have hbA : b ∉ A := (Finset.mem_sdiff.mp hb).2
  rw [@Subsingleton.elim (Fin N) hsub b a] at hbA
  exact absurd ha hbA

/-- **`(diam)` with `HcompA` discharged.**  The remaining inputs are exactly the variance
estimate `LogVarBound` and the paper's `(prelim)` `HdefA`; the positional comparison is now a
theorem.  This is a conditional corollary, not `(diam)`. -/
theorem diam_conditional {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) [Nonempty (Fin N)] {C : ℝ}
    (hC : LogVarBound (N := N) p m C) (hdef : HdefA (N := N) p m) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (XA p m U) n : ℤ) : ℝ) / (n : ℝ)) atTop
        (𝓝 0) :=
  DiamAssembly.ae_spread_div_tendsto_zero_actual (N := N) hp0 hp1 hm hN
    (le_of_lt (targetParam_pos hp0 hp1 (show 1 ≤ m by omega))) hC
    (hcompA_actual hp0 hp1 hm hN) hdef

end DiamAssemblyHcomp
