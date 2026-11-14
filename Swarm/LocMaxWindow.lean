/-
# Composing the public `(locmax)` bound with the windowed envelope

This is the positive half of the bridge, at the level the paper actually uses it.

* `hfix_of_locmax_window` — *deterministic*: if the `(locmax)` window `Ico a b` contains every
  level of the level-window `[A-1, xTop]`, then the `hfix (omegaN i)` half of that level window is
  bounded by the same threshold, via `Loccoord.hfix_omegaN_eq_hof`.
* `exists_hfix_level_window_tail` — *probabilistic*: `WideRepair.array_locmax_hG_wide` applied to
  any window `Ico (A-M) (A+Up)` with `M ≤ A`, `M+Up ≤ K·L` gives the actual tail
  `≤ exp(-c L^{1/16})` of the event "some `hfix (omegaN i)` exceeds `xOf L` on a level window
  `Ico a b ⊆ Ico (A-M) (A+Up)`".  This is exactly the hypothesis `hH` of
  `SiteWindow.goodWWin_of_locmax`, whose levels `[A-1, xTop]` have cardinality `O_T(L)`.
* `goodWWin_of_locmax_window` — the two together with `(sep)` and the `G`-tail produce the
  windowed good event.

The missing hypothesis of the *prefix* version, `∀ u ≤ xTop` over the whole prefix, is exactly
what `PrefixObstruction.lean` shows cannot be supplied by any window data.
-/
import Swarm.WideLocMaxG
import Swarm.LocCoord
import Swarm.WindowIncrement

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1

variable {N : ℕ}

/-! ### 1. The deterministic cover -/

/-- **`(locmax)` on a window bounds `hfix` on every level window it contains.** -/
theorem hfix_of_locmax_window {p : ℝ} (hp0 : p ≠ 0) {m n : ℕ} {K : Finset (Fin N)}
    (hK : K.Nonempty) {U : Array N} {a b : ℕ} {x : ℝ}
    (h : ∀ j : Fin N, ∀ y ∈ Finset.Ico a b, hof p (siteMarks p m U j) y ≤ x)
    {A : ℕ} (hcover : ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n K hK U → v ∈ Finset.Ico a b) :
    ∀ i : Fin N, ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n K hK U →
      hfix (omegaN p m U i) v ≤ x := by
  intro i v hv1 hv2
  rw [Loccoord.hfix_omegaN_eq_hof (p := p) hp0 (m := m) (U := U) i v]
  exact h i v (hcover v hv1 hv2)

/-! ### 2. The actual `(locmax)` tail on a level window -/

/-- **The `hfix` tail on any level window of cardinality `≤ K·L` inside a `(locmax)` window.**
This is `WideRepair.array_locmax_hG_wide` read through `Loccoord.hfix_omegaN_eq_hof`. -/
theorem exists_hfix_level_window_tail {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (K : ℝ) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      ((M : ℝ) + (Up : ℝ)) ≤ K * (L : ℝ) →
      ∀ (a b : ℕ), A - M ≤ a → b ≤ A + Up →
      (arrayMeasure N) {U : Array N | ∃ i : Fin N, ∃ v ∈ Finset.Ico a b,
          xOf L ≤ hfix (omegaN p m U i) v}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨c, hc, L₀, h⟩ := WideRepair.array_locmax_hG_wide (N := N) (p := p) hp0 hp1 hm K hK
  have hpne : p ≠ 0 := by linarith
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M Up hMA hMU a b ha hb
  refine le_trans (measure_mono ?_) (h L hL A M Up hMA hMU)
  intro U hU
  obtain ⟨i, v, hv, hle⟩ := hU
  have hvlo : A - M ≤ v := le_trans ha (Finset.mem_Ico.mp hv).1
  have hvhi : v < A + Up := lt_of_lt_of_le (Finset.mem_Ico.mp hv).2 hb
  refine ⟨i, v, Finset.mem_Ico.mpr ⟨hvlo, hvhi⟩, Or.inl ?_⟩
  rwa [← Loccoord.hfix_omegaN_eq_hof (p := p) hpne (m := m) (U := U) i v]

/-! ### 3. The windowed good event from `(locmax)` on a covering window -/

/-- **The windowed `GoodW` from a `(locmax)` window covering the level window.** -/
theorem goodWWin_of_locmax_window {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {A a b : ℕ} {H G : ℝ} (hH1 : 1 ≤ H) (hGnn : 0 ≤ G)
    (hA : ∀ i ∈ I, A ≤ (runMax p m U i n).toNat)
    (hLoc : ∀ j : Fin N, ∀ y ∈ Finset.Ico a b, hof p (siteMarks p m U j) y ≤ H)
    (hcover : ∀ v : ℕ, A ≤ v + 1 →
      v ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U → v ∈ Finset.Ico a b)
    (hG : ∀ i ∈ I, ∀ u : ℕ, A ≤ u →
      u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U →
      Gtail p m U i u (n + 2) ≤ G) :
    GoodWWin p m n I J hI (max (2 * H + 6) (2 * G)) A U := by
  have hpne : p ≠ 0 := by linarith
  refine goodWWin_of_locmax hp0 hp1 I J hI hJ hid hsep hH1 hGnn hA ?_ hG
  intro i hi v hv1 hv2
  exact hfix_of_locmax_window (K := I ∪ J) hpne (hI.mono Finset.subset_union_left)
    (x := H) hLoc hcover i v hv1 hv2

/-! ### 4. The record-window instantiation -/

/-- **The level window `[A-1, xTop]` of the record geometry** is contained in the `(locmax)` window
`Ico (A-1) (A + (T+1)L + 3)` when `xTop ≤ r+1` and `r+1 ≤ A + (T+1)L + 2`.  The window's
cardinality is `(T+1)L + 4`. -/
theorem level_window_subset_record {p : ℝ} {m n : ℕ} {K : Finset (Fin N)} (hK : K.Nonempty)
    (U : Array N) {A r T L : ℕ} (hA1 : 1 ≤ A) (hrA : r + 1 ≤ A + ((T + 1) * L + 2))
    (hxTop : xTop p m n K hK U ≤ r + 1) :
    ∀ v : ℕ, A ≤ v + 1 → v ≤ xTop p m n K hK U →
      v ∈ Finset.Ico (A - 1) (A + ((T + 1) * L + 3)) := by
  intro v hv1 hv2
  rw [Finset.mem_Ico]
  exact ⟨by omega, by omega⟩

end SiteWindow

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1

variable {N : ℕ}

/-- **The record-window `hfix` tail.**  For the actual array, every level of the record window
`[A-1, r+1]` has `hfix (omegaN p m U i) ≤ L^{1/16}` off an event of mass `≤ exp(-c_T L^{1/16})`,
provided `r+1 ≤ A + (T+1)L + 2` and `4 ≤ L`.  This is `WideRepair.array_locmax_hG_wide` read
through `LocCoord.hfix_omegaN_eq_hof` on the window `Ico (A-1) (A+(T+1)L+3)`, whose cardinality is
`(T+1)L+4 ≤ (T+2)L`.

This is the *true* form of the site-locality bridge: the level window it controls is exactly the
one `goodWWin_of_locmax` needs, and it is `O_T(L)`, not the whole prefix `[0, xTop]`.  The
constants `C` and `L₀` may depend on `T`, as in the paper's `C_T`, `c_T`. -/
theorem exists_hfix_record_window_tail {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ C : ℕ → ℝ, (∀ T : ℕ, 0 < C T) ∧ ∃ L₀ : ℕ → ℕ, ∀ (T : ℕ), ∀ L ≥ L₀ T,
      ∀ (A r : ℕ), 4 ≤ L → 1 ≤ A → r + 1 ≤ A + ((T + 1) * L + 2) →
      (arrayMeasure N)
          {U : Array N | ∃ i : Fin N, ∃ v ∈ Finset.Ico (A - 1) (r + 2),
            xOf L ≤ hfix (omegaN p m U i) v}
        ≤ ENNReal.ofReal (Real.exp (-(C T) * xOf L)) := by
  have h : ∀ T : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      ((M : ℝ) + (Up : ℝ)) ≤ ((T : ℝ) + 2) * (L : ℝ) →
      ∀ (a b : ℕ), A - M ≤ a → b ≤ A + Up →
      (arrayMeasure N) {U : Array N | ∃ i : Fin N, ∃ v ∈ Finset.Ico a b,
          xOf L ≤ hfix (omegaN p m U i) v}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) :=
    fun T => exists_hfix_level_window_tail hp0 hp1 hm ((T : ℝ) + 2) (by positivity)
  choose C hC L₀ hL₀ using h
  refine ⟨C, hC, L₀, ?_⟩
  intro T L hL A r hL4 hA1 hrA
  have hcard : ((1 : ℕ) : ℝ) + (((T + 1) * L + 3 : ℕ) : ℝ) ≤ ((T : ℝ) + 2) * (L : ℝ) := by
    push_cast
    have hLr : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
    nlinarith
  have hb : r + 2 ≤ A + ((T + 1) * L + 3) := by omega
  exact hL₀ T L hL A 1 ((T + 1) * L + 3) hA1 hcard (A - 1) (r + 2) le_rfl hb

end SiteWindow

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 5. The `G`-half: `Gtail` is dominated by the `Gsup` of `(locmax)` -/

/-- The ratio `rq (omegaN)` is the mark ratio `rhoOf` of the site marks. -/
theorem rq_omegaN_eq_rhoOf (hp0 : p ≠ 0) (U : Array N) (i : Fin N) (v : ℕ) :
    rq (omegaN p m U i) v = rhoOf p (siteMarks p m U i v) := by
  unfold rq
  rw [Loccoord.omegaN_eq (p := p) (m := m) (U := U) i v]
  by_cases h : siteMarks p m U i v = true
  · rw [if_pos h, h, SwarmMarks.rhoOf_true p]
  · have h' : siteMarks p m U i v = false := by
      cases hb : siteMarks p m U i v with
      | false => rfl
      | true => exact absurd hb h
    rw [if_neg h, h', SwarmMarks.rhoOf_false]
    norm_num

/-- The product form of the truncated forward potential:
`G_N(y) = 1 + ∑_{m<N} ∏_{u≤m} rho(y+u)`. -/
theorem Gtrunc_eq_sum (ω : ℕ → Bool) (N y : ℕ) :
    Gtrunc p ω N y
      = 1 + ∑ m ∈ Finset.range N,
          ∏ u ∈ Finset.range (m + 1), rhoOf p (ω (y + u)) := by
  induction N generalizing y with
  | zero => simp [Gtrunc, Gv_zero]
  | succ k ih =>
      have hshift : ∀ m : ℕ, rhoOf p (ω y) *
            (∏ u ∈ Finset.range (m + 1), rhoOf p (ω (y + 1 + u)))
          = ∏ u ∈ Finset.range (m + 2), rhoOf p (ω (y + u)) := by
        intro m
        rw [Finset.prod_range_succ' (f := fun u => rhoOf p (ω (y + u)))]
        rw [show (∏ u ∈ Finset.range (m + 1), rhoOf p (ω (y + (u + 1))))
              = ∏ u ∈ Finset.range (m + 1), rhoOf p (ω (y + 1 + u)) from
            Finset.prod_congr rfl fun u _ => by rw [show y + (u + 1) = y + 1 + u by ring]]
        simp only [Nat.add_zero, mul_comm]
      rw [Gtrunc_succ, ih (y + 1),
        Finset.sum_range_succ' (f := fun m => ∏ u ∈ Finset.range (m + 1), rhoOf p (ω (y + u)))]
      have h1 : rhoOf p (ω y) *
            (1 + ∑ m ∈ Finset.range k,
              (∏ u ∈ Finset.range (m + 1), rhoOf p (ω (y + 1 + u))))
          = rhoOf p (ω y) + ∑ m ∈ Finset.range k,
              (∏ u ∈ Finset.range (m + 2), rhoOf p (ω (y + u))) := by
        rw [mul_add, mul_one, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun m _ => hshift m
      rw [h1]
      rw [show (∏ u ∈ Finset.range (0 + 1), rhoOf p (ω (y + u))) = rhoOf p (ω y) from by simp]
      ring

/-- `Gsum` is one truncation of `Gsup`: for `x < K`,
`∑_{z∈[x,K)} ∏_{v∈(x,z]} rho = G_{K-1-x}(x+1)`. -/
theorem Gsum_eq_Gtrunc (hp0 : p ≠ 0) (U : Array N) (i : Fin N) {x K : ℕ}
    (hxK : x < K) :
    Gsum p m U i x K = Gtrunc p (siteMarks p m U i) (K - x - 1) (x + 1) := by
  have hsum : Gsum p m U i x K
      = ∑ j ∈ Finset.range (K - x),
          ∏ u ∈ Finset.range j, rhoOf p (siteMarks p m U i (x + 1 + u)) := by
    unfold Gsum
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.prod_Ico_eq_prod_range]
    rw [show x + j + 1 - (x + 1) = j by omega]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [rq_omegaN_eq_rhoOf hp0]
  have hx1 : 1 ≤ K - x := by omega
  have hsplit : K - x = (K - x - 1) + 1 := (Nat.sub_add_cancel hx1).symm
  rw [hsum, Gtrunc_eq_sum, hsplit,
    Finset.sum_range_succ' (f := fun j => ∏ u ∈ Finset.range j,
      rhoOf p (siteMarks p m U i (x + 1 + u)))]
  simp only [Finset.prod_range_zero]
  have hidx : K - x - 1 + 1 - 1 = K - x - 1 := by omega
  rw [hidx]
  ring

/-- **`Gtail` is bounded by `Gsup`**: the finite tail sum is a truncation of `Gsup`. -/
theorem Gtail_le_one_add_Gsup (hp0 : p ≠ 0) (U : Array N) (i : Fin N) (x K : ℕ)
    (hbdd : BddAbove (Set.range fun n => Gtrunc p (siteMarks p m U i) n (x + 1))) :
    Gtail p m U i x K ≤ 1 + Gsup p (siteMarks p m U i) x := by
  rcases Nat.lt_or_ge x K with hxK | hKx
  · have h1 : Gsum p m U i x K
        = Gtrunc p (siteMarks p m U i) (K - x - 1) (x + 1) :=
      Gsum_eq_Gtrunc hp0 U i hxK
    have h2 : Gtrunc p (siteMarks p m U i) (K - x - 1) (x + 1)
        ≤ Gsup p (siteMarks p m U i) x :=
      Gtrunc_le_Gsup (siteMarks p m U i) x (K - x - 1) hbdd
    rw [Gtail, h1]
    linarith
  · have hempty : Finset.Ico x K = ∅ := Finset.Ico_eq_empty_iff.mpr (by omega)
    have h1 : (1 : ℝ) ≤ Gsup p (siteMarks p m U i) x := by
      have h0 : Gtrunc p (siteMarks p m U i) 0 (x + 1) = 1 := by simp [Gtrunc, Gv_zero]
      calc (1 : ℝ) = Gtrunc p (siteMarks p m U i) 0 (x + 1) := h0.symm
        _ ≤ Gsup p (siteMarks p m U i) x := Gtrunc_le_Gsup (siteMarks p m U i) x 0 hbdd
    rw [Gtail, Gsum, hempty, Finset.sum_empty]
    linarith

end SiteWindow

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- **The windowed `GoodW` from the full `(locmax)` event.**  If, on a window covering the level
window `[A-1, xTop]`, both halves of `(locmax)` hold at threshold `H` (`h_j ≤ H` and `G_j ≤ H`),
and `Gsup` is finite, then the windowed good event holds with
`B = max (2H+6) (2(H+1))`.  The shift `H+1` is the definitional normalisation
`SwarmSiteDiff.Gtail = 1 + Gsum`. -/
theorem goodWWin_of_locmax_event {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {A a b : ℕ} {H : ℝ} (hH1 : 1 ≤ H)
    (hA : ∀ i ∈ I, A ≤ (runMax p m U i n).toNat)
    (hLoc : ∀ j : Fin N, ∀ y ∈ Finset.Ico a b,
      hof p (siteMarks p m U j) y ≤ H ∧ Gsup p (siteMarks p m U j) y ≤ H)
    (hcover : ∀ v : ℕ, A ≤ v + 1 →
      v ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U → v ∈ Finset.Ico a b)
    (hbdd : ∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) :
    GoodWWin p m n I J hI (max (2 * H + 6) (2 * (H + 1))) A U := by
  have hpne : p ≠ 0 := by linarith
  have hGnn : (0 : ℝ) ≤ H + 1 := by linarith
  refine goodWWin_of_locmax_window hp0 hp1 I J hI hJ hid hsep hH1 hGnn hA ?_ hcover ?_
  · intro j y hy
    exact (hLoc j y hy).1
  · intro i hi u hu1 hu2
    have hmem := hcover u (by omega) hu2
    have h1 : Gtail p m U i u (n + 2) ≤ 1 + Gsup p (siteMarks p m U i) u :=
      Gtail_le_one_add_Gsup hpne U i u (n + 2) (hbdd i u)
    have h2 : Gsup p (siteMarks p m U i) u ≤ H := (hLoc i u hmem).2
    linarith

end SiteWindow
