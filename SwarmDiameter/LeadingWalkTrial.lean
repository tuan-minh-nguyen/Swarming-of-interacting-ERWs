import Swarm.BlkMeasure
import Swarm.SeedPos

open Filter MeasureTheory Set
open Swarming Swarming.Model Swarming.Trajectory Swarming.Uniform SwarmFresh SwarmRestart
open scoped ENNReal Topology

namespace Swarming.Diameter

/-- The positive-speed bound and positive probability of strict positivity
bound the mass of the finite path event needed for the leading walks. -/
theorem exists_leading_walk_trial_mass_ge {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 ≤ N →
      let μ := arrayMeasure N
      let V := {U : Array N | posPath p m U ∈ strictPos}
      0 < μ V / 2 ∧
        ∀ᶠ t : ℕ in atTop, μ V / 2 ≤ μ {U : Array N |
          (∀ s < t, ∀ i, 0 < posPath p m U (s + 1) i) ∧
            ∀ i, (κ / 2) * (t : ℝ) ≤ (posPath p m U t i : ℝ)} := by
  obtain ⟨κ, hκ, hspeed⟩ := M4Blk.main_claim_direct p m hp₀ hp₁ hm
  refine ⟨κ, hκ, ?_⟩
  intro N hN
  obtain ⟨v, hkv, _, hv⟩ := hspeed N hN
  let μ := arrayMeasure N
  let V := {U : Array N | posPath p m U ∈ strictPos}
  have hV : μ V ≠ 0 := SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN
  refine ⟨ENNReal.div_pos hV (by norm_num), ?_⟩
  let B (j : ℕ) := {U : Array N | ∀ t ≥ j, ∀ i : Fin N,
    (κ / 2) * (t : ℝ) ≤ (posPath p m U t i : ℝ)}
  have hB : ∀ᵐ U ∂μ, U ∈ ⋃ j : ℕ, B j := by
    filter_upwards [hv] with U hU
    have hv' : κ / 2 < v := (by linarith : κ / 2 < κ).trans_le hkv
    have hratio : ∀ᶠ t : ℕ in atTop, ∀ i : Fin N,
        κ / 2 < ((trajectory p m U t).pos i : ℝ) / (t : ℝ) :=
      Filter.eventually_all.mpr fun i => (hU i).eventually (Ioi_mem_nhds hv')
    have hpos : ∀ᶠ t : ℕ in atTop, ∀ i : Fin N,
        (κ / 2) * (t : ℝ) ≤ (posPath p m U t i : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hratio] with t ht h i
      exact ((lt_div_iff₀ (Nat.cast_pos.mpr ht)).mp (h i)).le
    exact Set.mem_iUnion.mpr (eventually_atTop.mp hpos)
  have hmono : Monotone (fun j => V ∩ B j) :=
    fun _ _ h _ hU => ⟨hU.1, fun t ht => hU.2 t (h.trans ht)⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [← Set.inter_iUnion, Set.inter_comm V, Measure.measure_inter_eq_of_ae hB] at hlim
  filter_upwards [hlim.eventually (Ioi_mem_nhds (ENNReal.half_lt_self hV (measure_ne_top μ V)))]
     with t ht
  exact ht.le.trans (measure_mono (fun U hU =>
    ⟨fun s _ i => hU.1.2 s i, hU.2 t le_rfl⟩))

private theorem localTime_eq_of_shifted_path {X Y : ℕ → ℤ} {t k : ℕ} {d x : ℤ}
    (hx : 0 ≤ x) (hbefore : ∀ s < t, X s < d) (hY₀ : Y 0 = 0)
    (hpath : ∀ s ≤ k, X (t + s) = d + Y s) :
    localTime X (t + k) (d + x) = localTime Y k x := by
  induction k with
  | zero =>
    have hXt : X t = d := by simpa [hY₀] using hpath 0 le_rfl
    rw [Nat.add_zero, localTime_zero, hY₀, localTime_def]
    have hfilter : (Finset.range (t + 1)).filter (fun s => X s = d + x) =
        if x = 0 then {t} else ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range]
      by_cases h : s = t
      · subst s
        by_cases hx₀ : x = 0 <;> simp [hXt, hx₀]
      · have hnone : ¬ (s < t + 1 ∧ X s = d + x) := by
          rintro ⟨hst, hsx⟩
          have hs := hbefore s (by omega)
          omega
        by_cases hx₀ : x = 0
        · simp only [hnone, if_pos hx₀, Finset.mem_singleton, h]
        · simp only [hnone, if_neg hx₀, Finset.notMem_empty]
    rw [hfilter]
    by_cases hx₀ : x = 0
    · subst x
      simp
    · simp [hx₀, Ne.symm hx₀]
  | succ k ih =>
    rw [Nat.add_succ, localTime_succ, localTime_succ,
      ih (fun s hs => hpath s (Nat.le_succ_of_le hs))]
    have hs := hpath (k + 1) le_rfl
    rw [Nat.add_succ] at hs
    simp [hs]

/-- The local time of a leading walk above its starting level agrees with
that of the translated walk. -/
theorem leading_localTime_eq {N t k : ℕ} {p : ℝ} {m : ℕ} {d : ℤ}
    {U : Swarming.Uniform.Array (N + 1)} {V : Swarming.Uniform.Array N}
    (hbefore : ∀ s < t, ∀ i : Fin N, posPath p m U s i.castSucc < d)
    (hpath : ∀ s ≤ k, ∀ i : Fin N,
      posPath p m U (t + s) i.castSucc = d + posPath p m V s i)
    (i : Fin N) {x : ℤ} (hx : 0 ≤ x) :
    (trajectory p m U (t + k)).ell i.castSucc (d + x) =
      (trajectory p m V k).ell i x := by
  rw [ell_eq_localTime, ell_eq_localTime]
  exact localTime_eq_of_shifted_path hx (fun s hs => hbefore s hs i)
    rfl (fun s hs => hpath s hs i)

/-- While the last walk has stayed below the starting level of the leading walks,
their right-jump probabilities equal those of the translated smaller system. -/
theorem leading_rightProbability_eq {N t k : ℕ} {p : ℝ} {m : ℕ} {d : ℤ}
    {U : Swarming.Uniform.Array (N + 1)} {V : Swarming.Uniform.Array N}
    (hbefore : ∀ s < t, ∀ i : Fin N, posPath p m U s i.castSucc < d)
    (hpath : ∀ s ≤ k, ∀ i : Fin N,
      posPath p m U (t + s) i.castSucc = d + posPath p m V s i)
    (hlast : ∀ s ≤ t + k, posPath p m U s (Fin.last N) < d)
    (i : Fin N) (hi : 0 ≤ posPath p m V k i) :
    rightProbability p m (trajectory p m U (t + k)).ell i.castSucc
        (posPath p m U (t + k) i.castSucc) =
      rightProbability p m (trajectory p m V k).ell i (posPath p m V k i) := by
  let x := posPath p m V k i
  have hzero : (trajectory p m U (t + k)).ell (Fin.last N) (d + x) = 0 := by
    rw [ell_eq_localTime]
    exact localTime_eq_zero_of_ne _ _ fun s hs => ne_of_lt
      ((hlast s hs).trans_le (by omega))
  have hpos : posPath p m U (t + k) i.castSucc = d + x := hpath k le_rfl i
  have hℓ (j : Fin N) : (trajectory p m U (t + k)).ell j.castSucc (d + x) =
      (trajectory p m V k).ell j x := leading_localTime_eq hbefore hpath j hi
  have hVisits :
      otherVisits (trajectory p m U (t + k)).ell i.castSucc (d + x) =
        otherVisits (trajectory p m V k).ell i x := by
    classical
    simp only [otherVisits, Fin.sum_univ_castSucc, Fin.castSucc_inj,
      hℓ, hzero, ite_self, add_zero]
  rw [hpos]
  change rightProbability p m (trajectory p m U (t + k)).ell i.castSucc (d + x) =
    rightProbability p m (trajectory p m V k).ell i x
  unfold rightProbability Excited
  by_cases h : m ≤ otherVisits (trajectory p m V k).ell i x <;> simp [hVisits, h]

/-- The trailing walk is symmetric throughout its confinement. Each leading
walk visits any site of the confinement interval at most once. -/
theorem trailing_rightProbability_eq_half {N n L k : ℕ} {p : ℝ} {m : ℕ} {r : ℤ}
    {U : Swarming.Uniform.Array (N + 1)} (hm : N + 1 ≤ m)
    (hbefore : ∀ s < n, ∀ i : Fin N, posPath p m U s i.castSucc < r)
    (hprep : ∀ s ≤ 4 * L, ∀ i : Fin N, posPath p m U (n + s) i.castSucc = r + (s : ℤ))
    (hlead : ∀ s, 0 < s → s ≤ k → ∀ i : Fin N,
      r + 4 * (L : ℤ) < posPath p m U (n + 4 * L + s) i.castSucc)
    (hlo : r + (L : ℤ) ≤ posPath p m U (n + 4 * L + k) (Fin.last N))
    (hhi : posPath p m U (n + 4 * L + k) (Fin.last N) ≤ r + 3 * (L : ℤ)) :
    rightProbability p m (trajectory p m U (n + 4 * L + k)).ell (Fin.last N)
      (posPath p m U (n + 4 * L + k) (Fin.last N)) = 1 / 2 := by
  let t := n + 4 * L + k
  let x := posPath p m U t (Fin.last N)
  change r + (L : ℤ) ≤ x at hlo
  change x ≤ r + 3 * (L : ℤ) at hhi
  have hvisit (i : Fin N) {s : ℕ} (hs : s ≤ t) (hsx : posPath p m U s i.castSucc = x) :
      (s : ℤ) + r = (n : ℤ) + x := by
    have hns : n ≤ s := by
      by_contra! h
      have h₁ := hbefore s h i
      omega
    have hs₄ : s ≤ n + 4 * L := by
      by_contra! h
      have hs₀ : 0 < s - (n + 4 * L) := by omega
      have hsk : s - (n + 4 * L) ≤ k := by dsimp only [t] at hs; omega
      have h₁ := hlead (s - (n + 4 * L)) hs₀ hsk i
      rw [Nat.add_sub_of_le h.le, hsx] at h₁
      omega
    have h₁ := hprep (s - n) (by omega) i
    rw [Nat.add_sub_of_le hns, hsx] at h₁
    omega
  have hℓ (i : Fin N) : (trajectory p m U t).ell i.castSucc x ≤ 1 := by
    rw [ell_eq_localTime, localTime_def]
    apply Finset.card_le_one.mpr
    intro s hs u hu
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hs hu
    have h₁ := hvisit i hs.1 hs.2
    have h₂ := hvisit i hu.1 hu.2
    omega
  have hsum : otherVisits (trajectory p m U t).ell (Fin.last N) x ≤ N := by
    classical
    simp only [otherVisits, Fin.sum_univ_castSucc, Fin.castSucc_ne_last, if_false,
      if_true, add_zero]
    simpa using
      (Finset.sum_le_sum (fun i _ => hℓ i) :
        ∑ i : Fin N, (trajectory p m U t).ell i.castSucc x ≤ ∑ _i : Fin N, (1 : ℕ))
  change rightProbability p m (trajectory p m U t).ell (Fin.last N) x = 1 / 2
  unfold rightProbability Excited
  rw [if_neg (by omega)]

end Swarming.Diameter

