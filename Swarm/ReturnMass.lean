/-
# Finite next-record mass from a one-step successor

For any capped state `s` with all positions at most `0`, fair-pattern domination proves
that the first-record mass tends to one. If a chosen walker starts at `1-b`, the
no-record mass is at most `(2b+1) * sqrt 2 / sqrt (L+1)`.
The application is the all-left successor of a simultaneous-record state, where `b = 2`.
-/
import Swarm.MassOne
import Swarm.FreshCyl

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SwarmFinHorizon.Return

open SimJump SimJump.RecKernel SwarmRec

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {N m : ℕ}

noncomputable def hitWState (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (s : State N m) : ℝ := by
  classical
  exact if Record.FirstRecord (Record.extendPath q) k s then pathW p k q s else 0

theorem hitWState_of_firstRecord (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (s : State N m)
    (h : Record.FirstRecord (Record.extendPath q) k s) :
    hitWState p q s = pathW p k q s := by
  classical
  rw [hitWState, if_pos h]

theorem hitWState_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {k : ℕ}
    (q : Fin k → JumpVec N) (s : State N m) : 0 ≤ hitWState p q s := by
  classical
  rw [hitWState]
  split
  · exact pathW_nonneg p hp hp1 k q s
  · exact le_rfl

noncomputable def hitMassState (p : ℝ) (L : ℕ) (s : State N m) : ℝ :=
  ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N, hitWState p q s

noncomputable def avoidMassState (p : ℝ) (L : ℕ) (s : State N m) : ℝ :=
  ∑ q : Fin L → JumpVec N,
    (if NoRecUp q L le_rfl s then (1 : ℝ) else 0) * pathW p L q s

theorem avoidMassState_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (L : ℕ) (s : State N m) : 0 ≤ avoidMassState p L s := by
  rw [avoidMassState]
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (by split_ifs <;> norm_num) (pathW_nonneg p hp hp1 L q s)

theorem avoidMassState_shift (p : ℝ) (L : ℕ) (s : State N m) :
    ∑ q : Fin (L + 1) → JumpVec N,
        (if NoRecUp q L (Nat.le_succ L) s then (1 : ℝ) else 0) * pathW p (L + 1) q s
      = avoidMassState p L s := by
  classical
  set e : ((Fin L → JumpVec N) × JumpVec N) ≃ (Fin (L + 1) → JumpVec N) :=
    (Equiv.prodComm (Fin L → JumpVec N) (JumpVec N)).trans
      (Fin.snocEquiv (fun _ : Fin (L + 1) => JumpVec N)) with he
  have he_apply : ∀ (q : Fin L → JumpVec N) (v : JumpVec N),
      e (q, v) = Fin.snoc (α := fun _ : Fin (L + 1) => JumpVec N) q v := by
    intro q v
    rw [he]
    exact snocPair q v
  rw [← Fintype.sum_equiv e
    (fun qv : (Fin L → JumpVec N) × JumpVec N =>
      (if NoRecUp (e qv) L (Nat.le_succ L) s then (1 : ℝ) else 0)
        * pathW p (L + 1) (e qv) s)
    (fun q : Fin (L + 1) → JumpVec N =>
      (if NoRecUp q L (Nat.le_succ L) s then (1 : ℝ) else 0) * pathW p (L + 1) q s)
    (fun qv => rfl)]
  rw [Fintype.sum_prod_type, avoidMassState]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hiff : ∀ v : JumpVec N,
      NoRecUp (e (q', v)) L (Nat.le_succ L) s ↔ NoRecUp q' L le_rfl s := by
    intro v
    have hst : ∀ (t : ℕ) (ht : t ≤ L),
        stateAt (e (q', v)) t (le_trans ht (Nat.le_succ L)) s = stateAt q' t ht s := by
      intro t ht
      exact stateAt_congr (fun n hn hn' => by rw [he_apply]; exact snoc_apply_lt q' v n hn hn')
        t _ _ _
    constructor
    · intro h t ht i
      exact (hst t ht) ▸ h t ht i
    · intro h t ht i
      rw [hst t ht]
      exact h t ht i
  have hstep : ∀ v : JumpVec N,
      (if NoRecUp (e (q', v)) L (Nat.le_succ L) s then (1 : ℝ) else 0)
        * pathW p (L + 1) (e (q', v)) s
      = (if NoRecUp q' L le_rfl s then (1 : ℝ) else 0)
        * (pathW p L q' s * stepW p m (evolve L q' s) v) := by
    intro v
    have hif : (if NoRecUp (e (q', v)) L (Nat.le_succ L) s then (1 : ℝ) else 0)
        = (if NoRecUp q' L le_rfl s then (1 : ℝ) else 0) := by
      by_cases h : NoRecUp q' L le_rfl s
      · rw [if_pos ((hiff v).mpr h), if_pos h]
      · rw [if_neg (fun hc => h ((hiff v).mp hc)), if_neg h]
    rw [hif, he_apply]
    simp only [pathW, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_congr rfl fun v _ => hstep v]
  rw [← Finset.mul_sum, ← Finset.mul_sum, stepW_sum_one]
  ring

theorem hitMassState_succ (p : ℝ) (L : ℕ) (s : State N m) :
    hitMassState p (L + 1) s = hitMassState p L s
      + ∑ q : Fin (L + 1) → JumpVec N,
          (if Record.FirstRecord (Record.extendPath q) (L + 1) s then (1 : ℝ) else 0)
            * pathW p (L + 1) q s := by
  classical
  rw [hitMassState, Finset.sum_range_succ, hitMassState]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hitWState]
  split_ifs with h <;> simp

theorem hitMassState_add_avoidMassState (p : ℝ) (_hp : 1 / 2 ≤ p) (_hp1 : p ≤ 1)
    (s : State N m) (hs : ∀ i, s.pos i ≤ 0) :
    ∀ L : ℕ, hitMassState p L s + avoidMassState p L s = 1 := by
  intro L
  induction L with
  | zero =>
      have hhit : hitMassState p 0 s = 0 := by
        rw [hitMassState, Finset.sum_range_one]
        have hzero : ∀ q : Fin 0 → JumpVec N, hitWState p q s = 0 := by
          intro q
          rw [hitWState, if_neg]
          intro hcon
          obtain ⟨i, hi⟩ := hcon.1
          have h0 : (evolveFun (Record.extendPath q) 0 s).pos i = s.pos i := rfl
          rw [h0] at hi
          have := hs i
          omega
        simp only [hzero, Finset.sum_const_zero]
      have htrue : NoRecUp (default : Fin 0 → JumpVec N) 0 le_rfl s := by
        intro t ht i
        have ht0 : t = 0 := by omega
        subst ht0
        rw [stateAt_zero]
        exact hs i
      have havoid : avoidMassState p 0 s = 1 := by
        rw [avoidMassState, Finset.sum_eq_single (default : Fin 0 → JumpVec N)]
        · rw [if_pos htrue]
          simp [pathW]
        · intro b _ hb
          exact absurd (funext fun t => t.elim0) hb
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      rw [hhit, havoid]
      norm_num
  | succ L ih =>
      have hcombine :
          ∑ q : Fin (L + 1) → JumpVec N,
              (if Record.FirstRecord (Record.extendPath q) (L + 1) s then (1 : ℝ) else 0)
                * pathW p (L + 1) q s
            + ∑ q : Fin (L + 1) → JumpVec N,
              (if NoRecUp q (L + 1) le_rfl s then (1 : ℝ) else 0) * pathW p (L + 1) q s
          = ∑ q : Fin (L + 1) → JumpVec N,
              (if NoRecUp q L (Nat.le_succ L) s then (1 : ℝ) else 0)
                * pathW p (L + 1) q s := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← add_mul]
        congr 1
        exact indicator_firstRecord (le_rfl : L + 1 ≤ L + 1) hs
      rw [hitMassState_succ, add_assoc,
        show avoidMassState p (L + 1) s
          = ∑ q : Fin (L + 1) → JumpVec N,
              (if NoRecUp q (L + 1) le_rfl s then (1 : ℝ) else 0) * pathW p (L + 1) q s
          from rfl,
        hcombine, avoidMassState_shift p L s, ← ih]

theorem rmax_pattern_lt_of_start {L : ℕ} {q : Fin L → JumpVec N} {s : State N m}
    {i₀ : Fin N} (b : ℕ) (hpos : s.pos i₀ = 1 - (b : ℤ))
    (hno : NoRecUp q L le_rfl s) :
    SwarmReflect.rmax (pattern i₀ q) L < (b : ℤ) := by
  have hkey : ∀ t ≤ L, SwarmReflect.psum (pattern i₀ q) t ≤ -s.pos i₀ := by
    intro t ht
    have h := hno t ht i₀
    rw [pos_stateAt_eq q s i₀ ht] at h
    omega
  have hrmax : ∀ t ≤ L, SwarmReflect.rmax (pattern i₀ q) t ≤ -s.pos i₀ := by
    intro t
    induction t with
    | zero => intro _; simpa [SwarmReflect.rmax] using hkey 0 (Nat.zero_le L)
    | succ t ih =>
        intro ht
        rw [SwarmReflect.rmax_succ]
        exact max_le (ih (by omega)) (hkey (t + 1) (by omega))
  have h := hrmax L le_rfl
  rw [hpos] at h
  omega

theorem avoidMassState_le_count (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (L : ℕ) (s : State N m) {i₀ : Fin N} (b : ℕ)
    (hpos : s.pos i₀ = 1 - (b : ℤ)) :
    avoidMassState p L s ≤ (1 / 2 : ℝ) ^ L *
      ((Finset.univ.filter (fun π : Pattern L => SwarmReflect.rmax π L < (b : ℤ))).card : ℝ) := by
  classical
  set D : Pattern L → Prop := fun π => SwarmReflect.rmax π L < (b : ℤ) with hD
  have hmono : ∀ π π' : Pattern L, PatLe π π' → (if D π' then (1 : ℝ) else 0)
      ≤ (if D π then (1 : ℝ) else 0) := by
    intro π π' hle
    by_cases h : D π
    · rw [if_pos h]
      split_ifs <;> norm_num
    · have h' : ¬ D π' := by
        intro hc
        exact h (lt_of_le_of_lt (rmax_mono_pat hle L) hc)
      rw [if_neg h, if_neg h']
  have hdom := patMass_le_halfAvg p hp hp1 i₀ L (fun π => if D π then (1 : ℝ) else 0) hmono s
  have hpt : ∀ q : Fin L → JumpVec N,
      (if NoRecUp q L le_rfl s then (1 : ℝ) else 0) * pathW p L q s
        ≤ (if D (pattern i₀ q) then (1 : ℝ) else 0) * pathW p L q s := by
    intro q
    by_cases h : NoRecUp q L le_rfl s
    · rw [if_pos h, if_pos (rmax_pattern_lt_of_start b hpos h)]
    · rw [if_neg h]
      have hnn : (0 : ℝ) ≤ (if D (pattern i₀ q) then (1 : ℝ) else 0) := by
        by_cases hd : D (pattern i₀ q) <;> simp [hd]
      exact mul_le_mul_of_nonneg_right hnn (pathW_nonneg p hp hp1 L q s)
  have hcard : ∑ π : Pattern L, (if D π then (1 : ℝ) else 0)
      = ((Finset.univ.filter D).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [avoidMassState]
  refine le_trans (Finset.sum_le_sum fun q _ => hpt q) (le_trans hdom ?_)
  unfold halfAvg
  rw [hcard]

theorem avoidMassState_le_sqrt (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (L : ℕ) (s : State N m) {i₀ : Fin N} {b : ℕ} (hb : 1 ≤ b)
    (hpos : s.pos i₀ = 1 - (b : ℤ)) :
    avoidMassState p L s ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1) := by
  classical
  refine le_trans (avoidMassState_le_count p hp hp1 L s b hpos) ?_
  have hcard := SwarmReflect.card_rmax_lt_le_sqrt (n := L) hb
  have hnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ L := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hcard hnonneg) ?_
  have h2 : ((1 : ℝ) / 2) ^ L * 2 ^ L = 1 := by
    rw [← mul_pow]
    norm_num
  have heq : (1 / 2 : ℝ) ^ L *
        ((2 * (b : ℝ) + 1) * Real.sqrt 2 * 2 ^ L / Real.sqrt ((L : ℝ) + 1))
      = ((2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) *
        (((1 : ℝ) / 2) ^ L * 2 ^ L) := by
    ring
  rw [heq, h2, mul_one]

theorem tendsto_avoidMassState (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (s : State N m) {i₀ : Fin N} {b : ℕ} (hb : 1 ≤ b)
    (hpos : s.pos i₀ = 1 - (b : ℤ)) :
    Tendsto (fun L : ℕ => avoidMassState p L s) atTop (𝓝 0) := by
  have hsq : Tendsto (fun L : ℕ => Real.sqrt ((L : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun L : ℕ => (Real.sqrt ((L : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hsq.inv_tendsto_atTop
  have hbound : Tendsto (fun L : ℕ =>
      (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (2 * (b : ℝ) + 1) * Real.sqrt 2)
      (f := (atTop : Filter ℕ))).mul hinv
    simpa [div_eq_mul_inv] using h
  exact squeeze_zero (fun L => avoidMassState_nonneg p hp hp1 L s)
    (fun L => avoidMassState_le_sqrt p hp hp1 L s hb hpos) hbound

theorem tendsto_hitMassState (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (s : State N m) (hs : ∀ i, s.pos i ≤ 0) {i₀ : Fin N} {b : ℕ} (hb : 1 ≤ b)
    (hpos : s.pos i₀ = 1 - (b : ℤ)) :
    Tendsto (fun L : ℕ => hitMassState p L s) atTop (𝓝 1) := by
  have hav := tendsto_avoidMassState p hp hp1 s hb hpos
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hav
  have heq : (fun L : ℕ => hitMassState p L s) = (fun L : ℕ => 1 - avoidMassState p L s) := by
    funext L
    have hsum := hitMassState_add_avoidMassState p hp hp1 s hs L
    linarith
  rw [heq]
  simpa using h

noncomputable def recTermState (p : ℝ) (k : ℕ) (s : State N m) : ℝ :=
  ∑ q : Fin k → JumpVec N, hitWState p q s

theorem hitMassState_eq_sum_range (p : ℝ) (L : ℕ) (s : State N m) :
    hitMassState p L s = ∑ k ∈ Finset.range (L + 1), recTermState p k s := rfl

theorem recTermState_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (s : State N m) : 0 ≤ recTermState p k s :=
  Finset.sum_nonneg fun q _ => hitWState_nonneg p hp hp1 q s

theorem hasSum_recTermState (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (s : State N m) (hs : ∀ i, s.pos i ≤ 0) {i₀ : Fin N} {b : ℕ} (hb : 1 ≤ b)
    (hpos : s.pos i₀ = 1 - (b : ℤ)) :
    HasSum (fun k => recTermState p k s) 1 := by
  have hnn : ∀ k, 0 ≤ recTermState p k s := fun k => recTermState_nonneg p hp hp1 k s
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hshift : Tendsto (fun L : ℕ => ∑ k ∈ Finset.range (L + 1), recTermState p k s)
      atTop (𝓝 1) := by
    simpa [hitMassState_eq_sum_range] using tendsto_hitMassState p hp hp1 s hs hb hpos
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  simpa using hshift

/-- The horizon-free first-record weights from a general below-record state have
exactly unit mass. -/
theorem tsum_hitWState_ofReal_eq_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (s : State N m) (hs : ∀ i, s.pos i ≤ 0) {i₀ : Fin N} {b : ℕ} (hb : 1 ≤ b)
    (hpos : s.pos i₀ = 1 - (b : ℤ)) :
    ∑' pq : (k : ℕ) × (Fin k → JumpVec N), ENNReal.ofReal (hitWState p pq.2 s) = 1 := by
  classical
  rw [ENNReal.tsum_sigma']
  have hinner : ∀ k : ℕ, (∑' q : Fin k → JumpVec N, ENNReal.ofReal (hitWState p q s))
      = ENNReal.ofReal (recTermState p k s) := by
    intro k
    rw [recTermState, ENNReal.ofReal_sum_of_nonneg
      (fun q _ => hitWState_nonneg p hp hp1 q s)]
    exact tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi)
  simp only [hinner]
  have hsum : Summable (fun k => recTermState p k s) :=
    (hasSum_recTermState p hp hp1 s hs hb hpos).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => recTermState_nonneg p hp hp1 k s) hsum,
    (hasSum_recTermState p hp hp1 s hs hb hpos).tsum_eq]
  simp

/-- If the starting state is already at the record threshold, the stopped word
law is the time-zero atom. -/
theorem tsum_hitWState_ofReal_eq_one_of_rec_now (p : ℝ) (s : State N m)
    {i₀ : Fin N} (hi₀ : s.pos i₀ = 1) :
    ∑' pq : (k : ℕ) × (Fin k → JumpVec N), ENNReal.ofReal (hitWState p pq.2 s) = 1 := by
  classical
  let q0 : Fin 0 → JumpVec N := fun i => i.elim0
  let pq0 : (k : ℕ) × (Fin k → JumpVec N) := ⟨0, q0⟩
  have hfr0 : Record.FirstRecord (Record.extendPath q0) 0 s := by
    refine ⟨⟨i₀, hi₀⟩, ?_⟩
    intro t ht
    exact (Nat.not_lt_zero t ht).elim
  calc
    ∑' pq : (k : ℕ) × (Fin k → JumpVec N), ENNReal.ofReal (hitWState p pq.2 s)
        = ENNReal.ofReal (hitWState p pq0.2 s) := by
          refine tsum_eq_single pq0 ?_
          rintro ⟨k, q⟩ hpq
          by_cases hfr : Record.FirstRecord (Record.extendPath q) k s
          · by_cases hk : k = 0
            · subst k
              have heq : (⟨0, q⟩ : (k : ℕ) × (Fin k → JumpVec N)) = pq0 := by
                have hq : q = q0 := Subsingleton.elim _ _
                change (⟨0, q⟩ : (k : ℕ) × (Fin k → JumpVec N)) = ⟨0, q0⟩
                rw [hq]
              exact (hpq heq).elim
            · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
              have hle := hfr.2 0 hkpos i₀
              have hs0 : (evolveFun (Record.extendPath q) 0 s).pos i₀ = s.pos i₀ := rfl
              rw [hs0, hi₀] at hle
              omega
          · simp [hitWState, hfr]
    _ = 1 := by
      rw [hitWState_of_firstRecord p pq0.2 s hfr0]
      change ENNReal.ofReal (pathW p 0 q0 s) = 1
      rw [show pathW p 0 q0 s = 1 from rfl]
      simp

theorem pos_step_allLeft {z : RecState N m} (hz : z ∈ srSet N m) (v : JumpVec N)
    (hv : ∀ i, v i = false) (i : Fin N) :
    (step m (Record.ofRecState z) v).pos i = -1 := by
  rw [step_pos, stepPos, SwarmFreshCyl.ofRecState_pos_eq_zero hz i, hv i]
  simp

theorem tendsto_hitMassState_step_allLeft (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {z : RecState N m} (hz : z ∈ srSet N m) (v : JumpVec N) (hv : ∀ i, v i = false)
    (i₀ : Fin N) :
    Tendsto (fun L : ℕ => hitMassState p L (step m (Record.ofRecState z) v)) atTop (𝓝 1) := by
  have hpos : (step m (Record.ofRecState z) v).pos i₀ = 1 - (2 : ℕ) := by
    rw [pos_step_allLeft hz v hv]
    norm_num
  exact tendsto_hitMassState p hp hp1 _ (fun i => by rw [pos_step_allLeft hz v hv]; norm_num)
    (by norm_num) hpos

/-- Unit continuation mass, in the same countable word-indexed form used by the
first-letter factorisation. -/
theorem tsum_hitWState_ofReal_step_allLeft (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {z : RecState N m} (hz : z ∈ srSet N m) (v : JumpVec N) (hv : ∀ i, v i = false)
    (i₀ : Fin N) :
    ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (hitWState p pq.2 (step m (Record.ofRecState z) v)) = 1 := by
  have hpos : (step m (Record.ofRecState z) v).pos i₀ = 1 - (2 : ℕ) := by
    rw [pos_step_allLeft hz v hv]
    norm_num
  exact tsum_hitWState_ofReal_eq_one p hp hp1 _
    (fun i => by rw [pos_step_allLeft hz v hv]; norm_num) (by norm_num) hpos

/-- **Unit finite-return mass from every actual one-step successor.**  If all first
jumps are left this is the `b=2` fair-walk estimate; otherwise the successor is
already at the record level and the continuation stops at time zero. -/
theorem tsum_hitWState_ofReal_step (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) {z : RecState N m} (hz : z ∈ srSet N m) (v : JumpVec N) :
    ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (hitWState p pq.2 (step m (Record.ofRecState z) v)) = 1 := by
  classical
  by_cases hv : ∀ i, v i = false
  · obtain ⟨i₀, _⟩ := (Record.ofRecState_recordStart z hm).exists_zero
    exact tsum_hitWState_ofReal_step_allLeft p hp hp1 hz v hv i₀
  · push Not at hv
    obtain ⟨i₀, hi₀⟩ := hv
    have hvi : v i₀ = true := by
      cases h : v i₀ <;> simp_all
    apply tsum_hitWState_ofReal_eq_one_of_rec_now p _ (i₀ := i₀)
    rw [step_pos, stepPos, SwarmFreshCyl.ofRecState_pos_eq_zero hz i₀, hvi]
    simp

end SwarmFinHorizon.Return
