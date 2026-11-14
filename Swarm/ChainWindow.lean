/-
# Window laws of a stationary Markov chain

Let `β` be a measurable space, `μ` a probability measure on `β` and `κ : Kernel β β` a Markov
kernel with `μ` invariant (`μ.bind κ = μ`).  This file constructs the law of the chain
`x 0, x 1, x 2, …` on every finite window of `ℤ` and proves:

* probability,
* projectivity (`IsProjectiveMeasureFamily`),
* shift stationarity (`P (I + k) = (P I).map (winReindex k I)`),

so that `SwarmKolNC.exists_stationary_isProjectiveLimit_recState` produces a shift-invariant
probability on `ℤ → β` with exactly these window laws.

Mathematically the whole content is: for a chain with invariant start law, *the law of
`(x 1, …, x n)` is the law of `(x 0, …, x (n-1))`*.  Everything else is bookkeeping.
-/
import Swarm.Imports

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmChain

variable {β : Type*} [MeasurableSpace β]

/-! ## Vectors, appending and coordinates -/

/-- Append a coordinate at the end of a vector. -/
def snocF {m : ℕ} (v : Fin m → β) (b : β) : Fin (m + 1) → β :=
  fun i => if h : (i : ℕ) < m then v ⟨i.1, h⟩ else b

/-- The first `m` coordinates of a vector of length `m + 1`. -/
def initF {m : ℕ} (v : Fin (m + 1) → β) : Fin m → β := fun i => v i.castSucc

/-- The coordinates `1, …, m` of a vector of length `m + 1`. -/
def tailF {m : ℕ} (v : Fin (m + 1) → β) : Fin m → β := fun i => v i.succ

/-- The first `n` coordinates of a vector of length `N`, for `n ≤ N`. -/
def truncF {N n : ℕ} (h : n ≤ N) (v : Fin N → β) : Fin n → β :=
  fun i => v ⟨i.1, lt_of_lt_of_le i.2 h⟩

@[simp] theorem snocF_castSucc {m : ℕ} (v : Fin m → β) (b : β) (j : Fin m) :
    snocF v b j.castSucc = v j := by simp [snocF]

@[simp] theorem snocF_last {m : ℕ} (v : Fin m → β) (b : β) :
    snocF v b (Fin.last m) = b := by simp [snocF]

@[simp] theorem initF_snocF {m : ℕ} (v : Fin m → β) (b : β) : initF (snocF v b) = v := by
  funext i; simp [initF]

theorem tailF_snocF {m : ℕ} (v : Fin (m + 1) → β) (b : β) :
    tailF (snocF v b) = snocF (tailF v) b := by
  funext i
  by_cases h : (i : ℕ) < m
  · have h1 : ((i.succ : Fin (m + 2)) : ℕ) < m + 1 := by simp; omega
    simp only [tailF, snocF]
    rw [dif_pos h1, dif_pos h]
    congr 2
  · have him : (i : ℕ) = m := by have := i.2; omega
    have hi : i = Fin.last m := Fin.ext him
    subst hi
    simp [tailF, snocF, Fin.val_last]

/-- `truncF` composed with an append is the truncation of the first coordinate. -/
theorem truncF_snocF {m n : ℕ} (h : n ≤ m + 1) (v : Fin (m + 1) → β) (b : β) :
    truncF (N := m + 2) (n := n) (by omega) (snocF v b)
      = truncF (N := m + 1) (n := n) h v := by
  funext i
  have hi : (i : ℕ) < m + 1 := lt_of_lt_of_le i.2 h
  simp [truncF, snocF, hi]

/-- Truncation to the full length is the identity map. -/
theorem truncF_self {n : ℕ} (v : Fin n → β) :
    truncF (N := n) (n := n) le_rfl v = v := by
  funext i; simp [truncF]

/-! ## Measurability of the coordinate maps -/

theorem measurable_snocF {m : ℕ} :
    Measurable fun p : (Fin m → β) × β => snocF p.1 p.2 := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : (i : ℕ) < m
  · have hfun : (fun p : (Fin m → β) × β => snocF p.1 p.2 i) = fun p => p.1 ⟨i.1, h⟩ := by
      funext p; simp [snocF, h]
    rw [hfun]
    exact (measurable_pi_apply _).comp measurable_fst
  · have hfun : (fun p : (Fin m → β) × β => snocF p.1 p.2 i) = fun p => p.2 := by
      funext p; simp [snocF, h]
    rw [hfun]
    exact measurable_snd

theorem measurable_initF {m : ℕ} : Measurable fun v : Fin (m + 1) → β => initF v := by
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_pi_apply _

theorem measurable_tailF {m : ℕ} : Measurable fun v : Fin (m + 1) → β => tailF v := by
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_pi_apply _

theorem measurable_truncF {N n : ℕ} (h : n ≤ N) :
    Measurable (truncF (β := β) (N := N) (n := n) h) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_pi_apply _

theorem measurable_shiftIdx {N n d : ℕ} (h : n + d ≤ N) :
    Measurable fun v : Fin N → β =>
      (fun i : Fin n => v ⟨i.1 + d, by omega⟩ : Fin n → β) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- Two probability measures on a subsingleton measurable space coincide. -/
theorem eq_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  refine Measure.ext fun s _ => ?_
  have h : s = Set.univ ∨ s = ∅ := by
    by_cases hs : ∃ b, b ∈ s
    · left
      obtain ⟨b, hb⟩ := hs
      exact Set.eq_univ_of_forall fun c => by
        have : c = b := Subsingleton.elim c b
        rwa [this]
    · right
      exact Set.eq_empty_of_forall_notMem fun b hb => hs ⟨b, hb⟩
  rcases h with h | h <;> rw [h] <;> simp

/-- Two probability measures pushing into a subsingleton space coincide. -/
theorem map_eq_of_subsingleton {α' : Type*} [MeasurableSpace α'] [Subsingleton α']
    {μ : Measure β} [IsProbabilityMeasure μ] (f : β → α') (hf : Measurable f)
    (ν : Measure α') [IsProbabilityMeasure ν] : μ.map f = ν := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  exact eq_of_subsingleton _ _

/-! ## The chain vectors -/

/-- The kernel "apply `κ` to the last coordinate" on vectors of length `n + 1`. -/
noncomputable def lastK (κ : Kernel β β) (n : ℕ) : Kernel (Fin (n + 1) → β) β :=
  κ.comap (fun w : Fin (n + 1) → β => w (Fin.last n)) (measurable_pi_apply _)

theorem lastK_apply (κ : Kernel β β) (n : ℕ) (w : Fin (n + 1) → β) :
    lastK κ n w = κ (w (Fin.last n)) := rfl

instance (κ : Kernel β β) [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (lastK κ n) := by
  unfold lastK; infer_instance

/-- The law of `(x 0, …, x n)` (a vector of length `n + 1`). -/
noncomputable def chainStep (μ : Measure β) (κ : Kernel β β) : (n : ℕ) → Measure (Fin (n + 1) → β)
  | 0 => μ.map (fun b => fun _ : Fin 1 => b)
  | n + 1 => ((chainStep μ κ n) ⊗ₘ lastK κ n).map
      (fun p : (Fin (n + 1) → β) × β => snocF p.1 p.2)

/-- The law of `(x 0, …, x (n-1))` (a vector of length `n`). -/
noncomputable def chainVec (μ : Measure β) (κ : Kernel β β) (n : ℕ) : Measure (Fin n → β) :=
  match n with
  | 0 => Measure.dirac (fun i => i.elim0)
  | k + 1 => chainStep μ κ k

@[simp] theorem chainVec_zero (μ : Measure β) (κ : Kernel β β) :
    chainVec μ κ 0 = Measure.dirac (fun i => i.elim0) := rfl

theorem chainVec_succ (μ : Measure β) (κ : Kernel β β) (n : ℕ) :
    chainVec μ κ (n + 1) = chainStep μ κ n := rfl

theorem chainStep_zero (μ : Measure β) (κ : Kernel β β) :
    chainStep μ κ 0 = μ.map (fun b => fun _ : Fin 1 => b) := rfl

theorem chainStep_succ (μ : Measure β) (κ : Kernel β β) (n : ℕ) :
    chainStep μ κ (n + 1) = ((chainStep μ κ n) ⊗ₘ lastK κ n).map
      (fun p : (Fin (n + 1) → β) × β => snocF p.1 p.2) := rfl

theorem chainVec_succ_succ (μ : Measure β) (κ : Kernel β β) (n : ℕ) :
    chainVec μ κ (n + 2) = ((chainVec μ κ (n + 1)) ⊗ₘ lastK κ n).map
      (fun p : (Fin (n + 1) → β) × β => snocF p.1 p.2) := by
  rw [chainVec_succ, chainVec_succ, chainStep_succ]

instance isProbabilityMeasure_chainStep (μ : Measure β) [IsProbabilityMeasure μ]
    (κ : Kernel β β) [IsMarkovKernel κ] :
    ∀ n, IsProbabilityMeasure (chainStep μ κ n)
  | 0 => by rw [chainStep_zero]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  | n + 1 => by
      haveI := isProbabilityMeasure_chainStep μ κ n
      rw [chainStep_succ]
      haveI : IsProbabilityMeasure (chainStep μ κ n ⊗ₘ lastK κ n) :=
        ⟨by rw [Measure.compProd_apply_univ, measure_univ]⟩
      exact Measure.isProbabilityMeasure_map measurable_snocF.aemeasurable

instance isProbabilityMeasure_chainVec (μ : Measure β) [IsProbabilityMeasure μ]
    (κ : Kernel β β) [IsMarkovKernel κ] :
    ∀ n, IsProbabilityMeasure (chainVec μ κ n)
  | 0 => by rw [chainVec_zero]; infer_instance
  | n + 1 => isProbabilityMeasure_chainStep μ κ n


/-! ## Naturality of `compProd` in its left argument

If the kernel `κ` factors through a measurable map `f` of the state space, then pushing a
`compProd` forward along `Prod.map f id` only changes the measure.  This is the only
`compProd` manipulation used below and it replaces the missing `Measure.compProd_map_left`. -/

theorem compProd_map_left {α α' γ : Type*} [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] (κ : Kernel α γ) [IsSFiniteKernel κ]
    (f : α → α') (hf : Measurable f) (κ' : Kernel α' γ) [IsSFiniteKernel κ']
    (hκ : ∀ a, κ a = κ' (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f id) = (μ.map f) ⊗ₘ κ' := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply (hs := (hf.prodMap measurable_id) hs), Measure.compProd_apply hs,
    lintegral_map (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun a => ?_
  rw [hκ a]
  congr 2

/-! ## The one-step shift: the law of `(x 1, …, x M)` is the law of `(x 0, …, x (M-1))` -/

/-- The map sending a point to the constant `1`-vector. -/
theorem measurable_fin1_const : Measurable (fun b : β => fun _ : Fin 1 => b) :=
  measurable_pi_lambda _ fun _ => measurable_id

/-- The composite `tailF ∘ snocF` on pairs of a `1`-vector and a point: forget the vector. -/
theorem tailF_snocF_zero :
    ((fun v : Fin 2 → β => tailF v) ∘ fun p : (Fin 1 → β) × β => snocF p.1 p.2)
      = fun p : (Fin 1 → β) × β => fun _ : Fin 1 => p.2 := by
  funext p
  simp only [Function.comp_apply]
  rw [tailF_snocF (m := 0)]
  funext i
  have hi : i = (0 : Fin 1) := Fin.ext (by have := i.2; omega)
  subst hi
  simp [snocF]

/-- The one-step shift `(x 0, …, x n) ↦ (x 1, …, x n)` does not change the joint law when the
start law is invariant.  This is the mathematical content of the whole file. -/
theorem chainStep_shift (μ : Measure β) [IsProbabilityMeasure μ] (κ : Kernel β β)
    [IsMarkovKernel κ] (hμ : μ.bind κ = μ) :
    ∀ M, (chainStep μ κ M).map tailF = chainVec μ κ M
  | 0 => by
      rw [chainVec_zero]
      haveI : IsProbabilityMeasure ((chainStep μ κ 0).map tailF) :=
        Measure.isProbabilityMeasure_map measurable_tailF.aemeasurable
      exact eq_of_subsingleton _ _
  | 1 => by
      have hdet : (lastK κ 0) ∘ₖ Kernel.deterministic (fun b => fun _ : Fin 1 => b)
          measurable_fin1_const = κ := by
        refine Kernel.ext fun b => ?_
        rw [Kernel.comp_apply, Kernel.deterministic_apply,
          Measure.dirac_bind (Kernel.measurable (lastK κ 0))]
        rfl
      have key : (lastK κ 0) ∘ₘ chainStep μ κ 0 = μ := by
        rw [chainStep_zero, ← Measure.deterministic_comp_eq_map (f := fun b => fun _ : Fin 1 => b)
          measurable_fin1_const, Measure.comp_assoc, hdet, hμ]
      calc (chainStep μ κ 1).map tailF
          = (chainStep μ κ 0 ⊗ₘ lastK κ 0).map
              ((fun v : Fin 2 → β => tailF v) ∘ fun p : (Fin 1 → β) × β => snocF p.1 p.2) := by
            rw [chainStep_succ, Measure.map_map measurable_tailF measurable_snocF]
        _ = (chainStep μ κ 0 ⊗ₘ lastK κ 0).map
              (fun p : (Fin 1 → β) × β => fun _ : Fin 1 => p.2) := by rw [tailF_snocF_zero]
        _ = ((chainStep μ κ 0 ⊗ₘ lastK κ 0).map Prod.snd).map
              (fun b => fun _ : Fin 1 => b) :=
            (Measure.map_map measurable_fin1_const measurable_snd).symm
        _ = ((lastK κ 0) ∘ₘ chainStep μ κ 0).map (fun b => fun _ : Fin 1 => b) := by
            congr 1
            exact Measure.snd_compProd (chainStep μ κ 0) (lastK κ 0)
        _ = chainStep μ κ 0 := by rw [key, chainStep_zero]
        _ = chainVec μ κ 1 := (chainVec_succ μ κ 0).symm
  | m + 2 => by
      have hcomp :
          ((fun v : Fin (m + 3) → β => tailF v) ∘ fun p : (Fin (m + 2) → β) × β => snocF p.1 p.2)
            = (fun q : (Fin (m + 1) → β) × β => snocF q.1 q.2)
                ∘ (Prod.map (fun v : Fin (m + 2) → β => tailF v) id) := by
        funext p
        exact tailF_snocF (m := m + 1) p.1 p.2
      have hker : ∀ w : Fin (m + 2) → β, lastK κ (m + 1) w = lastK κ m (tailF w) := by
        intro w
        simp only [lastK_apply, tailF]
        rfl
      calc (chainStep μ κ (m + 2)).map tailF
          = (chainStep μ κ (m + 1) ⊗ₘ lastK κ (m + 1)).map
              ((fun v : Fin (m + 3) → β => tailF v)
                ∘ fun p : (Fin (m + 2) → β) × β => snocF p.1 p.2) := by
            rw [chainStep_succ, Measure.map_map measurable_tailF measurable_snocF]
        _ = ((chainStep μ κ (m + 1) ⊗ₘ lastK κ (m + 1)).map
              (Prod.map (fun v : Fin (m + 2) → β => tailF v) id)).map
              (fun q : (Fin (m + 1) → β) × β => snocF q.1 q.2) := by
            rw [hcomp, Measure.map_map measurable_snocF
              (measurable_tailF.prodMap measurable_id)]
        _ = (((chainStep μ κ (m + 1)).map tailF) ⊗ₘ lastK κ m).map
              (fun q : (Fin (m + 1) → β) × β => snocF q.1 q.2) := by
            rw [compProd_map_left (μ := chainStep μ κ (m + 1)) (κ := lastK κ (m + 1))
              (f := fun v : Fin (m + 2) → β => tailF v) measurable_tailF
              (κ' := lastK κ m) hker]
        _ = chainStep μ κ (m + 1) := by
            rw [chainStep_shift μ κ hμ (m + 1), chainVec_succ, chainStep_succ]
        _ = chainVec μ κ (m + 2) := (chainVec_succ μ κ (m + 1)).symm

/-! ## Truncation: the first `n` coordinates of a chain vector -/

theorem chainVec_trunc (μ : Measure β) [IsProbabilityMeasure μ] (κ : Kernel β β)
    [IsMarkovKernel κ] :
    ∀ (M n : ℕ) (h : n ≤ M + 1), (chainStep μ κ M).map (truncF h) = chainVec μ κ n
  | 0, 0, h => by
      rw [chainVec_zero]
      exact map_eq_of_subsingleton (truncF (β := β) (N := 1) (n := 0) h)
        (measurable_truncF (β := β) h) _
  | 0, 1, h => by
      rw [chainVec_succ, chainStep_zero]
      have hid : truncF (β := β) (N := 1) (n := 1) h = id := funext fun v => truncF_self v
      rw [hid, Measure.map_id]
  | 0, n + 2, h => by omega
  | M + 1, 0, h => by
      rw [chainVec_zero]
      exact map_eq_of_subsingleton (truncF (β := β) (N := M + 2) (n := 0) h)
        (measurable_truncF (β := β) h) _
  | M + 1, m + 1, h => by
      by_cases hm : m = M + 1
      · subst hm
        rw [chainVec_succ]
        have hid : truncF (β := β) (N := M + 2) (n := M + 2) h = id :=
          funext fun v => truncF_self v
        rw [hid, Measure.map_id]
      · have h' : m + 1 ≤ M + 1 := by omega
        rw [chainStep_succ, Measure.map_map (measurable_truncF h) measurable_snocF]
        have hfun : (truncF (β := β) (N := M + 2) (n := m + 1) h) ∘
            (fun p : (Fin (M + 1) → β) × β => snocF p.1 p.2)
              = (truncF (β := β) (N := M + 1) (n := m + 1) h') ∘ Prod.fst := by
          funext p
          exact truncF_snocF (m := M) (n := m + 1) h' p.1 p.2
        rw [hfun, ← Measure.map_map (measurable_truncF h') measurable_fst, ← Measure.fst,
          Measure.fst_compProd]
        exact chainVec_trunc μ κ M (m + 1) h'

/-! ## Reading a later window of a longer chain -/

theorem chainVec_shiftD (μ : Measure β) [IsProbabilityMeasure μ] (κ : Kernel β β)
    [IsMarkovKernel κ] (hμ : μ.bind κ = μ) :
    ∀ (d N n : ℕ) (h : n + d ≤ N),
      (chainVec μ κ N).map (fun v : Fin N → β => fun i : Fin n => v ⟨i.1 + d, by omega⟩)
        = chainVec μ κ n
  | 0, N, n, h => by
      have hfun : (fun v : Fin N → β => fun i : Fin n => v ⟨i.1 + 0, by omega⟩)
          = truncF (β := β) (N := N) (n := n) (by omega) := by
        funext v i
        exact congrArg v (Fin.ext (by simp))
      rw [hfun]
      cases N with
      | zero =>
          have hn : n = 0 := by omega
          subst hn
          rw [chainVec_zero]
          exact map_eq_of_subsingleton (truncF (β := β) (N := 0) (n := 0) (by omega))
            (measurable_truncF (β := β) _) _
      | succ M =>
          rw [chainVec_succ]
          exact chainVec_trunc μ κ M n (by omega)
  | d + 1, N, n, h => by
      cases N with
      | zero => omega
      | succ M =>
          rw [chainVec_succ]
          have hfun : (fun v : Fin (M + 1) → β => fun i : Fin n => v ⟨i.1 + (d + 1), by omega⟩)
              = (fun w : Fin M → β => fun i : Fin n => w ⟨i.1 + d, by omega⟩) ∘ tailF := by
            funext v i
            simp only [Function.comp_apply, tailF]
            congr 1
          rw [hfun, ← Measure.map_map (g := fun w : Fin M → β => fun i : Fin n =>
            w ⟨i.1 + d, by omega⟩) (measurable_shiftIdx (by omega)) measurable_tailF,
            chainStep_shift μ κ hμ M]
          exact chainVec_shiftD μ κ hμ d M n (by omega)

/-! ## Window laws on finite sets of integer times -/

section Window

variable (μ : Measure β) [IsProbabilityMeasure μ] (κ : Kernel β β) [IsMarkovKernel κ]
  (hinv : μ.bind κ = μ)

/-- The length of the span of a nonempty window. -/
noncomputable def winLen (I : Finset ℤ) (h : I.Nonempty) : ℕ := (I.max' h - I.min' h).toNat + 1

theorem winOff_lt (I : Finset ℤ) (h : I.Nonempty) (i : I) :
    (((i : ℤ) - I.min' h)).toNat < winLen I h := by
  have hA : (0 : ℤ) ≤ I.max' h - I.min' h := by
    have := Finset.min'_le I (I.max' h) (Finset.max'_mem I h); omega
  have hdef : winLen I h = (I.max' h - I.min' h + 1).toNat := by
    rw [winLen, Int.toNat_add hA (by norm_num : (0:ℤ) ≤ 1), Int.toNat_one]
  have h3 : 0 < I.max' h - I.min' h + 1 := by omega
  rw [hdef]
  exact (Int.toNat_lt_toNat (n := (i : ℤ) - I.min' h)
    (m := I.max' h - I.min' h + 1) h3).mpr (by
      have := Finset.le_max' I (i : ℤ) i.2
      have := Finset.min'_le I (i : ℤ) i.2
      omega)

/-- The offset of a point of a nonempty window from its left end. -/
noncomputable def winOff (I : Finset ℤ) (h : I.Nonempty) (i : I) : Fin (winLen I h) :=
  ⟨(((i : ℤ) - I.min' h)).toNat, winOff_lt I h i⟩

/-- Measurability of the coordinate projection defining a nonempty window law. -/
theorem measurable_winProj (I : Finset ℤ) (h : I.Nonempty) :
    Measurable (fun v : Fin (winLen I h) → β => fun i : I => v (winOff I h i)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

theorem map_map' {α γ δ : Type*} [MeasurableSpace α] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (f : α → γ) (g : γ → δ) (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).map g = μ.map (g ∘ f) := Measure.map_map hg hf

/-- The law of the chain on a nonempty window. -/
noncomputable def winLawOf (I : Finset ℤ) (h : I.Nonempty) : Measure (Π i : I, β) :=
  (chainVec μ κ (winLen I h)).map (fun v => fun i : I => v (winOff I h i))

/-- The law of the chain on an arbitrary finite window of integer times. -/
noncomputable def winLaw (I : Finset ℤ) : Measure (Π i : I, β) :=
  if h : I.Nonempty then winLawOf μ κ I h
  else Measure.dirac (fun i : I => (h ⟨i.1, i.2⟩).elim)

theorem winLaw_eq (I : Finset ℤ) (h : I.Nonempty) : winLaw μ κ I = winLawOf μ κ I h := by
  rw [winLaw, dif_pos h]

instance isProbabilityMeasure_winLaw (I : Finset ℤ) : IsProbabilityMeasure (winLaw μ κ I) := by
  rw [winLaw]
  split_ifs with h
  · exact Measure.isProbabilityMeasure_map (measurable_winProj I h).aemeasurable
  · infer_instance

/-- The window law can be computed from a chain vector of any length at least the span, as long
as the offsets are the offsets from the left end of the window. -/
theorem winLaw_eq_chainVec_map (hinv : μ.bind κ = μ) {I : Finset ℤ} (h : I.Nonempty) {N : ℕ}
    (hN : winLen I h ≤ N) {off : I → Fin N}
    (hoff : ∀ i, (off i : ℕ) = (((i : ℤ) - I.min' h)).toNat) :
    (chainVec μ κ N).map (fun v => fun i : I => v (off i)) = winLaw μ κ I := by
  rw [winLaw_eq μ κ I h, winLawOf]
  have htrunc : (chainVec μ κ N).map
      (fun v : Fin N → β => fun i : Fin (winLen I h) => v ⟨i.1, lt_of_lt_of_le i.2 hN⟩)
      = chainVec μ κ (winLen I h) := by
    rw [← chainVec_shiftD μ κ hinv 0 N (winLen I h) (by omega)]
    congr 1
  rw [← htrunc,
    Measure.map_map (g := fun w : Fin (winLen I h) → β => fun i : I => w (winOff I h i))
      (f := fun v : Fin N → β => fun i : Fin (winLen I h) => v ⟨i.1, lt_of_lt_of_le i.2 hN⟩)
      (measurable_pi_lambda _ fun i => measurable_pi_apply _)
      (measurable_pi_lambda _ fun i => measurable_pi_apply _)]
  congr 1
  funext v i
  exact congrArg v (Fin.ext (by simp [winOff, hoff]))

/-! ### Arithmetic of windows -/

theorem min'_sub_min'_of_subset {I J : Finset ℤ} (hJI : J ⊆ I) (hJ : J.Nonempty)
    (hI : I.Nonempty) : I.min' hI ≤ J.min' hJ :=
  Finset.min'_le I (J.min' hJ) (hJI (Finset.min'_mem J hJ))

theorem max'_le_max'_of_subset {I J : Finset ℤ} (hJI : J ⊆ I) (hJ : J.Nonempty)
    (hI : I.Nonempty) : J.max' hJ ≤ I.max' hI :=
  Finset.le_max' I (J.max' hJ) (hJI (Finset.max'_mem J hJ))

/-- Offsets of a sub-window differ by the displacement of the left ends. -/
theorem winOff_sub {I J : Finset ℤ} (hJI : J ⊆ I) (hJ : J.Nonempty) (hI : I.Nonempty)
    (j : J) :
    (((j : ℤ) - I.min' hI)).toNat
      = (((j : ℤ) - J.min' hJ)).toNat + (J.min' hJ - I.min' hI).toNat := by
  have hmin := min'_sub_min'_of_subset hJI hJ hI
  have h1 : (j : ℤ) - I.min' hI = ((j : ℤ) - J.min' hJ) + (J.min' hJ - I.min' hI) := by ring
  rw [h1, Int.toNat_add (by have := Finset.min'_le J (j : ℤ) j.2; omega) (by omega)]

/-- The length of a sub-window plus the displacement of the left ends is at most the length of
the larger window. -/
theorem winLen_add_le {I J : Finset ℤ} (hJI : J ⊆ I) (hJ : J.Nonempty) (hI : I.Nonempty) :
    winLen J hJ + (J.min' hJ - I.min' hI).toNat ≤ winLen I hI := by
  have hmin := min'_sub_min'_of_subset hJI hJ hI
  have hmax := max'_le_max'_of_subset hJI hJ hI
  have hA : (0 : ℤ) ≤ J.max' hJ - J.min' hJ := by
    have := Finset.min'_le J (J.max' hJ) (Finset.max'_mem J hJ); omega
  have hB : (0 : ℤ) ≤ J.min' hJ - I.min' hI := by omega
  have key : (J.max' hJ - I.min' hI).toNat
      = (J.max' hJ - J.min' hJ).toNat + (J.min' hJ - I.min' hI).toNat := by
    rw [← Int.toNat_add hA hB]
    congr 1
    ring
  have h3 : (J.max' hJ - I.min' hI).toNat ≤ (I.max' hI - I.min' hI).toNat :=
    Int.toNat_le_toNat (by omega)
  simp only [winLen]
  omega

theorem subsingleton_pi_of_not_nonempty {s : Finset ℤ} (h : ¬ s.Nonempty) :
    Subsingleton (Π i : s, β) :=
  ⟨fun f g => funext fun i => absurd ⟨i.1, i.2⟩ h⟩

theorem measurable_restrict₂ {I J : Finset ℤ} (hJI : J ⊆ I) :
    Measurable (Finset.restrict₂ (π := fun _ : ℤ => β) hJI) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

/-! ### Projectivity -/

theorem winLaw_projective (hinv : μ.bind κ = μ) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ => β) (winLaw μ κ) := by
  intro I J hJI
  by_cases hJ : J.Nonempty
  · have hI : I.Nonempty := by
      obtain ⟨y, hy⟩ := hJ
      exact ⟨y, hJI hy⟩
    rw [winLaw_eq μ κ J hJ, winLaw_eq μ κ I hI, winLawOf, winLawOf,
      map_map' (chainVec μ κ (winLen I hI))
        (fun v : Fin (winLen I hI) → β => fun i : I => v (winOff I hI i))
        (Finset.restrict₂ (π := fun _ : ℤ => β) hJI) (measurable_winProj I hI)
        (measurable_restrict₂ hJI)]
    have hle : winLen J hJ + (J.min' hJ - I.min' hI).toNat ≤ winLen I hI :=
      winLen_add_le hJI hJ hI
    rw [← chainVec_shiftD μ κ hinv (d := (J.min' hJ - I.min' hI).toNat)
      (N := winLen I hI) (n := winLen J hJ) hle,
      map_map' (chainVec μ κ (winLen I hI))
        (fun v : Fin (winLen I hI) → β => fun i : Fin (winLen J hJ) =>
          v ⟨i.1 + (J.min' hJ - I.min' hI).toNat, by omega⟩)
        (fun w : Fin (winLen J hJ) → β => fun j : J => w (winOff J hJ j))
        (measurable_shiftIdx hle) (measurable_winProj J hJ)]
    congr 1
    funext v j
    exact congrArg v (Fin.ext (by
      simp only [Function.comp_apply, winOff, winOff_sub hJI hJ hI j]))
  · rw [winLaw, dif_neg hJ]
    haveI : Subsingleton (Π j : J, β) := subsingleton_pi_of_not_nonempty hJ
    exact (map_eq_of_subsingleton _ (measurable_restrict₂ hJI) _).symm

/-! ### Shift stationarity -/

theorem sub_mem_of_mem_image {k j : ℤ} {I : Finset ℤ}
    (hj : j ∈ I.image (fun i => i + k)) : j - k ∈ I := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  simpa using hi

/-- Reindex a window law on `I` to the shifted window `I + k`. -/
def winReindex (k : ℤ) (I : Finset ℤ) :
    (Π j : I, β) → (Π j : I.image (fun i => i + k), β) := by
  classical
  exact fun y j => y ⟨j.1 - k, sub_mem_of_mem_image j.2⟩

theorem measurable_winReindex (k : ℤ) (I : Finset ℤ) : Measurable (winReindex (β := β) k I) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

theorem min'_image_add (I : Finset ℤ) (h : I.Nonempty) (k : ℤ) :
    (I.image (fun i : ℤ => i + k)).min' (h.image (fun i : ℤ => i + k)) = I.min' h + k := by
  refine le_antisymm ?_ ?_
  · exact Finset.min'_le (I.image (fun i : ℤ => i + k)) (I.min' h + k)
      (Finset.mem_image.mpr ⟨I.min' h, Finset.min'_mem I h, rfl⟩)
  · refine Finset.le_min' _ _ (I.min' h + k) fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have := Finset.min'_le I i hi
    omega

theorem max'_image_add (I : Finset ℤ) (h : I.Nonempty) (k : ℤ) :
    (I.image (fun i : ℤ => i + k)).max' (h.image (fun i : ℤ => i + k)) = I.max' h + k := by
  refine le_antisymm ?_ ?_
  · refine Finset.max'_le _ _ (I.max' h + k) fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have := Finset.le_max' I i hi
    omega
  · exact Finset.le_max' (I.image (fun i : ℤ => i + k)) (I.max' h + k)
      (Finset.mem_image.mpr ⟨I.max' h, Finset.max'_mem I h, rfl⟩)

theorem winLen_image_add (I : Finset ℤ) (h : I.Nonempty) (k : ℤ) :
    winLen (I.image (fun i : ℤ => i + k)) (h.image (fun i : ℤ => i + k)) = winLen I h := by
  rw [winLen, winLen, min'_image_add, max'_image_add, add_sub_add_right_eq_sub]

theorem winLaw_shift (hinv : μ.bind κ = μ) (k : ℤ) (I : Finset ℤ) :
    winLaw μ κ (I.image (fun i => i + k)) = (winLaw μ κ I).map (winReindex k I) := by
  by_cases hI : I.Nonempty
  · have hJ : (I.image (fun i : ℤ => i + k)).Nonempty := hI.image _
    have hlen : winLen (I.image (fun i : ℤ => i + k)) hJ = winLen I hI := winLen_image_add I hI k
    have hJ_eq : winLaw μ κ (I.image (fun i : ℤ => i + k))
        = (chainVec μ κ (winLen (I.image (fun i : ℤ => i + k)) hJ)).map
            (fun v => fun j : I.image (fun i : ℤ => i + k) => v (winOff _ hJ j)) :=
      winLaw_eq μ κ _ hJ
    have hI_eq : winLaw μ κ I
        = (chainVec μ κ (winLen (I.image (fun i : ℤ => i + k)) hJ)).map
            (fun v => fun i : I => v ⟨(((i : ℤ) - I.min' hI)).toNat, by
              rw [hlen]; exact winOff_lt I hI i⟩) := by
      refine (winLaw_eq_chainVec_map μ κ hinv hI (N := winLen (I.image (fun i : ℤ => i + k)) hJ)
        (by omega) (fun i => rfl)).symm
    rw [hJ_eq, hI_eq, map_map' (chainVec μ κ (winLen (I.image (fun i : ℤ => i + k)) hJ))
      (fun v => fun i : I => v ⟨(((i : ℤ) - I.min' hI)).toNat, by rw [hlen]; exact winOff_lt I hI i⟩)
      (winReindex k I)
      (measurable_pi_lambda _ fun i => measurable_pi_apply _) (measurable_winReindex k I)]
    congr 1
    funext v j
    have hmin : (I.image (fun i : ℤ => i + k)).min' hJ = I.min' hI + k := min'_image_add I hI k
    exact congrArg v (Fin.ext (by
      simp only [Function.comp_apply, winOff, winReindex, hmin]
      rw [show ((j : ℤ) - k) - I.min' hI = (j : ℤ) - (I.min' hI + k) from by ring]))
  · have hJ : ¬ (I.image (fun i : ℤ => i + k)).Nonempty := by
      rintro ⟨y, hy⟩
      obtain ⟨i, hi, -⟩ := Finset.mem_image.mp hy
      exact hI ⟨i, hi⟩
    rw [winLaw, dif_neg hJ]
    haveI : Subsingleton (Π j : I.image (fun i : ℤ => i + k), β) :=
      subsingleton_pi_of_not_nonempty hJ
    exact (map_eq_of_subsingleton _ (measurable_winReindex k I) _).symm

end Window

end SwarmChain
