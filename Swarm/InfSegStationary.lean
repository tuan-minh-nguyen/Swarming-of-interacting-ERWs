/-This file continues `InfSegCompat.lean`.  `InfSeg.lean` provides the Ionescu–Tulcea law
`infLaw p hm hp hp1 π` on `ℕ → Pair N m`, its exact initial law `map_eval_zero` and the one-step
cylinder identity `jointLaw`.  The mathematical point here is that the chain is *homogeneous in the
last coordinate*: `homK n` reads only the state at time `n`.  That is what makes the law
shift-stationary once the one-step law `pairLaw` is invariant, and it is exactly the structure that
the generic Mathlib Ionescu–Tulcea API does not hand over for free.

Contents.

1. `measure_eq_of_frestrictLe` : **marginal extensionality**, with no compactness of the state
   space.  Two finite measures on `Π n, X n` agreeing on every finite-window law of the first
   `n+1` coordinates are equal.  Proof: `MeasureTheory.IsProjectiveLimit.unique` for the projective
   family `inducedFamily (fun n => μ.map (frestrictLe n))`.
2. The window maps `winS` (the shifted window `x 1, …, x (n+1)`), `snoc` (append a last
   coordinate) and `dropFirst`, with measurability and the exact identities
   `snoc_frestrictLe`, `snoc_winS`, `dropFirst_frestrictLe`, `dropFirst_last`.
3. `compProd_dropFirst` : the formal kernel identity behind homogeneity:
   `(ν ⊗ₘ homK (n+1)).map (dropFirst × id) = (ν.map dropFirst) ⊗ₘ homK n`
   for *every* measure `ν` on windows of length `n+2`.  Proved by testing on rectangles
   (`generateFrom_prod`, `isPiSystem_prod`, `ext_of_generate_finite`) and `compProd_apply_prod`.
4. `measure_eval_one` : the one-step marginal of `infLaw` is `pairLaw` itself, under
   `Kernel.Invariant (hitKKernel p hm) π`; together with `map_eval_zero` this is the base case of
   the window induction.
5. `window_stationary` : `(infLaw).map (frestrictLe n) = (infLaw).map (winS n)` for every `n`,
   by induction, using only `jointLaw`, the identities of §2, `compProd_dropFirst` and the
   invariance of `pairLaw`.  No compactness, no tightness, no positivity of `π (srSet)`.
6. `measurePreserving_trajShift` : **the trajectory shift preserves the law `infLaw`** — the
   stationarity of the canonical enriched trajectory under the genuine invariant record measure
   `π`, by §1 applied to §5.
7. The payoff: with the a.e. compatibility of `InfSegCompat`, the assembled chain law
   `chainLaw (infLaw …)` is a shift-stationary probability law on `SwarmConcat.Chain N`, and the
   paper's Kac regeneration sum holds for it.

Scope ledger: everything here is *conditional* on the existence of an invariant probability `π` for
the true stopped record kernel `hitKKernel p hm` (`TightAvail` supplies such a `π` only from the
explicit `AdvanceClause` / `HalfClause` inputs, which are not proved anywhere).  Nothing here
proves `hstruct`, positivity of `π (srSet)`, a fresh-law identity, or global tightness.
-/
import Swarm.InfSegCompat

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open SimJump

namespace SwarmInfSeg

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {N m : ℕ}

/-! ## 1. Marginal extensionality on a countable product -/

/-- **Marginal extensionality.**  Two finite measures on `Π n, X n` that agree on the law of the
first `n+1` coordinates for every `n` are equal.  No compactness of the `X n` is used: this is
`MeasureTheory.IsProjectiveLimit.unique` for the projective family of windows. -/
theorem measure_eq_of_frestrictLe {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    {μ ν : Measure (Π n, X n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (Preorder.frestrictLe (π := X) n)
      = ν.map (Preorder.frestrictLe (π := X) n)) : μ = ν := by
  classical
  have hfam : ∀ a b : ℕ, ∀ hab : a ≤ b,
      ((fun n => μ.map (Preorder.frestrictLe (π := X) n)) b).map
          (Preorder.frestrictLe₂ (π := X) hab)
        = (fun n => μ.map (Preorder.frestrictLe (π := X) n)) a := by
    intro a b hab
    rw [Measure.map_map (Preorder.measurable_frestrictLe₂ (X := X) hab)
      (Preorder.measurable_frestrictLe (X := X) b),
      Preorder.frestrictLe₂_comp_frestrictLe (π := X) hab]
  let fam : (n : ℕ) → Measure (Π i : Finset.Iic n, X i) :=
    fun n => μ.map (Preorder.frestrictLe (π := X) n)
  let P : ∀ I : Finset ℕ, Measure (Π i : I, X i) := MeasureTheory.inducedFamily fam
  have hproj : MeasureTheory.IsProjectiveMeasureFamily P :=
    MeasureTheory.isProjectiveMeasureFamily_inducedFamily fam hfam
  have hμ : MeasureTheory.IsProjectiveLimit μ P :=
    (MeasureTheory.isProjectiveLimit_nat_iff hproj μ).mpr (fun n => by
      show μ.map (Preorder.frestrictLe (π := X) n) = P (Finset.Iic n)
      rw [show P (Finset.Iic n) = fam n from MeasureTheory.inducedFamily_Iic (μ := fam) n])
  have hν : MeasureTheory.IsProjectiveLimit ν P :=
    (MeasureTheory.isProjectiveLimit_nat_iff hproj ν).mpr (fun n => by
      show ν.map (Preorder.frestrictLe (π := X) n) = P (Finset.Iic n)
      rw [show P (Finset.Iic n) = fam n from MeasureTheory.inducedFamily_Iic (μ := fam) n, ← h n])
  exact MeasureTheory.IsProjectiveLimit.unique hμ hν

/-! ## 2. Window maps: the shifted window, appending and dropping coordinates -/

/-- The shifted window of length `n+1`: coordinates `1, …, n+1`.  It is definitionally the window
of the shifted trajectory. -/
noncomputable def winS (n : ℕ) (x : ℕ → Pair N m) : Π _i : Finset.Iic n, Pair N m :=
  fun i => x (i.1 + 1)

theorem winS_apply (n : ℕ) (x : ℕ → Pair N m) (i : Finset.Iic n) :
    winS (N := N) (m := m) n x i = x (i.1 + 1) := rfl

theorem winS_eq_frestrictLe_shift (n : ℕ) (x : ℕ → Pair N m) :
    winS (N := N) (m := m) n x
      = Preorder.frestrictLe (π := fun _ => Pair N m) n
          (SwarmChainAssemble.trajShift x) := rfl

theorem measurable_winS (n : ℕ) : Measurable (winS (N := N) (m := m) n) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_pi_apply (i.1 + 1)

/-- **Append a last coordinate**: `(w 0, …, w n, b)`. -/
noncomputable def snoc (n : ℕ) (q : (Π _i : Finset.Iic n, Pair N m) × Pair N m) :
    Π _i : Finset.Iic (n + 1), Pair N m :=
  fun i => if h : i.1 ≤ n then q.1 ⟨i.1, Finset.mem_Iic.2 h⟩ else q.2

/-- **Drop the first coordinate**: `(w 1, …, w (n+1))`. -/
noncomputable def dropFirst (n : ℕ) (w : Π _i : Finset.Iic (n + 1), Pair N m) :
    Π _i : Finset.Iic n, Pair N m :=
  fun i => w ⟨i.1 + 1, Finset.mem_Iic.2 (by have h := Finset.mem_Iic.1 i.2; omega)⟩

theorem measurable_snoc (n : ℕ) : Measurable (snoc (N := N) (m := m) n) := by
  classical
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.1 ≤ n
  · have heq : (fun q : (Π _i : Finset.Iic n, Pair N m) × Pair N m => snoc n q i)
        = fun q => q.1 ⟨i.1, Finset.mem_Iic.2 h⟩ := by
      funext q
      simp only [snoc, dif_pos h]
    rw [heq]
    exact (measurable_pi_apply _).comp measurable_fst
  · have heq : (fun q : (Π _i : Finset.Iic n, Pair N m) × Pair N m => snoc n q i)
        = fun q => q.2 := by
      funext q
      simp only [snoc, dif_neg h]
    rw [heq]
    exact measurable_snd

theorem measurable_dropFirst (n : ℕ) : Measurable (dropFirst (N := N) (m := m) n) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_pi_apply
    (⟨i.1 + 1, Finset.mem_Iic.2 (by have h := Finset.mem_Iic.1 i.2; omega)⟩ :
      Finset.Iic (n + 1))

/-- The window of length `n+2` split as its prefix of length `n+1` and its last coordinate. -/
theorem snoc_frestrictLe (n : ℕ) (x : ℕ → Pair N m) :
    snoc (N := N) (m := m) n
        (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1))
      = Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1) x := by
  classical
  funext i
  by_cases h : i.1 ≤ n
  · simp only [snoc, dif_pos h, Preorder.frestrictLe_apply]
  · have hi : i.1 = n + 1 := by have h2 := Finset.mem_Iic.1 i.2; omega
    simp only [snoc, dif_neg h, Preorder.frestrictLe_apply]
    rw [hi]

/-- The shifted window of length `n+2` split as the shifted window of length `n+1` and the last
coordinate. -/
theorem snoc_winS (n : ℕ) (x : ℕ → Pair N m) :
    snoc (N := N) (m := m) n (winS (N := N) (m := m) n x, x (n + 2))
      = winS (N := N) (m := m) (n + 1) x := by
  classical
  funext i
  by_cases h : i.1 ≤ n
  · simp only [snoc, dif_pos h, winS_apply]
  · have hi : i.1 = n + 1 := by have h2 := Finset.mem_Iic.1 i.2; omega
    simp only [snoc, dif_neg h, winS_apply]
    rw [hi]

/-- Dropping the first coordinate of the window of length `n+2` is the shifted window. -/
theorem dropFirst_frestrictLe (n : ℕ) (x : ℕ → Pair N m) :
    dropFirst (N := N) (m := m) n
        (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1) x)
      = winS (N := N) (m := m) n x := rfl

/-- The last coordinate is untouched by dropping the first one. -/
theorem dropFirst_last (n : ℕ) (w : Π _i : Finset.Iic (n + 1), Pair N m) :
    dropFirst (N := N) (m := m) n w ⟨n, Finset.mem_Iic.2 le_rfl⟩
      = w ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := rfl

theorem measurable_dropFirst_prod (n : ℕ) :
    Measurable (Prod.map (dropFirst (N := N) (m := m) n) (id : Pair N m → Pair N m)) := by
  have h : (Prod.map (dropFirst (N := N) (m := m) n) (id : Pair N m → Pair N m))
      = fun q : (Π _i : Finset.Iic (n + 1), Pair N m) × Pair N m =>
          (dropFirst (N := N) (m := m) n q.1, q.2) := rfl
  rw [h]
  exact ((measurable_dropFirst n).comp measurable_fst).prodMk measurable_snd

/-- The window of length `1` is the constant function at the first coordinate. -/
theorem frestrictLe_zero_fun :
    (Preorder.frestrictLe (π := fun _ => Pair N m) 0 :
        (ℕ → Pair N m) → (Π _i : Finset.Iic 0, Pair N m))
      = fun x => fun _ => x 0 := by
  funext x i
  simp only [Preorder.frestrictLe_apply]
  congr 1
  have h := Finset.mem_Iic.1 i.2
  omega

/-- The shifted window of length `1` is the constant function at the second coordinate. -/
theorem winS_zero_fun :
    (winS (N := N) (m := m) 0 : (ℕ → Pair N m) → (Π _i : Finset.Iic 0, Pair N m))
      = fun x => fun _ => x 1 := by
  funext x i
  simp only [winS_apply]
  congr 1
  have h := Finset.mem_Iic.1 i.2
  omega

/-! ## 3. The homogeneity identity for `compProd` with `homK` -/

/-- **Homogeneity in the last coordinate.**  Pushing a `compProd` with the `(n+2)`-step kernel
`homK (n+1)` forward along "drop the first coordinate of the window" is the same as applying the
`(n+1)`-step kernel to the dropped window: `homK` only reads the last coordinate, and dropping the
first coordinate does not change the last one.  This holds for *every* measure `ν` on windows. -/
theorem compProd_dropFirst (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (ν : Measure (Π _i : Finset.Iic (n + 1), Pair N m)) [IsFiniteMeasure ν] :
    (ν ⊗ₘ homK (N := N) (m := m) p hm (n + 1)).map
        (Prod.map (dropFirst (N := N) (m := m) n) id)
      = (ν.map (dropFirst (N := N) (m := m) n)) ⊗ₘ homK (N := N) (m := m) p hm n := by
  classical
  haveI hK : IsMarkovKernel (homK (N := N) (m := m) p hm (n + 1)) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1 (n + 1)
  haveI hKn : IsMarkovKernel (homK (N := N) (m := m) p hm n) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1 n
  haveI hSν0 : SFinite ν := inferInstance
  haveI hSν : SFinite (ν.map (dropFirst (N := N) (m := m) n)) := inferInstance
  haveI hfin : IsFiniteMeasure (ν ⊗ₘ homK (N := N) (m := m) p hm (n + 1)) :=
    ⟨by rw [Measure.compProd_apply_univ]; exact measure_lt_top ν _⟩
  refine ext_of_generate_finite
    (image2 (· ×ˢ ·) {s : Set (Π _i : Finset.Iic n, Pair N m) | MeasurableSet s}
      {t : Set (Pair N m) | MeasurableSet t})
    generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : MeasurableSet t := ht
    have hms : MeasurableSet (dropFirst (N := N) (m := m) n ⁻¹' s) :=
      (measurable_dropFirst n) hs'
    have hpre : (Prod.map (dropFirst (N := N) (m := m) n) id) ⁻¹' (s ×ˢ t)
        = (dropFirst (N := N) (m := m) n ⁻¹' s) ×ˢ t := by
      ext q
      simp only [Prod.map, id, mem_preimage, Set.mem_prod]
    rw [Measure.map_apply (measurable_dropFirst_prod n) (hs'.prod ht'), hpre,
      Measure.compProd_apply_prod hms ht', Measure.compProd_apply_prod hs' ht',
      setLIntegral_map hs' (Kernel.measurable_coe _ ht') (measurable_dropFirst n)]
    refine setLIntegral_congr_fun hms ?_
    intro w _
    rw [show (fun w : Π _i : Finset.Iic (n + 1), Pair N m =>
          (homK (N := N) (m := m) p hm (n + 1) w) t)
        = (fun w => (homK (N := N) (m := m) p hm n
            (dropFirst (N := N) (m := m) n w)) t) from by
      funext w
      simp only [homK, Kernel.comap_apply]
      rw [dropFirst_last n w]]
  · have h1 : (ν ⊗ₘ homK (N := N) (m := m) p hm (n + 1)).map
          (Prod.map (dropFirst (N := N) (m := m) n) (id : Pair N m → Pair N m)) univ
        = ν univ := by
      rw [Measure.map_apply (measurable_dropFirst_prod n) MeasurableSet.univ,
        Set.preimage_univ, Measure.compProd_apply_univ]
    have h2 : ((ν.map (dropFirst (N := N) (m := m) n)) ⊗ₘ
          homK (N := N) (m := m) p hm n) univ = ν univ := by
      rw [Measure.compProd_apply_univ,
        Measure.map_apply (measurable_dropFirst n) MeasurableSet.univ, Set.preimage_univ]
    rw [h1, h2]

/-! ## 4. The one-step marginal is the invariant `pairLaw` -/

/-- **The law of the state at time `1` is `pairLaw`**, by the cylinder identity at `n = 0` and the
invariance of `pairLaw` for the enriched step `pairK`.  This is the base case of the window
induction; it is the only place where `Kernel.Invariant (hitKKernel p hm) π` enters. -/
theorem measure_eval_one (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map (fun x : ℕ → Pair N m => x 1)
      = SwarmSegKernel.pairLaw (N := N) (m := m) p hm π := by
  classical
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  haveI hK0 : IsMarkovKernel (homK (N := N) (m := m) p hm 0) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1 0
  have hconst : Measurable (fun z : Pair N m => fun _ : Finset.Iic 0 => z) :=
    measurable_pi_lambda _ fun _ => measurable_id
  have hev0 : Measurable (fun x : ℕ → Pair N m => x 0) := measurable_pi_apply 0
  have hev1 : Measurable (fun x : ℕ → Pair N m => x 1) := measurable_pi_apply 1
  have hjoint := jointLaw (N := N) (m := m) p hm hp hp1 π 0
  have hν : (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) 0)
      = (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
          (fun z : Pair N m => fun _ : Finset.Iic 0 => z) := by
    rw [frestrictLe_zero_fun,
      show (fun x : ℕ → Pair N m => fun _ : Finset.Iic 0 => x 0)
          = (fun z : Pair N m => fun _ : Finset.Iic 0 => z) ∘ (fun x : ℕ → Pair N m => x 0)
          from rfl,
      ← Measure.map_map hconst hev0, map_eval_zero (N := N) (m := m) p hm hp hp1 π]
  have hsnd : ((infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) 0)) ⊗ₘ
          homK (N := N) (m := m) p hm 0
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map
          (fun x => (Preorder.frestrictLe (π := fun _ => Pair N m) 0 x, x (0 + 1))) := hjoint
  calc (infLaw (N := N) (m := m) p hm hp hp1 π).map (fun x : ℕ → Pair N m => x 1)
      = ((infLaw (N := N) (m := m) p hm hp hp1 π).map
          (fun x => (Preorder.frestrictLe (π := fun _ => Pair N m) 0 x, x (0 + 1)))).map
            Prod.snd := by
        rw [Measure.map_map measurable_snd (measurable_prefixSucc (N := N) (m := m) 0)]
        rfl
    _ = (((infLaw (N := N) (m := m) p hm hp hp1 π).map
            (Preorder.frestrictLe (π := fun _ => Pair N m) 0)) ⊗ₘ
              homK (N := N) (m := m) p hm 0).map Prod.snd := by rw [hsnd]
    _ = ((infLaw (N := N) (m := m) p hm hp hp1 π).map
            (Preorder.frestrictLe (π := fun _ => Pair N m) 0)).bind
              (fun v => homK (N := N) (m := m) p hm 0 v) := by
        rw [← Measure.snd, Measure.snd_compProd]
    _ = (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).bind
          (fun z => SwarmSegKernel.pairK (N := N) (m := m) p hm z) := by
        have hcomp : (fun z : Pair N m => homK (N := N) (m := m) p hm 0
              (fun _ : Finset.Iic 0 => z))
            = (fun z => SwarmSegKernel.pairK (N := N) (m := m) p hm z) := by
          funext z
          simp only [homK, Kernel.comap_apply]
        rw [hν, SwarmSegKernel.bind_map_eq hconst
          (Kernel.measurable (homK (N := N) (m := m) p hm 0)), hcomp]
    _ = SwarmSegKernel.pairLaw (N := N) (m := m) p hm π :=
        SwarmSegKernel.pairLaw_bind (N := N) (m := m) p hm hp hp1 hinv

/-- The law of the state at time `0` is `pairLaw` (restating `map_eval_zero`). -/
theorem measure_eval_zero' (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map (fun x : ℕ → Pair N m => x 0)
      = SwarmSegKernel.pairLaw (N := N) (m := m) p hm π :=
  map_eval_zero (N := N) (m := m) p hm hp hp1 π

/-- **Base case of the window induction**: the law of the window `(x 0)` is the law of the window
`(x 1)`. -/
theorem window_stationary_zero (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) 0)
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map (winS (N := N) (m := m) 0) := by
  have h0 := measure_eval_zero' (N := N) (m := m) p hm hp hp1 π
  have h1 := measure_eval_one (N := N) (m := m) p hm hp hp1 π hinv
  have hconst : Measurable (fun z : Pair N m => fun _ : Finset.Iic 0 => z) :=
    measurable_pi_lambda _ fun _ => measurable_id
  have hev0 : Measurable (fun x : ℕ → Pair N m => x 0) := measurable_pi_apply 0
  have hev1 : Measurable (fun x : ℕ → Pair N m => x 1) := measurable_pi_apply 1
  rw [frestrictLe_zero_fun, winS_zero_fun,
    show (fun x : ℕ → Pair N m => fun _ : Finset.Iic 0 => x 0)
        = (fun z : Pair N m => fun _ : Finset.Iic 0 => z) ∘ (fun x : ℕ → Pair N m => x 0)
        from rfl,
    show (fun x : ℕ → Pair N m => fun _ : Finset.Iic 0 => x 1)
        = (fun z : Pair N m => fun _ : Finset.Iic 0 => z) ∘ (fun x : ℕ → Pair N m => x 1)
        from rfl,
    ← Measure.map_map hconst hev0, ← Measure.map_map hconst hev1, h0, h1]

/-! ## 5. The window induction -/

/-- **One step of the window induction.**  If the law of the window `(x 0, …, x n)` equals the law
of `(x 1, …, x (n+1))`, then the same holds one length up.  Everything used is the cylinder
identity `jointLaw`, the split identities of §2 and the homogeneity identity
`compProd_dropFirst`. -/
theorem window_stationary_succ (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ)
    (ih : (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) n)
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map (winS (N := N) (m := m) n)) :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map (winS (N := N) (m := m) (n + 1)) := by
  classical
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  haveI hKn : IsMarkovKernel (homK (N := N) (m := m) p hm n) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1 n
  haveI hKn1 : IsMarkovKernel (homK (N := N) (m := m) p hm (n + 1)) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1 (n + 1)
  haveI hSν : SFinite ((infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))) := inferInstance
  have hjointn := jointLaw (N := N) (m := m) p hm hp hp1 π n
  have hjointn1 := jointLaw (N := N) (m := m) p hm hp hp1 π (n + 1)
  have hpairn : Measurable (fun x : ℕ → Pair N m =>
      (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1))) :=
    measurable_prefixSucc (N := N) (m := m) n
  have hpairn1 : Measurable (fun x : ℕ → Pair N m =>
      (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1) x, x (n + 2))) :=
    (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) (n + 1)).prodMk
      (measurable_pi_apply (n + 2))
  have hwinpair : Measurable (fun x : ℕ → Pair N m =>
      (winS (N := N) (m := m) n x, x (n + 2))) :=
    (measurable_winS n).prodMk (measurable_pi_apply (n + 2))
  have ha : (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))
      = (((infLaw (N := N) (m := m) p hm hp hp1 π).map
            (Preorder.frestrictLe (π := fun _ => Pair N m) n)) ⊗ₘ
              homK (N := N) (m := m) p hm n).map (snoc (N := N) (m := m) n) := by
    rw [show (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))
        = (snoc (N := N) (m := m) n) ∘ (fun x : ℕ → Pair N m =>
            (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1)))
        from funext fun x => (snoc_frestrictLe (N := N) (m := m) n x).symm,
      hjointn, Measure.map_map (measurable_snoc n) hpairn]
  have hb : (infLaw (N := N) (m := m) p hm hp hp1 π).map (winS (N := N) (m := m) (n + 1))
      = ((infLaw (N := N) (m := m) p hm hp hp1 π).map
          (fun x => (winS (N := N) (m := m) n x, x (n + 2)))).map
            (snoc (N := N) (m := m) n) := by
    rw [show winS (N := N) (m := m) (n + 1)
        = (snoc (N := N) (m := m) n) ∘ (fun x : ℕ → Pair N m =>
            (winS (N := N) (m := m) n x, x (n + 2)))
        from funext fun x => (snoc_winS (N := N) (m := m) n x).symm,
      Measure.map_map (measurable_snoc n) hwinpair]
  have hc : (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (fun x => (winS (N := N) (m := m) n x, x (n + 2)))
      = (((infLaw (N := N) (m := m) p hm hp hp1 π).map
            (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))) ⊗ₘ
              homK (N := N) (m := m) p hm (n + 1)).map
                (Prod.map (dropFirst (N := N) (m := m) n) id) := by
    rw [show (fun x : ℕ → Pair N m => (winS (N := N) (m := m) n x, x (n + 2)))
        = (Prod.map (dropFirst (N := N) (m := m) n) id)
            ∘ (fun x => (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1) x, x (n + 2)))
        from funext fun x => by
          simp only [Function.comp_apply, Prod.map, id, dropFirst_frestrictLe],
      hjointn1, Measure.map_map (measurable_dropFirst_prod n) hpairn1]
  rw [ha, hb, hc, compProd_dropFirst (N := N) (m := m) p hm hp hp1 n]
  have hdrop : ((infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))).map
          (dropFirst (N := N) (m := m) n)
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map (winS (N := N) (m := m) n) := by
    rw [Measure.map_map (measurable_dropFirst n)
      (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) (n + 1)),
      show (dropFirst (N := N) (m := m) n)
          ∘ (Preorder.frestrictLe (π := fun _ => Pair N m) (n + 1))
          = winS (N := N) (m := m) n
        from funext fun x => dropFirst_frestrictLe (N := N) (m := m) n x]
  rw [hdrop, ih]

/-- **Window stationarity for every length**: the law of `(x 0, …, x n)` equals the law of
`(x 1, …, x (n+1))` under `infLaw`, for every `n`, whenever `π` is invariant for the true stopped
record kernel. -/
theorem window_stationary (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) (n : ℕ) :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) n)
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map (winS (N := N) (m := m) n) := by
  induction n with
  | zero => exact window_stationary_zero p hm hp hp1 π hinv
  | succ n ih => exact window_stationary_succ p hm hp hp1 π n ih

/-! ## 6. The trajectory law is shift-stationary -/

/-- **Shift-stationarity of the canonical enriched trajectory.**  Under an invariant probability
`π` for the genuine record kernel `hitKKernel p hm`, dropping the first record step preserves the
law `infLaw p hm hp hp1 π`. -/
theorem measurePreserving_trajShift (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    MeasurePreserving (SwarmChainAssemble.trajShift (N := N) (m := m))
      (infLaw (N := N) (m := m) p hm hp hp1 π)
      (infLaw (N := N) (m := m) p hm hp hp1 π) := by
  classical
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  haveI hfin : IsFiniteMeasure ((infLaw (N := N) (m := m) p hm hp hp1 π).map
      (SwarmChainAssemble.trajShift (N := N) (m := m))) :=
    Measure.isFiniteMeasure_map _ _
  refine ⟨SwarmChainAssemble.measurable_trajShift (N := N) (m := m), ?_⟩
  refine measure_eq_of_frestrictLe (X := fun _ => Pair N m) (fun n => ?_)
  rw [Measure.map_map (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) n)
    (SwarmChainAssemble.measurable_trajShift (N := N) (m := m))]
  rw [show (Preorder.frestrictLe (π := fun _ => Pair N m) n)
      ∘ (SwarmChainAssemble.trajShift (N := N) (m := m))
      = winS (N := N) (m := m) n from funext fun x => (winS_eq_frestrictLe_shift n x).symm]
  exact (window_stationary p hm hp hp1 π hinv n).symm

/-! ## 7. The assembled chain law is stationary and obeys the Kac sum -/

/-- **The assembled chain law of the canonical trajectory is shift-stationary.** -/
theorem measurePreserving_chainLaw_shift (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    MeasurePreserving (fun c : SwarmConcat.Chain N => c.shift)
      (SwarmChainAssemble.chainLaw (infLaw (N := N) (m := m) p hm hp hp1 π))
      (SwarmChainAssemble.chainLaw (infLaw (N := N) (m := m) p hm hp hp1 π)) := by
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  exact SwarmChainAssemble.chainLaw_measurePreserving_shift _
    (trajCompat_ae p hm hp hp1 π) (measurePreserving_trajShift p hm hp hp1 π hinv)

/-- **The paper's Kac regeneration sum holds for the canonical chain law.**  For the chain
assembled from the canonical enriched trajectory, the return-time tail sum over the regeneration
event `Chain.A` is at most one. -/
theorem chainLaw_kac_tsum_infLaw (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    (∑' k : ℕ, SwarmChainAssemble.chainLaw (infLaw (N := N) (m := m) p hm hp hp1 π)
        (SwarmConcat.Chain.A ∩ KacFormula.noReturn
          (fun c : SwarmConcat.Chain N => c.shift) SwarmConcat.Chain.A k)) ≤ 1 := by
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  exact SwarmChainAssemble.chainLaw_kac_tsum _
    (trajCompat_ae p hm hp hp1 π) (measurePreserving_trajShift p hm hp hp1 π hinv)

end SwarmInfSeg
