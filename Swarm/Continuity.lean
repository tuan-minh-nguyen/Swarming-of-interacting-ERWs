import Swarm.Bridge

open MeasureTheory Set Topology
open scoped ENNReal

namespace SimJump.Record

variable {N m : ℕ}

/-- The topology induced by the product of the position and local-time coordinates. -/
local instance : TopologicalSpace (State N m) :=
  TopologicalSpace.induced (fun s : State N m => (s.pos, s.eta)) inferInstance

lemma cont_pos : Continuous (fun s : State N m => s.pos) := by
  change Continuous (Prod.fst ∘ fun s : State N m => (s.pos, s.eta))
  exact continuous_fst.comp continuous_induced_dom

lemma cont_eta : Continuous (fun s : State N m => s.eta) := by
  change Continuous (Prod.snd ∘ fun s : State N m => (s.pos, s.eta))
  exact continuous_snd.comp continuous_induced_dom

/-- Record normalisation is continuous: positions translate by one and local times are
merely reindexed by one site. -/
lemma continuous_normalize : Continuous (normalize (N := N) (m := m)) := by
  apply continuous_induced_rng.2
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    change Continuous (fun s : State N m => s.pos i - 1)
    exact ((continuous_apply i).comp cont_pos).sub continuous_const
  · refine continuous_pi fun i => continuous_pi fun x => ?_
    change Continuous (fun s : State N m => s.eta i (x + 1))
    exact (continuous_apply (x + 1)).comp ((continuous_apply i).comp cont_eta)

/-- Compact record-state coordinates depend continuously on the stopped capped-step state. -/
lemma continuous_toRecordAmb : Continuous (toRecordAmb (N := N) (m := m)) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    exact (continuous_of_discreteTopology (f := halfDist)).comp ((continuous_apply i).comp cont_pos)
  · refine continuous_pi fun i => continuous_pi fun x => ?_
    refine continuous_discrete_rng.2 fun c => ?_
    have heq :
        (fun s : State N m => ⟨(normalize s).eta i x,
          Nat.lt_succ_of_le ((normalize s).hcap i x)⟩) ⁻¹' {c}
        = (fun s : State N m => s.eta i (x + 1)) ⁻¹' {c.val} := by
      ext s
      simp only [Fin.ext_iff, Set.mem_preimage, Set.mem_singleton_iff, normalize]
    rw [heq]
    exact (isOpen_discrete _).preimage
      ((continuous_apply (x + 1)).comp ((continuous_apply i).comp cont_eta))

/-- Expanding compact record coordinates into the capped-step chain is continuous. -/
lemma continuous_ofRecState : Continuous (ofRecState (N := N) (m := m)) := by
  apply continuous_induced_rng.2
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    have hc : Continuous (fun y : SwarmRec.RecState N m => y.val.1 i) :=
      (continuous_apply i).comp (continuous_fst.comp continuous_subtype_val)
    change Continuous (fun y : SwarmRec.RecState N m => -(2 * (y.val.1 i : ℤ)))
    exact (continuous_of_discreteTopology (f := fun d : ℕ => -(2 * (d : ℤ)))).comp hc
  · refine continuous_pi fun i => continuous_pi fun x => ?_
    have hc : Continuous (fun y : SwarmRec.RecState N m => y.val.2 i x) :=
      (continuous_apply x).comp ((continuous_apply i).comp
        (continuous_snd.comp continuous_subtype_val))
    exact (continuous_of_discreteTopology (f := fun c : Fin (m + 1) => c.val)).comp hc


