module

public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.PlanarTopology.MeasurableReachability
public import PottsContinuity.PlanarTopology.OpenGraphMonotonicity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- Measurability of actual open reachability in any fixed induced domain,
including infinite domains such as half-planes and strips. -/
theorem measurableSet_domain_open_reachable (D : Set LatticeVertex)
    (u v : {z // z ∈ D}) :
    MeasurableSet {ω : LatticeConfiguration | ((PD.rcInfiniteOpenGraph ω).induce D).Reachable u v} := by
  apply measurableSet_sampledGraph_reachable (fun ω : LatticeConfiguration => (PD.rcInfiniteOpenGraph ω).induce D)
  intro x y
  exact measurableSet_open_adj x.val y.val

/-- An original root in S connects to the vertical boundary using only the
closed right half-plane and original sampled open bonds. -/
def halfPlaneBoundaryEvent (S : Set LatticeVertex) : Set LatticeConfiguration :=
  {ω | ∃ u : {z : LatticeVertex // 0 ≤ z.1}, u.val ∈ S ∧
    ∃ v : {z : LatticeVertex // 0 ≤ z.1}, v.val.1 = 0 ∧
      ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable u v}

theorem halfPlaneBoundaryEvent_measurableSet (S : Set LatticeVertex) :
    MeasurableSet (halfPlaneBoundaryEvent S) := by
  have hc (p : Prop) : MeasurableSet {ω : LatticeConfiguration | p} := by
    by_cases hp : p <;> simp [hp]
  have hm (u v : {z : LatticeVertex // 0 ≤ z.1}) : MeasurableSet
      {ω : LatticeConfiguration | u.val ∈ S ∧ v.val.1 = 0 ∧
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable u v} :=
    (hc (u.val ∈ S)).inter ((hc (v.val.1 = 0)).inter (measurableSet_domain_open_reachable _ u v))
  convert MeasurableSet.iUnion (fun u => MeasurableSet.iUnion (hm u)) using 1
  ext ω
  simp only [halfPlaneBoundaryEvent,Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · rintro ⟨u,hu,v,hv,huv⟩
    exact ⟨u,v,hu,hv,huv⟩
  · rintro ⟨u,v,hu,hv,huv⟩
    exact ⟨u,hu,v,hv,huv⟩

end
end PottsContinuity.PlanarTopology
