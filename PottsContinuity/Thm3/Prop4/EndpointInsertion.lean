module

public import PottsContinuity.PD.RCInfinite.FiniteEnergy
public import PottsContinuity.PD.FK.Events
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Extending an actual finite connection by one original edge

DCST, the odd-square remark following Lemma 7, TeX lines 1761–1767.
The event uses actual open edges under any finite boundary partition.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance endpointEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
attribute [local instance] configurationMeasurableSpace

/-- Finite-energy extension of an actual connection at either prescribed
endpoint, with no independence assumption between the path and the new edge. -/
theorem finite_connection_endpoint_insertion (θ : Parameters) (ξ : BoundaryCondition V)
    (u v w : V) (hvw : G.Adj v w) :
    PD.RCInfinite.openEnergy θ*(measure G θ ξ (connectivityEvent G u v)).toReal ≤
      (measure G θ ξ (connectivityEvent G u w)).toReal := by
  classical
  let e : G.edgeSet := ⟨s(v,w),G.mem_edgeSet.mpr hvw⟩
  let E : Set (Configuration G) := {C | e ∈ C}
  have henergy : PD.RCInfinite.openEnergy θ ≤ (measure G θ ξ E).toReal := by
    have h := (configurationProbability_edge_finite_energy θ ξ Set.univ hvw (by simp)).1
    simpa only [Set.univ_inter, measure_univ, ENNReal.toReal_one, mul_one,
      PD.RCInfinite.openEnergy] using h
  have hconnUpper : IsUpperSet (connectivityEvent G u v) := by
    intro A B hAB hA
    exact actualConnected_mono hAB hA
  have hEUpper : IsUpperSet E := by
    intro A B hAB hA
    exact hAB hA
  have hfkg := measure_positive_association θ ξ (connectivityEvent G u v) E hconnUpper hEUpper
  have hsub : connectivityEvent G u v ∩ E ⊆ connectivityEvent G u w := by
    rintro C ⟨hconn,hCE⟩
    have hedge : (openGraph G C).Adj v w := (openGraph_adj G C v w).mpr ⟨e,hCE,rfl⟩
    exact hconn.trans hedge.reachable
  calc
    _ = (measure G θ ξ (connectivityEvent G u v)).toReal*PD.RCInfinite.openEnergy θ := mul_comm _ _
    _ ≤ (measure G θ ξ (connectivityEvent G u v)).toReal*(measure G θ ξ E).toReal :=
      mul_le_mul_of_nonneg_left henergy ENNReal.toReal_nonneg
    _ ≤ (measure G θ ξ (connectivityEvent G u v ∩ E)).toReal := hfkg
    _ ≤ _ := measureReal_mono hsub

end

end PottsContinuity.Thm3.Prop4
