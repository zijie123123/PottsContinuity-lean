module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.NativeWindowCarrier
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.DecreasingEmbeddedComparison

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW Push Exploration
noncomputable section

abbrev lemma4ActiveNativeWindowVertex (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :=
  incidentVertexSet (lemma4NativeWindowGraph n A j)

abbrev lemma4ActiveNativeWindowGraph (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :=
  (lemma4NativeWindowGraph n A j).induce (incidentVertexSet (lemma4NativeWindowGraph n A j))

abbrev lemma4ActiveNativeWindowEmbedding (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :=
  incidentVertexEmbedding (lemma4NativeWindowGraph n A j)

def lemma4ActiveNativeWindowSides (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    Set (lemma4ActiveNativeWindowVertex n A j) :=
  {u | u.val.val.1=(10*(j:ℤ)-13)*(n:ℤ) ∨ u.val.val.1=(10*(j:ℤ)-7)*(n:ℤ)}

theorem lemma4ActiveNativeWindowGraph_map_le
    (n : ℕ) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    (lemma4ActiveNativeWindowGraph n A j).map (lemma4ActiveNativeWindowEmbedding n A j) ≤
      edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A) := by
  rw [incidentVertexGraph_map]
  exact lemma4NativeWindowGraph_le n A j

/-- Actual stopped-record wiring, followed by ANY native exterior state,
is dominated by the joined vertical sides on the active window carrier. -/
theorem lemma4_actual_native_window_induced_partition_le_joined_sides
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n) (j : Fin 3)
    (K : RemovedConfiguration
      (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A))
      (subgraphRemovedEdges ((lemma4ActiveNativeWindowGraph n A j).map
        (lemma4ActiveNativeWindowEmbedding n A j))
        (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)))) :
    (isolatedExtensionPullbackBoundary (lemma4ActiveNativeWindowEmbedding n A j)
      (frozenBoundary (frozenBoundary (BoundaryCondition.free ∅)
        (revealRecordConfiguration (lemma4JointSourceReveal n) A).val) K.val)).partition ≤
      (BoundaryCondition.wired (lemma4ActiveNativeWindowSides n A j)).partition := by
  classical
  let G := lemma4AmbientGraph n
  let R := lemma4JointSourceReveal n A
  let Q := (revealRecordConfiguration (lemma4JointSourceReveal n) A).val
  let E := (edgeRestrictionConfigurationEquiv G R K.val).val
  have hattach : ∀ b ∈ E ∪ Q, ∀ u : lemma4ActiveNativeWindowVertex n A j,
      (lemma4ActiveNativeWindowEmbedding n A j) u ∈ b.val →
        u ∈ lemma4ActiveNativeWindowSides n A j := by
    intro b hb u hu
    rcases Finset.mem_union.mp hb with hbE | hbQ
    · change b ∈ (edgeRestrictionConfigurationEquiv G R K.val).val at hbE
      rw [edgeRestrictionConfigurationEquiv_val] at hbE
      obtain ⟨d,hd,heq⟩ := Finset.mem_map.mp hbE
      have hdout := (mem_subgraphRemovedEdges d).mp (K.property hd)
      rw [incidentVertexGraph_map] at hdout
      have hval : d.val=b.val := congrArg Subtype.val heq
      have hud : u.val ∈ d.val := by rw [hval]; exact hu
      exact lemma4_native_window_removed_edge_endpoint_on_side n hn A hA j d hdout u hud
    · have hb' : b ∈ A ∧ b ∈ lemma4JointSourceReveal n A := by
        simpa only [Q,revealRecordConfiguration,Finset.mem_inter] using hbQ
      exact lemma4_record_open_edge_at_active_window_vertex_on_side n hn A hA j b hb'.1 hb'.2 u hu
  have hbound := frozen_free_partition_le_wired_of_endpoint_attachment G
    (lemma4ActiveNativeWindowEmbedding n A j) (lemma4ActiveNativeWindowSides n A j) (E ∪ Q) hattach
  change Setoid.comap (lemma4ActiveNativeWindowEmbedding n A j)
    (componentSetoid (edgeRestriction G R) (frozenBoundary (BoundaryCondition.free ∅) Q) K.val) ≤ _
  rw [componentSetoid_edgeRestriction,← componentSetoid_union_frozen]
  exact hbound

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
