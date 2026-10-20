module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.IncidentVertexLaw
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK
noncomputable section

/-- A nontrivial actual path using only retained bonds restricts to the
incident-vertex carrier, with its original endpoints and states unchanged. -/
theorem active_restriction_connection_of_retained_walk
    {V : Type*} [Finite V] (C H : SimpleGraph V) (hCH : C ≤ H)
    (A : Configuration H) {u v : V} (huv : u ≠ v)
    (p : (openGraph H A).Walk u v)
    (hedges : ∀ d ∈ p.edges, d ∈ C.edgeSet) :
    ∃ x y : incidentVertexSet C, x.val=u ∧ y.val=v ∧
      ActualConnected (C.induce (incidentVertexSet C))
        (embeddedConfigurationRestriction (C.induce (incidentVertexSet C)) H
          (incidentVertexEmbedding C) ((incidentVertexGraph_map C).le.trans hCH) A) x y := by
  classical
  let h : C.map (Function.Embedding.refl V) ≤ H := by
    rw [show ((Function.Embedding.refl V : V ↪ V) : V → V)=id from rfl,SimpleGraph.map_id]
    exact hCH
  let B := embeddedConfigurationRestriction C H (Function.Embedding.refl V) h A
  have hretain : ∀ d ∈ p.edges, d ∈ (openGraph C B).edgeSet := by
    intro d hd
    induction hdval : d using Sym2.inductionOn with
    | hf a b =>
      rw [hdval] at hd
      apply (openGraph C B).mem_edgeSet.mpr
      apply (embeddedRestriction_openGraph_adj_iff C H (Function.Embedding.refl V) h A a b).mpr
      exact ⟨C.mem_edgeSet.mp (hedges _ hd),p.adj_of_mem_edges hd⟩
  let q := p.transfer (openGraph C B) hretain
  have hsupport : ∀ z ∈ q.support, z ∈ incidentVertexSet C := by
    intro z hz
    by_cases hzu : z=u
    · subst z
      obtain ⟨w,hw⟩ := q.reachable.nonempty_neighborSet_left huv
      exact ⟨w,openGraph_le C B hw⟩
    · obtain ⟨w,hw⟩ := (q.takeUntil z hz).reachable.symm.nonempty_neighborSet_left hzu
      exact ⟨w,openGraph_le C B hw⟩
  let r := q.induce (incidentVertexSet C) hsupport
  let J := C.induce (incidentVertexSet C)
  let i := incidentVertexEmbedding C
  let hJ : J.map i ≤ H := (incidentVertexGraph_map C).le.trans hCH
  let F : (openGraph C B).induce (incidentVertexSet C) →g
      openGraph J (embeddedConfigurationRestriction J H i hJ A) :=
    { toFun := id
      map_rel' := by
        intro x y hxy
        have hxy' : (openGraph C B).Adj x.val y.val := hxy
        apply (embeddedRestriction_openGraph_adj_iff J H i hJ A x y).mpr
        exact ⟨openGraph_le C B hxy',
          ((embeddedRestriction_openGraph_adj_iff C H (Function.Embedding.refl V) h A x.val y.val).mp hxy').2⟩ }
  exact ⟨⟨u,hsupport u q.start_mem_support⟩,⟨v,hsupport v q.end_mem_support⟩,rfl,rfl,⟨r.map F⟩⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
