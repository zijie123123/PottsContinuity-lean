module

public import PottsContinuity.Thm3.Prop4.RawStoppedComponentLaw
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper

/-! # Reference exterior partitions on a remaining edge component -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push PlanarMixed.Square
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance componentReferenceEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- An edge omitted from a retained remaining component has a queried
endpoint whenever it touches that component. -/
theorem edgeClosed_remaining_removed_edge_endpoint {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G)
    (S : Set V)
    (hclosed : ∀ x ∈ S, ∀ y, (edgeRestriction G R).Adj x y → y ∈ S)
    (e : G.edgeSet)
    (he : e ∈ subgraphRemovedEdges (((edgeRestriction G R).induce S).map (pocketInclusion S)) G)
    (x : V) (hx : x ∈ S) (hxe : x ∈ e.val) :
    ∃ f ∈ R, x ∈ f.val := by
  classical
  by_cases heR : e ∈ R
  · exact ⟨e,heR,hxe⟩
  · exfalso
    have hn := (mem_subgraphRemovedEdges e).mp he
    obtain ⟨y,hpair⟩ := Sym2.mem_iff_exists.mp hxe
    have hG : G.Adj x y := G.mem_edgeSet.mp (hpair ▸ e.property)
    have hH : (edgeRestriction G R).Adj x y := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hG,?_⟩
      rintro ⟨f,hf,hfe⟩
      have hfe' : f = e := Subtype.ext (hfe.trans hpair.symm)
      exact heR (hfe' ▸ hf)
    have hy := hclosed x hx y hH
    apply hn
    rw [hpair]
    exact (((edgeRestriction G R).induce S).map (pocketInclusion S)).mem_edgeSet.mpr
      ((SimpleGraph.map_adj _ _ _ _).mpr ⟨⟨x,hx⟩,⟨y,hy⟩,hH,rfl,rfl⟩)

/-- Arbitrary exterior configurations cannot produce a stronger retained
partition than wiring all queried-adjacent vertices. The original reference
boundary is allowed any identifications supported on queried endpoints. -/
theorem edgeClosed_remaining_reference_partition_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G)
    (S : Set V)
    (hclosed : ∀ x ∈ S, ∀ y, (edgeRestriction G R).Adj x y → y ∈ S)
    (ξ : BoundaryCondition V) (anchor : S)
    (ha : ∃ e ∈ R, anchor.val ∈ e.val)
    (hξ : ∀ x y, ξ.partition.r x y → x = y ∨
      (∃ e ∈ R, x ∈ e.val) ∧ (∃ e ∈ R, y ∈ e.val))
    (K : RemovedConfiguration G
      (subgraphRemovedEdges (((edgeRestriction G R).induce S).map (pocketInclusion S)) G)) :
    (isolatedExtensionPullbackBoundary (pocketInclusion S) (frozenBoundary ξ K.val)).partition ≤
      (BoundaryCondition.wired {x : S | ∃ e ∈ R, x.val ∈ e.val}).partition := by
  classical
  let r := wiredPocketRetraction S anchor
  let W : Set S := {x | ∃ e ∈ R, x.val ∈ e.val}
  have hr : ∀ x : S, r ((pocketInclusion S) x) = x := by
    intro x
    change wiredPocketRetraction S anchor x.val = x
    simp only [wiredPocketRetraction,dite_eq_left x.property]
  have hmem (x : V) (hx : ∃ e ∈ R, x ∈ e.val) : r x ∈ W := by
    by_cases hxC : x ∈ S
    · simpa only [r,W,wiredPocketRetraction,dite_eq_left hxC,Set.mem_ofPred_eq] using hx
    · simpa only [r,W,wiredPocketRetraction,dite_eq_right hxC,Set.mem_ofPred_eq] using ha
  apply componentSetoid_comap_le_of_retraction (pocketInclusion S) r hr ξ K.val
    (BoundaryCondition.wired W).partition
  · intro x y hxy
    apply (BoundaryCondition.wired_rel _ _ _).mpr
    rcases hξ x y hxy with h | ⟨hx,hy⟩
    · exact Or.inl (congrArg r h)
    · exact Or.inr ⟨hmem x hx,hmem y hy⟩
  · intro x y hxy
    obtain ⟨e,he,hev⟩ := (openGraph_adj G K.val x y).mp hxy
    have heR := K.property he
    have bx : r x ∈ W := by
      by_cases hx : x ∈ S
      · apply hmem
        exact edgeClosed_remaining_removed_edge_endpoint G R S hclosed e heR x hx
          (hev ▸ Sym2.mem_iff.mpr (Or.inl rfl))
      · simpa only [r,W,wiredPocketRetraction,dite_eq_right hx,Set.mem_ofPred_eq] using ha
    have by' : r y ∈ W := by
      by_cases hy : y ∈ S
      · apply hmem
        exact edgeClosed_remaining_removed_edge_endpoint G R S hclosed e heR y hy
          (hev ▸ Sym2.mem_iff.mpr (Or.inr rfl))
      · simpa only [r,W,wiredPocketRetraction,dite_eq_right hy,Set.mem_ofPred_eq] using ha
    exact (BoundaryCondition.wired_rel _ _ _).mpr (Or.inr ⟨bx,by'⟩)

end
end PottsContinuity.Thm3.Prop4
