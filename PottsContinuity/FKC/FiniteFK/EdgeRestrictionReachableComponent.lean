-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EdgeRestrictionReachableComponent.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EdgeRestrictionReachableClosure
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- The actual vertex carrier of the edge-restricted component of `o`. -/
def edgeRestrictionReachableComponentCarrier
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o : V) : Set V :=
  {v | (edgeRestriction G R).Reachable o v}

/-- The induced graph of the actual edge-restricted graph on the vertices
reachable from `o`; isolated vertices of the ambient graph remain represented
in the full carrier, while this component carrier contains exactly the
reachable ones. -/
def edgeRestrictionReachableComponentGraph
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o : V) :
    SimpleGraph (edgeRestrictionReachableComponentCarrier G R o) :=
  (edgeRestriction G R).induce (edgeRestrictionReachableComponentCarrier G R o)

/-- The literal subtype embedding of the component vertices into the original
vertex type. -/
def edgeRestrictionReachableComponentEmbedding
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o : V) :
    edgeRestrictionReachableComponentCarrier G R o ↪ V where
  toFun := Subtype.val
  inj' := by
    intro x y h
    exact Subtype.ext h

/-- The component graph embeds back into the original vertex graph through
literal subtype coercion. -/
def edgeRestrictionReachableComponentToOriginal
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o : V) :
    edgeRestrictionReachableComponentGraph G R o →g G where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    exact edgeRestriction_le G R (SimpleGraph.induce_adj.mp hxy)

@[simp] theorem edgeRestrictionReachableComponentToOriginal_apply
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o : V)
    (x : edgeRestrictionReachableComponentCarrier G R o) :
    edgeRestrictionReachableComponentToOriginal G R o x = x.val := rfl

/-- The actual reachable component is closed under every original neighbor
outside `B`, once all incident edge states are uniform and the component
origin has a retained incident edge. The edge making the neighbor reachable
is proved to survive the actual `EdgeRestriction`: at the origin it is
compared with the explicit seed, and elsewhere the last edge of a real
reachable walk supplies the seed. -/
theorem edgeRestrictionReachableComponent_closed_under_original_neighbors
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (o : V) (B : Set V)
    (huniform : ∀ v, v ∉ B → ∀ e f : G.edgeSet,
      v ∈ e.val → v ∈ f.val → (e ∈ R ↔ f ∈ R))
    (horigin : ∃ e : G.edgeSet, o ∈ e.val ∧ e ∉ R) :
    ∀ ⦃x : edgeRestrictionReachableComponentCarrier G R o⦄,
      x.val ∉ B → ∀ ⦃y : V⦄, G.Adj x.val y →
        ∃ z : edgeRestrictionReachableComponentCarrier G R o,
          z.val = y ∧ (edgeRestrictionReachableComponentGraph G R o).Adj x z := by
  classical
  intro x hxB y hxy
  let H := edgeRestriction G R
  have hseed : ∃ e : G.edgeSet, x.val ∈ e.val ∧ e ∉ R := by
    by_cases hxo : x.val = o
    · rw [hxo]
      exact horigin
    · obtain ⟨path⟩ := x.property
      have hnonil : ¬ path.Nil := SimpleGraph.Walk.not_nil_of_ne (by
        intro heq
        exact hxo heq.symm)
      let eH : H.edgeSet := ⟨s(path.penultimate, x.val), H.mem_edgeSet.mpr
        (path.adj_penultimate hnonil)⟩
      have heHmem : eH.val ∈ (edgeRestriction G R).edgeSet := eH.property
      have heNotOpen : eH.val ∉ openEdges G R := by
        have hsets := congrArg (fun E : Set (Sym2 V) => eH.val ∈ E)
          (edgeRestriction_edgeSet G R)
        have hmem : eH.val ∈ G.edgeSet \ openEdges G R := hsets.mp heHmem
        exact hmem.2
      let eG : G.edgeSet := ⟨eH.val, edgeRestriction_le G R
        (path.adj_penultimate hnonil)⟩
      have heGnot : eG ∉ R := by
        intro hR
        exact heNotOpen ((coe_mem_openEdges_iff G R eG).mpr hR)
      refine ⟨eG, ?_, heGnot⟩
      have heqVal : eG.val = eH.val := rfl
      rw [heqVal]
      exact (Sym2.mem_iff').2 (Or.inr rfl)
  obtain ⟨e, heV, heR⟩ := hseed
  have hxyH : H.Adj x.val y :=
    edgeRestriction_adj_of_uniform_incident_status G R B huniform hxB e heV heR hxy
  have hreach : H.Reachable o y := x.property.trans hxyH.reachable
  let z : edgeRestrictionReachableComponentCarrier G R o := ⟨y, hreach⟩
  refine ⟨z, rfl, ?_⟩
  exact SimpleGraph.induce_adj.mpr hxyH

end PottsContinuity.FKC.FiniteFK
