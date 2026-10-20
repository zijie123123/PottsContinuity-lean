module

public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual
public import PottsContinuity.Thm3.Push.RectangleLabelFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Finite and literal sampled dual walks on the same original edges -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Forgetting the finite face carrier preserves every actual sampled
closed-dual edge, with its original crossed-bond label. -/
theorem rectangle_finite_closed_dual_adj_sampled (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (s t : RectangleDualVertex a w h)
    (hst : (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj s t) :
    (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Adj s.val t.val := by
  classical
  obtain ⟨f,hf,hfst⟩ := (openGraph_adj _ _ s t).mp hst
  obtain ⟨e,rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective f
  have he : e.primalEdge ∉ A := (mem_rectangleDualConfiguration a w h A e).mp hf
  have hh := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) hfst
  change s(e.crossingBond.source,e.crossingBond.target) = s(s.val,t.val) at hh
  refine ⟨e,he,?_⟩
  rcases Sym2.eq_iff.mp hh with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Or.inl ⟨hs.symm,ht.symm⟩
  · exact Or.inr ⟨ht.symm,hs.symm⟩

/-- The finite dual graph embeds in the literal sampled closed-dual graph. -/
def rectangleFiniteClosedDualToSampled (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A) →g
      PlanarTopology.rectangleSampledClosedDualGraph a w h A where
  toFun := Subtype.val
  map_rel' := rectangle_finite_closed_dual_adj_sampled a w h A _ _

/-- Reachability on retained finite face labels is exactly literal sampled
closed-dual reachability, including the empty walk. -/
theorem rectangle_finite_closed_dual_reachable_iff_sampled (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (s t : RectangleDualVertex a w h) :
    ActualConnected (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A) s t ↔
      (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Reachable s.val t.val := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.map (rectangleFiniteClosedDualToSampled a w h A)⟩
  · rintro ⟨p⟩
    exact PlanarTopology.rectangleSampledClosedDualGraph_walk_finite a w h A p s.property t.property

end
end PottsContinuity.Thm3.Prop4
