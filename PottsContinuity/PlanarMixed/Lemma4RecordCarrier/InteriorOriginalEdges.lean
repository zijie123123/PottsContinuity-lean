module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ComplementaryQueryStar

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push
noncomputable section

/-- A bond at an interior original vertex is represented in the literal dual
rectangle read. The vertex inequalities include the exact one-unit shift. -/
theorem dualBond_endpoints_mem_of_original_interior
    (a : LatticeVertex) (w h : ℕ) (b : LatticeBond) (u : LatticeVertex)
    (hu : u ∈ b.toSym2)
    (hx : a.1+1 ≤ u.1 ∧ u.1 ≤ a.1+(w:ℤ))
    (hy : a.2+1 ≤ u.2 ∧ u.2 ≤ a.2+(h:ℤ)) :
    (dualBondOfPrimal b).source ∈ PD.FK.latticeRectangle a w h ∧
      (dualBondOfPrimal b).target ∈ PD.FK.latticeRectangle a w h := by
  have he : u=b.source ∨ u=b.target := Sym2.mem_iff'.mp hu
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp only [LatticeBond.source,LatticeBond.target] at he
  all_goals rcases he with rfl | rfl
  all_goals
    simp only at hx hy
    simp only [dualBondOfPrimal,LatticeBond.source,LatticeBond.target,PD.FK.mem_latticeRectangle,
      ]
    omega

/-- Every sampled original bond incident to an interior shifted rectangle
vertex has a literal complementary edge representative. -/
theorem original_edge_represented_of_interior_endpoint
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (e : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (u : (V : Set LatticeVertex)) (hu : u ∈ e.val)
    (hx : a.1+1 ≤ u.val.1 ∧ u.val.1 ≤ a.1+(w:ℤ))
    (hy : a.2+1 ≤ u.val.2 ∧ u.val.2 ≤ a.2+(h:ℤ)) :
    ∃ f : (rectangleGraph a w h).edgeSet,
      rectangleDualOriginalEdge V a w h f=some e := by
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective e.val
  have hp : e.val=s(x,y) := hxy.symm
  have hadj : PD.FK.squareLattice.Adj x.val y.val := by
    have he := e.property
    rw [hp] at he
    exact (PD.FK.squareLattice.induce (V : Set LatticeVertex)).mem_edgeSet.mp he
  obtain ⟨b,hb⟩ := LatticeBond.exists_of_adj hadj
  have heq : b.toSym2=Sym2.map Subtype.val e.val := by rw [hp]; exact hb
  have hub : u.val ∈ b.toSym2 := by
    rw [heq]
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  have hm := dualBond_endpoints_mem_of_original_interior a w h b u.val hub hx hy
  let f := rectanglePrimalBondToEdge a w h ⟨dualBondOfPrimal b,hm⟩
  have hf : rectanglePrimalEdgeBond a w h f=dualBondOfPrimal b :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv ⟨dualBondOfPrimal b,hm⟩)
  refine ⟨f,?_⟩
  apply (originalEdgeOfBond_eq_some_iff V _ e).mpr
  rw [hf,primalBondOfDual_dualBondOfPrimal]
  apply Subtype.ext
  exact heq.symm


/-- At an interior vertex incident to an unrevealed bond, no OPEN original
bond from the raw complementary exploration can be attached. -/
theorem complementary_raw_query_no_open_attachment_at_native_interior
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (seeds : Finset (RectangleDualVertex a w h))
    (d : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (hd : d ∉ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A)))
    (u : (V : Set LatticeVertex)) (hud : u ∈ d.val)
    (hx : a.1+1 ≤ u.val.1 ∧ u.val.1 ≤ a.1+(w:ℤ))
    (hy : a.2+1 ≤ u.val.2 ∧ u.val.2 ≤ a.2+(h:ℤ))
    (b : (squareLattice.induce (V : Set LatticeVertex)).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A))) : u ∉ b.val := by
  intro hub
  obtain ⟨f,hf⟩ := original_edge_represented_of_interior_endpoint V a w h d u hud hx hy
  exact hd (complementary_raw_open_query_incident_query V a w h A seeds b hbA hb d f hf u hub hud)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
