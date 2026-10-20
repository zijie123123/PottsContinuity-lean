module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.OriginalClosedDualRead
public import PottsContinuity.Thm3.RSW.FiniteClosedDualRectangle
public import PottsContinuity.Exploration.RectangleTopFrontierPathSelector

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite RSW Exploration Push
noncomputable section
local instance routeSixFrontierReadEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- The original closed-dual graph uses actual unit lattice edges. -/
theorem originalClosedDualGraph_le_square (ω : LatticeConfiguration) :
    wholePlaneClosedDualGraph ω ≤ PD.FK.squareLattice := by
  intro u v huv
  obtain ⟨d,_,hdir⟩ := (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mp huv
  have hd := PD.FK.squareLattice.mem_edgeSet.mp (latticeBondEdge d).property
  rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hd
  · exact hd.symm

/-- The rectangular read is EXACTLY the printed source closed-dual crossing,
including confined support, outer edges, and both endpoint columns. -/
theorem source_closedDualRectangle_crossing_iff_read
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex))) :
    A ∈ finiteClosedDualHorizontalRectangle V a.1 (a.1+(w:ℤ)) a.2 (a.2+(h:ℤ)) ↔
      originalClosedDualRectangleRead V a w h A ∈ rectangleHorizontalCrossingEvent a w h := by
  constructor
  · rintro ⟨u,v,p,hu,hv,hp⟩
    have hrect : ∀ x ∈ p.support, x ∈ (PD.FK.latticeRectangle a w h : Set LatticeVertex) := by
      intro x hx
      exact (mem_latticeRectangle a x w h).mpr ⟨⟨(hp x hx).1,(hp x hx).2.1⟩,
        ⟨(hp x hx).2.2.1,(hp x hx).2.2.2⟩⟩
    let q := p.induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) hrect
    have hle : (wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)).induce
        (PD.FK.latticeRectangle a w h : Set LatticeVertex) ≤
        openGraph (rectangleGraph a w h) (originalClosedDualRectangleRead V a w h A) := by
      intro x y hxy
      exact (originalClosedDualRectangleRead_openGraph_adj_iff V a w h A x y).mpr
        ⟨originalClosedDualGraph_le_square _ hxy,hxy⟩
    refine ⟨⟨u,hrect u p.start_mem_support⟩,⟨v,hrect v p.end_mem_support⟩,?_,?_,⟨q.mapLe hle⟩⟩
    · exact Finset.mem_filter.mpr ⟨hrect u p.start_mem_support,hu⟩
    · exact Finset.mem_filter.mpr ⟨hrect v p.end_mem_support,hv⟩
  · rintro ⟨u,v,hu,hv,⟨p⟩⟩
    let f : openGraph (rectangleGraph a w h) (originalClosedDualRectangleRead V a w h A) →g
        wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A) :=
      { toFun := Subtype.val,
        map_rel' := fun hxy => (originalClosedDualRectangleRead_openGraph_adj_iff V a w h A _ _).mp hxy |>.2 }
    refine ⟨u.val,v.val,p.map f,(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2,?_⟩
    intro x hx
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hx
    obtain ⟨z,_,rfl⟩ := hx
    have hz := (mem_latticeRectangle a z.val w h).mp z.property
    exact ⟨hz.1.1,hz.1.2,hz.2.1,hz.2.2⟩

/-- Both source crossing successes and failures are read by the concrete
upper-frontier exploration `Exploration.rectangleTopFrontierReveal`. No highest-path
convention is changed. -/
theorem horizontalCrossing_readFrom_topFrontier
    (a : LatticeVertex) (w h : ℕ) :
    ReadFromReveal (Exploration.rectangleTopFrontierReveal a w h)
      (rectangleHorizontalCrossingEvent a w h) := by
  intro A B hB
  have transfer : ∀ C D : Configuration (rectangleGraph a w h),
      D ∩ Exploration.rectangleTopFrontierReveal a w h C=C ∩ Exploration.rectangleTopFrontierReveal a w h C →
      C ∈ rectangleHorizontalCrossingEvent a w h → D ∈ rectangleHorizontalCrossingEvent a w h := by
    intro C D hagree hC
    have hr : Push.rectangleTopFrontierSelector a w h C=
        some (Push.rectangleTopReveal a w h C,Push.rectangleTopFrontier a w h C) := by
      simp only [Push.rectangleTopFrontierSelector,ite_eq_left hC]
    have hreveal : Exploration.rectangleTopFrontierReveal a w h C=Push.rectangleTopReveal a w h C := by
      change extremalPathUpperRevealMap (Push.rectangleTopFrontierSelector a w h) Prod.fst C=_
      simp only [extremalPathUpperRevealMap,hr]
    have hs := Push.rectangleTopFrontierSelector_oneSidedStable a w h C D _ hr (by rwa [hreveal] at hagree)
    obtain ⟨u,v,hu,hv,hconn⟩ := (Push.rectangleTopFrontierSelector_spec a w h D _ hs).1
    exact ⟨u,v,hu,hv,actualConnected_mono
      (fun _ he => (Finset.mem_inter.mp ((Push.rectangleTopFrontierSelector_spec a w h D _ hs).2 he)).1) hconn⟩
  constructor
  · intro h
    apply transfer B A
    · simpa only [hB.1] using hB.2.symm
    · exact h
  · exact transfer A B hB.2

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
