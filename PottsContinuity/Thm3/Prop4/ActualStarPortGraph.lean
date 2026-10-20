module

public import PottsContinuity.Thm3.Prop4.RawFaceBoundaryBounds
public import PottsContinuity.Thm3.Prop4.FourPortInducedConnectivity
public import PottsContinuity.Thm3.Prop4.SampledStarPorts
public import PottsContinuity.Thm3.Push.CellBoundaryMixedIncidence

/-! # The connected graph of at most four actual sampled star ports -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section
local instance actualStarEdgeFT (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _

/-- Each genuine sampled star face is one of the four incident cell labels. -/
theorem sampledStarFacePorts_subset_four (a : LatticeVertex) (w h : ℕ) (z : RectangleVertex a w h) :
    sampledStarFacePorts a w h z ⊆
      ({z.val,(z.val.1-1,z.val.2),(z.val.1,z.val.2-1),(z.val.1-1,z.val.2-1)} : Finset LatticeVertex) := by
  rintro f ⟨b,hb,hf⟩
  change f ∈ ({z.val,(z.val.1-1,z.val.2),(z.val.1,z.val.2-1),(z.val.1-1,z.val.2-1)} : Finset LatticeVertex)
  have hzb : z.val ∈ b.val.toSym2 := Sym2.mem_iff.mpr (hb.imp Eq.symm Eq.symm)
  rcases hf with rfl | rfl
  · simpa only [Finset.mem_insert,Finset.mem_singleton] using Push.incident_bond_face_cases b.val z.val hzb false
  · simpa only [Finset.mem_insert,Finset.mem_singleton] using Push.incident_bond_face_cases b.val z.val hzb true

/-- The actual sampled port carrier is finite even at a boundary corner. -/
theorem sampledStarFacePorts_finite (a : LatticeVertex) (w h : ℕ) (z : RectangleVertex a w h) :
    (sampledStarFacePorts a w h z).Finite :=
  (Finset.finite_toSet _).subset (sampledStarFacePorts_subset_four a w h z)

/-- The actual star has at most four genuine face ports, independently of
its presentation as a finite carrier. -/
theorem sampledStarFacePorts_card_le_four (a : LatticeVertex) (w h : ℕ) (z : RectangleVertex a w h)
    [Fintype (sampledStarFacePorts a w h z)] : Fintype.card (sampledStarFacePorts a w h z) ≤ 4 := by
  classical
  let T : Finset LatticeVertex := {z.val,(z.val.1-1,z.val.2),(z.val.1,z.val.2-1),(z.val.1-1,z.val.2-1)}
  let f : sampledStarFacePorts a w h z ↪ T := {
    toFun := fun x => ⟨x.val,sampledStarFacePorts_subset_four a w h z x.property⟩
    inj' := fun x y h => Subtype.ext (congrArg (fun p : T => p.val) h) }
  have hcard := Fintype.card_le_of_injective f f.injective
  have hcard' : Fintype.card (sampledStarFacePorts a w h z) ≤ T.card := by
    simpa only [Fintype.card_coe] using hcard
  exact hcard'.trans Finset.card_le_four

/-- This auxiliary state closes exactly the actual original star. It is
used for geometry only and is not a source exploration or conditioning. -/
def actualStarClosedState (a : LatticeVertex) (w h : ℕ) (z : RectangleVertex a w h) :
    Configuration (rectangleGraph a w h) := by
  classical
  exact Finset.univ.filter fun e => z ∉ e.val

/-- Every normalized original bond incident to the selected vertex is closed
in the auxiliary geometric star state. -/
theorem actualStarClosedState_incident_closed (a : LatticeVertex) (w h : ℕ)
    (z : RectangleVertex a w h) (b : RectanglePrimalBond a w h)
    (hb : b.val.source = z.val ∨ b.val.target = z.val) :
    rectanglePrimalBondToEdge a w h b ∉ actualStarClosedState a w h z := by
  classical
  intro he
  apply (Finset.mem_filter.mp he).2
  change z ∈ s(⟨b.val.source,b.property.1⟩,⟨b.val.target,b.property.2⟩)
  exact Sym2.mem_iff.mpr (hb.imp (fun h => Subtype.ext h.symm) (fun h => Subtype.ext h.symm))

/-- Both endpoints of each auxiliary star step are genuine sampled ports. -/
theorem actualStarClosedState_adj_ports (a : LatticeVertex) (w h : ℕ) (z : RectangleVertex a w h)
    {x y : LatticeVertex}
    (hxy : (PlanarTopology.rectangleSampledClosedDualGraph a w h (actualStarClosedState a w h z)).Adj x y) :
    x ∈ sampledStarFacePorts a w h z ∧ y ∈ sampledStarFacePorts a w h z := by
  classical
  obtain ⟨d,hd,hends⟩ := hxy
  have hz : z ∈ d.primalEdge.val := by
    by_contra hn
    exact hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
  let b : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h d.primalEdge,rectanglePrimalEdgeBond_endpoints_mem_public a w h d.primalEdge⟩
  have hb : b.val.source = z.val ∨ b.val.target = z.val :=
    (rectangle_edge_vertex_normalized_endpoint a w h d.primalEdge z hz).imp Eq.symm Eq.symm
  have hs : d.crossingBond.source = b.val.faceBase false := by
    rw [d.crossingBond_eq]
    exact rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h d.primalEdge)
  have ht : d.crossingBond.target = b.val.faceBase true := by
    rw [d.crossingBond_eq]
    exact rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h d.primalEdge)
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨⟨b,hb,Or.inl hs⟩,⟨b,hb,Or.inr ht⟩⟩
  · exact ⟨⟨b,hb,Or.inr ht⟩,⟨b,hb,Or.inl hs⟩⟩

/-- The actual port graph is connected, including side and corner vertices.
No virtual corner bond is added. -/
theorem actualStarPortGraph_preconnected (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (z : RectangleVertex a w h) :
    ((PlanarTopology.rectangleSampledClosedDualGraph a w h (actualStarClosedState a w h z)).induce
      (sampledStarFacePorts a w h z)).Preconnected := by
  rintro ⟨x,b,hb,hx⟩ ⟨y,c,hc,hy⟩
  obtain ⟨p⟩ := PlanarTopology.rectangle_closed_star_incident_bond_faces_connected a w h hw hh
    (actualStarClosedState a w h z) z (actualStarClosedState_incident_closed a w h z)
    b c hb hc x y hx hy
  have support {s t} (q : (PlanarTopology.rectangleSampledClosedDualGraph a w h (actualStarClosedState a w h z)).Walk s t)
      (hs : s ∈ sampledStarFacePorts a w h z) : ∀ f ∈ q.support, f ∈ sampledStarFacePorts a w h z := by
    induction q with
    | nil =>
      intro f hf
      exact (List.mem_singleton.mp hf) ▸ hs
    | cons hst q ih =>
      intro f hf
      rw [SimpleGraph.Walk.support_cons,List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact hs
      · exact ih (actualStarClosedState_adj_ports a w h z hst).2 f hf
  exact ⟨p.induce _ (support p ⟨b,hb,hx⟩)⟩

end
end PottsContinuity.Thm3.Prop4
