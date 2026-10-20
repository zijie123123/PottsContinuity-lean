module

public import PottsContinuity.Thm3.Prop4.MarkedRectangleRawAccess
public import PottsContinuity.Thm3.Prop4.SampledStarPorts

/-! # Raw edge domains of a sampled dual face region -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section
local instance rawFaceEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance rawFaceEdgeFinite (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _

/-- Query exactly the original bonds incident to the specified face region. -/
def rawFaceRegionReveal (a : LatticeVertex) (w h : ℕ) (P : LatticeVertex → Prop) :
    Configuration (rectangleGraph a w h) := by
  classical
  exact Finset.univ.filter fun e => P (rectangleCrossingDualBond a w h e).source ∨
    P (rectangleCrossingDualBond a w h e).target

/-- Original bonds separating the specified face region from its complement. -/
def rawFaceRegionFrontier (a : LatticeVertex) (w h : ℕ) (P : LatticeVertex → Prop) :
    Configuration (rectangleGraph a w h) := by
  classical
  exact Finset.univ.filter fun e => P (rectangleCrossingDualBond a w h e).source ≠
    P (rectangleCrossingDualBond a w h e).target

/-- A bond left fresh has both incident dual faces outside the explored region. -/
theorem not_mem_rawFaceRegionReveal_iff (a : LatticeVertex) (w h : ℕ)
    (P : LatticeVertex → Prop) (e : (rectangleGraph a w h).edgeSet) :
    e ∉ rawFaceRegionReveal a w h P ↔
      ¬ P (rectangleCrossingDualBond a w h e).source ∧
      ¬ P (rectangleCrossingDualBond a w h e).target := by
  classical
  simp [rawFaceRegionReveal,not_or]

/-- A frontier bond is among the raw queries. -/
theorem rawFaceRegionFrontier_subset_reveal (a : LatticeVertex) (w h : ℕ)
    (P : LatticeVertex → Prop) :
    rawFaceRegionFrontier a w h P ⊆ rawFaceRegionReveal a w h P := by
  classical
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_cases hs : P (rectangleCrossingDualBond a w h e).source
  · exact Or.inl hs
  · right
    by_contra ht
    exact hh (propext (iff_of_false hs ht))

/-- Region closure under sampled closed dual bonds forces every frontier bond open. -/
theorem rawFaceRegionFrontier_subset_open (a : LatticeVertex) (w h : ℕ)
    (P : LatticeVertex → Prop) (A : Configuration (rectangleGraph a w h))
    (hclosed : ∀ e : (rectangleGraph a w h).edgeSet, e ∉ A →
      (P (rectangleCrossingDualBond a w h e).source ↔
        P (rectangleCrossingDualBond a w h e).target)) :
    rawFaceRegionFrontier a w h P ⊆ A := by
  classical
  intro e he
  by_contra hn
  exact (Finset.mem_filter.mp he).2 (propext (hclosed e hn))

/-- A queried closed bond has both dual faces in the reached region.
An open queried bond may also have both faces in that region. -/
theorem rawFaceRegionReveal_closed_faces (a : LatticeVertex) (w h : ℕ)
    (P : LatticeVertex → Prop) (A : Configuration (rectangleGraph a w h))
    (hclosed : ∀ e : (rectangleGraph a w h).edgeSet, e ∉ A →
      (P (rectangleCrossingDualBond a w h e).source ↔
        P (rectangleCrossingDualBond a w h e).target))
    (e : (rectangleGraph a w h).edgeSet)
    (he : e ∈ rawFaceRegionReveal a w h P) (hn : e ∉ A) :
    P (rectangleCrossingDualBond a w h e).source ∧
      P (rectangleCrossingDualBond a w h e).target := by
  classical
  rcases (Finset.mem_filter.mp he).2 with hs | ht
  · exact ⟨hs,(hclosed e hn).mp hs⟩
  · exact ⟨(hclosed e hn).mpr ht,ht⟩

/-- Every vertex incident to both a raw queried bond and a fresh bond is on
an original frontier bond, including boundary and corner vertices. -/
theorem rawFaceRegion_mixed_vertex_on_frontier (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (P : LatticeVertex → Prop)
    (z : RectangleVertex a w h)
    (e f : (rectangleGraph a w h).edgeSet)
    (he : e ∈ rawFaceRegionReveal a w h P) (hzE : z ∈ e.val)
    (hf : f ∉ rawFaceRegionReveal a w h P) (hzF : z ∈ f.val) :
    ∃ g ∈ rawFaceRegionFrontier a w h P, z ∈ g.val := by
  classical
  by_contra hn
  have noFront : ∀ g : (rectangleGraph a w h).edgeSet, z ∈ g.val →
      (P (rectangleCrossingDualBond a w h g).source ↔
        P (rectangleCrossingDualBond a w h g).target) := by
    intro g hzg
    apply Iff.of_eq
    by_contra hne
    exact hn ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩,hzg⟩
  let C : Configuration (rectangleGraph a w h) :=
    Finset.univ.filter fun e => z ∉ e.val
  have closedStar : ∀ b : RectanglePrimalBond a w h,
      b.val.source = z.val ∨ b.val.target = z.val → rectanglePrimalBondToEdge a w h b ∉ C := by
    intro b hb heC
    apply (Finset.mem_filter.mp heC).2
    change z ∈ s(⟨b.val.source,b.property.1⟩,⟨b.val.target,b.property.2⟩)
    rw [Sym2.mem_iff]
    rcases hb with hb | hb
    · exact Or.inl (Subtype.ext hb.symm)
    · exact Or.inr (Subtype.ext hb.symm)
  let b : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h e,rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
  let c : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h f,rectanglePrimalEdgeBond_endpoints_mem_public a w h f⟩
  have hb : b.val.source = z.val ∨ b.val.target = z.val :=
    (rectangle_edge_vertex_normalized_endpoint a w h e z hzE).imp Eq.symm Eq.symm
  have hc : c.val.source = z.val ∨ c.val.target = z.val :=
    (rectangle_edge_vertex_normalized_endpoint a w h f z hzF).imp Eq.symm Eq.symm
  have sourceBase (g : (rectangleGraph a w h).edgeSet) :
      (rectangleCrossingDualBond a w h g).source = (rectanglePrimalEdgeBond a w h g).faceBase false :=
    rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h g)
  have targetBase (g : (rectangleGraph a w h).edgeSet) :
      (rectangleCrossingDualBond a w h g).target = (rectanglePrimalEdgeBond a w h g).faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h g)
  have hfOut := (not_mem_rawFaceRegionReveal_iff a w h P f).mp hf
  obtain ⟨s,hs,hsP⟩ : ∃ s, (s = b.val.faceBase false ∨ s = b.val.faceBase true) ∧ P s := by
    rcases (Finset.mem_filter.mp he).2 with heS | heT
    · exact ⟨_,Or.inl (sourceBase e),heS⟩
    · exact ⟨_,Or.inr (targetBase e),heT⟩
  have hwalk := PlanarTopology.rectangle_closed_star_incident_bond_faces_connected
    a w h hw hh C z closedStar b c hb hc s (c.val.faceBase false) hs (Or.inl rfl)
  have step : ∀ {x y}, (PlanarTopology.rectangleSampledClosedDualGraph a w h C).Adj x y →
      (P x ↔ P y) := by
    rintro x y ⟨d,hd,hends⟩
    have hzg : z ∈ d.primalEdge.val := by
      by_contra hnz
      exact hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnz⟩)
    have hsame := noFront d.primalEdge hzg
    rw [← d.crossingBond_eq] at hsame
    rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hsame
    · exact hsame.symm
  obtain ⟨p⟩ := hwalk
  have transport {x y} (p : (PlanarTopology.rectangleSampledClosedDualGraph a w h C).Walk x y) :
      P x → P y := by
    induction p with
    | nil => exact id
    | cons hxy p ih => exact fun hx => ih ((step hxy).mp hx)
  apply hfOut.1
  rw [sourceBase f]
  exact transport p hsP

end
end PottsContinuity.Thm3.Prop4
