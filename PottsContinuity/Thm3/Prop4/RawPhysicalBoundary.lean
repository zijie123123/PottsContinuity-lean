module

public import PottsContinuity.Thm3.Prop4.RawComponentBoundaryPartition
public import PottsContinuity.PD.FK.FrozenBridge
public import PottsContinuity.Thm3.Prop4.RawRecordedFaceRegion

/-! # Physical rectangle boundary vertices touch the raw record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Every sampled bond with an exterior dual face is queried in the source
raw record, irrespective of that bond's open/closed state. -/
theorem sourceMarkedRawReveal_of_exterior_face (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (b : LatticeBond)
    (hb : b.source ∈ PD.FK.latticeRectangle a w h ∧ b.target ∈ PD.FK.latticeRectangle a w h)
    (side : Bool) (hext : b.faceBase side ∈ rectangleExteriorFaces a w h) :
    rectanglePrimalBondToEdge a w h ⟨b,hb⟩ ∈ sourceMarkedRawReveal a w h u v A := by
  let e := rectanglePrimalBondToEdge a w h ⟨b,hb⟩
  have heBond : rectanglePrimalEdgeBond a w h e = b :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv ⟨b,hb⟩)
  have hseed := rectangle_bond_exterior_face_is_marked_seed a w h u.val v.val b hb side hext
  have hregion : sampledDualSeedRegion a w h A
      (PlanarTopology.rectangleLowerDualArc a w h u.val v.val ∪
        PlanarTopology.rectangleUpperDualArc a w h u.val v.val) (b.faceBase side) :=
    ⟨b.faceBase side,hseed,SimpleGraph.Reachable.refl _⟩
  cases side
  · apply sampledRawDualReveal_queries_step a w h A _ (rectanglePrimalDualEdgeEquiv a w h e)
      (Or.inl ⟨rfl,rfl⟩)
    change sampledDualSeedRegion a w h A _ (rectangleCrossingDualBond a w h e).source
    rw [rectangleCrossingDualBond,heBond,dualBondOfPrimal_source]
    exact hregion
  · apply sampledRawDualReveal_queries_step a w h A _ (rectanglePrimalDualEdgeEquiv a w h e)
      (Or.inr ⟨rfl,rfl⟩)
    change sampledDualSeedRegion a w h A _ (rectangleCrossingDualBond a w h e).target
    rw [rectangleCrossingDualBond,heBond,dualBondOfPrimal_target]
    exact hregion

/-- Every physical side or corner vertex of a nondegenerate rectangle is
incident to an actual queried source boundary bond. -/
theorem sourceMarkedRawBoundaryVertices_of_rectangle_side (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v z : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h))
    (hz : z.val.1 = a.1 ∨ z.val.1 = a.1+(w : ℤ) ∨
      z.val.2 = a.2 ∨ z.val.2 = a.2+(h : ℤ)) :
    z ∈ sourceMarkedRawBoundaryVertices a w h u v A := by
  classical
  have bounds := (PD.FK.mem_latticeRectangle a z.val w h).mp z.property
  have use (b : LatticeBond)
      (hb : b.source ∈ PD.FK.latticeRectangle a w h ∧ b.target ∈ PD.FK.latticeRectangle a w h)
      (side : Bool) (hext : b.faceBase side ∈ rectangleExteriorFaces a w h)
      (hzb : z.val ∈ b.toSym2) : z ∈ sourceMarkedRawBoundaryVertices a w h u v A := by
    let e := rectanglePrimalBondToEdge a w h ⟨b,hb⟩
    refine ⟨e,sourceMarkedRawReveal_of_exterior_face a w h u v A b hb side hext,?_⟩
    have heBond : rectanglePrimalEdgeBond a w h e = b :=
      congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv ⟨b,hb⟩)
    have hmap : z.val ∈ e.val.map Subtype.val := by
      rw [← rectanglePrimalEdgeBond_toSym2_public,heBond]
      exact hzb
    obtain ⟨x,hxe,hxz⟩ := Sym2.mem_map.mp hmap
    exact (Subtype.ext hxz : x = z) ▸ hxe
  rcases hz with hz | hz | hz | hz
  · let k := if z.val.2 < a.2+(h : ℤ) then z.val.2 else z.val.2-1
    let b : LatticeBond := ⟨(a.1,k),.vertical⟩
    have hk : a.2 ≤ k ∧ k < a.2+(h : ℤ) := by dsimp [k]; split <;> omega
    apply use b (by constructor <;> rw [PD.FK.mem_latticeRectangle] <;>
      dsimp [b,LatticeBond.source,LatticeBond.target] <;> omega) false
    · dsimp [b,LatticeBond.faceBase,rectangleExteriorFaces]
      exact Or.inl (by omega)
    · simp only [LatticeBond.toSym2,Sym2.mem_iff]
      by_cases hc : z.val.2 < a.2+(h : ℤ)
      · left
        apply Prod.ext <;> dsimp [b,LatticeBond.source,k] <;> (try simp only [ite_eq_left hc]); omega
      · right
        apply Prod.ext <;> dsimp [b,LatticeBond.target,k] <;> (try simp only [ite_eq_right hc]) <;> omega
  · let k := if z.val.2 < a.2+(h : ℤ) then z.val.2 else z.val.2-1
    let b : LatticeBond := ⟨(a.1+(w : ℤ),k),.vertical⟩
    have hk : a.2 ≤ k ∧ k < a.2+(h : ℤ) := by dsimp [k]; split <;> omega
    apply use b (by constructor <;> rw [PD.FK.mem_latticeRectangle] <;>
      dsimp [b,LatticeBond.source,LatticeBond.target] <;> omega) true
    · dsimp [b,LatticeBond.faceBase,rectangleExteriorFaces]
      exact Or.inr (Or.inl (by omega))
    · simp only [LatticeBond.toSym2,Sym2.mem_iff]
      by_cases hc : z.val.2 < a.2+(h : ℤ)
      · left
        apply Prod.ext <;> dsimp [b,LatticeBond.source,k] <;> (try simp only [ite_eq_left hc]); omega
      · right
        apply Prod.ext <;> dsimp [b,LatticeBond.target,k] <;> (try simp only [ite_eq_right hc]) <;> omega
  · let k := if z.val.1 < a.1+(w : ℤ) then z.val.1 else z.val.1-1
    let b : LatticeBond := ⟨(k,a.2),.horizontal⟩
    have hk : a.1 ≤ k ∧ k < a.1+(w : ℤ) := by dsimp [k]; split <;> omega
    apply use b (by constructor <;> rw [PD.FK.mem_latticeRectangle] <;>
      dsimp [b,LatticeBond.source,LatticeBond.target] <;> omega) false
    · dsimp [b,LatticeBond.faceBase,rectangleExteriorFaces]
      exact Or.inr (Or.inr (Or.inl (by omega)))
    · simp only [LatticeBond.toSym2,Sym2.mem_iff]
      by_cases hc : z.val.1 < a.1+(w : ℤ)
      · left
        apply Prod.ext <;> dsimp [b,LatticeBond.source,k] <;> (try simp only [ite_eq_left hc]); omega
      · right
        apply Prod.ext <;> dsimp [b,LatticeBond.target,k] <;> (try simp only [ite_eq_right hc]) <;> omega
  · let k := if z.val.1 < a.1+(w : ℤ) then z.val.1 else z.val.1-1
    let b : LatticeBond := ⟨(k,a.2+(h : ℤ)),.horizontal⟩
    have hk : a.1 ≤ k ∧ k < a.1+(w : ℤ) := by dsimp [k]; split <;> omega
    apply use b (by constructor <;> rw [PD.FK.mem_latticeRectangle] <;>
      dsimp [b,LatticeBond.source,LatticeBond.target] <;> omega) true
    · dsimp [b,LatticeBond.faceBase,rectangleExteriorFaces]
      exact Or.inr (Or.inr (Or.inr (by omega)))
    · simp only [LatticeBond.toSym2,Sym2.mem_iff]
      by_cases hc : z.val.1 < a.1+(w : ℤ)
      · left
        apply Prod.ext <;> dsimp [b,LatticeBond.source,k] <;> (try simp only [ite_eq_left hc]); omega
      · right
        apply Prod.ext <;> dsimp [b,LatticeBond.target,k] <;> (try simp only [ite_eq_right hc]) <;> omega

/-- The frozen physical vertex boundary of the original rectangle is part
of the queried-adjacent raw boundary. -/
theorem frozenVertexBoundary_subset_sourceMarkedRawBoundaryVertices
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    frozenVertexBoundary (PD.FK.latticeRectangle a w h) ⊆
      sourceMarkedRawBoundaryVertices a w h u v A := by
  intro z hz
  obtain ⟨hzIn,y,hyAdj,hyOut⟩ := hz
  apply sourceMarkedRawBoundaryVertices_of_rectangle_side a w h hw hh u v z A
  have hzB := (PD.FK.mem_latticeRectangle a z.val w h).mp z.property
  have hyB : ¬((a.1 ≤ y.1 ∧ y.1 ≤ a.1+(w : ℤ)) ∧ a.2 ≤ y.2 ∧ y.2 ≤ a.2+(h : ℤ)) := by
    simpa only [PD.FK.mem_latticeRectangle] using hyOut
  change |z.val.1-y.1|+|z.val.2-y.2| = 1 at hyAdj
  simp only [abs_eq_max_neg] at hyAdj
  omega

end
end PottsContinuity.Thm3.Prop4
