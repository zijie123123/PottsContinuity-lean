module

public import PottsContinuity.Thm3.Prop4.SampledStarPorts
public import PottsContinuity.Thm3.Prop4.TubeGeometry
public import PottsContinuity.Thm3.Prop4.SampledArmCorrelation
public import PottsContinuity.PlanarTopology.BoxSampledDualScreen

/-!
# Actual sampled star roots at a maximal upper excursion

An original vertex is an actual dual face port except at the unused upper
right corner face. There the adjacent top face is a genuine port and already
belongs to the upper complementary arc.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- Every original box vertex except the unused upper-right face is a genuine
sampled star port at that same original vertex. -/
theorem box_vertex_sampled_star_port (n : ℕ) (z : (box n : Set LatticeVertex))
    (hz : z.val ≠ ((n : ℤ),(n : ℤ))) :
    z.val ∈ sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      ⟨z.val,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact z.property⟩ := by
  have hb : z.val ∈ box n := z.property
  simp only [box,Finset.mem_product,Finset.mem_Icc] at hb
  have h0 : z.val ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    exact z.property
  by_cases hx : z.val.1 < n
  · let e : LatticeBond := ⟨z.val,.horizontal⟩
    have h1 : e.target ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
      rw [PlanarTopology.latticeRectangle_neg_eq_box]
      simp only [e,LatticeBond.target,box,PD.box,Finset.mem_product,Finset.mem_Icc]
      omega
    exact ⟨⟨e,h0,h1⟩,Or.inl rfl,Or.inr rfl⟩
  · have hy : z.val.2 < n := by
      have hx' : z.val.1 = n := by omega
      by_contra h
      apply hz
      exact Prod.ext hx' (by omega)
    let e : LatticeBond := ⟨z.val,.vertical⟩
    have h1 : e.target ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
      rw [PlanarTopology.latticeRectangle_neg_eq_box]
      simp only [e,LatticeBond.target,box,PD.box,Finset.mem_product,Finset.mem_Icc]
      omega
    exact ⟨⟨e,h0,h1⟩,Or.inl rfl,Or.inr rfl⟩

/-- The actual adjacent top face is a sampled star port at the upper-right
original corner, although the outer corner face itself is not a port. -/
theorem upperRight_corner_top_sampled_star_port {n : ℕ} (hn : 1 ≤ n)
    (z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hz : z.val = ((n : ℤ),(n : ℤ))) :
    ((n : ℤ)-1,(n : ℤ)) ∈ sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) z := by
  let e : LatticeBond := ⟨((n : ℤ)-1,(n : ℤ)),.horizontal⟩
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have h0 : e.source ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    simp only [e,LatticeBond.source,PD.box,Finset.mem_product,Finset.mem_Icc]
    omega
  have h1 : e.target ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    simp only [e,LatticeBond.target,PD.box,Finset.mem_product,Finset.mem_Icc]
    omega
  refine ⟨⟨e,h0,h1⟩,Or.inr ?_,Or.inr rfl⟩
  rw [hz]
  simp only [e,LatticeBond.target,sub_add_cancel]

/-- Every configuration has a length-zero upper arm from a genuine corner
star port, without adding an unsampled exterior-corner bond. -/
theorem upperRight_corner_sampled_upper_arm {n : ℕ} (hn : 1 ≤ n)
    (z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hz : z.val = ((n : ℤ),(n : ℤ))) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) :
    A ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) z)
      (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) (fun _ => True) := by
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  refine ⟨((n : ℤ)-1,(n : ℤ)),upperRight_corner_top_sampled_star_port hn z hz,
    ((n : ℤ)-1,(n : ℤ)),?_,SimpleGraph.Walk.nil,fun _ _ => True.intro⟩
  apply Or.inl
  dsimp
  exact ⟨by omega,by omega,by omega⟩

end
end PottsContinuity.Thm3.Prop4
