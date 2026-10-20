module

public import PottsContinuity.Thm3.Prop4.SupportingLineExteriorArc
public import PottsContinuity.Thm3.Prop4.SampledArmCorrelation

/-!
# A sampled upper-half-plane exit has the correct complementary target

Every nontrivial arm uses the two actual faces of its last sampled crossing
bond. A zero-length arm keeps its explicit boundary-root geometric premise.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
local instance supportingArmTargetEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- A sampled arm above the supporting line reaches the upper complementary
arc. The only length-zero input is membership of an exterior root in that arc. -/
theorem supporting_line_sampled_arm_target (n : ℕ) (t b : ℝ)
    (u v z : LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (hu : (u.2 : ℝ) ≤ t*u.1+b) (hv : (v.2 : ℝ) ≤ t*v.1+b)
    (hzero : z ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) →
      z ∈ PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) :
    sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {z}
      (rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) : Set LatticeVertex)
      (fun y => b ≤ tiltedHeight t y) ⊆
    sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {z}
      (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
      (fun y => b ≤ tiltedHeight t y) := by
  rintro A ⟨f,hf,s,hs,p,hp⟩
  have hfz : f = z := hf
  have harc : s ∈ PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v := by
    cases p with
    | nil => simpa only [hfz] using hzero (hfz ▸ hs)
    | @cons s d f hsd q =>
      obtain ⟨e,_,hpair⟩ := hsd
      have hsHeight := hp s (List.mem_cons_self)
      have hdHeight := hp d (List.mem_cons_of_mem _ q.start_mem_support)
      have h0 : b ≤ tiltedHeight t ((rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).faceBase false) := by
        rw [← rectangleDualEdgeSource_faceBase _ _ _ e]
        rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hsHeight
        · exact hdHeight
      have h1 : b ≤ tiltedHeight t ((rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).faceBase true) := by
        rw [← rectangleDualEdgeTarget_faceBase _ _ _ e]
        rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hdHeight
        · exact hsHeight
      have hface : s = e.crossingBond.source ∨ s = e.crossingBond.target := by
        rcases hpair with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      have hface' : s = (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).faceBase false ∨
          s = (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e.primalEdge).faceBase true := by
        exact hface.imp (fun h => h.trans (rectangleDualEdgeSource_faceBase _ _ _ e))
          (fun h => h.trans (rectangleDualEdgeTarget_faceBase _ _ _ e))
      exact supporting_line_sampled_exterior_face_upper_arc n t b u v huB hvB huX hvX hu hv
        (rectanglePrimalEdgeBondEquiv _ _ _ e.primalEdge) s hface' hs h0 h1
  exact ⟨f,hf,s,harc,p,hp⟩

end
end PottsContinuity.Thm3.Prop4
