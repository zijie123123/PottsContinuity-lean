module

public import PottsContinuity.PlanarTopology.SampledBoundaryStarScreen
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial

/-- The normalized forms of the four actual lattice bonds incident to a vertex. -/
theorem latticeBond_incident_cases (b : LatticeBond) (z : LatticeVertex)
    (hz : b.source = z ∨ b.target = z) :
    b = ⟨z,.horizontal⟩ ∨ b = ⟨(z.1-1,z.2),.horizontal⟩ ∨
      b = ⟨z,.vertical⟩ ∨ b = ⟨(z.1,z.2-1),.vertical⟩ := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis with
  | horizontal =>
    rcases hz with hs | ht
    · exact Or.inl (congrArg (fun v => (⟨v,.horizontal⟩ : LatticeBond)) hs)
    · right; left
      have hx := congrArg Prod.fst ht
      have hy := congrArg Prod.snd ht
      congr 1
      apply Prod.ext <;> dsimp [LatticeBond.target] at hx hy ⊢ <;> omega
  | vertical =>
    rcases hz with hs | ht
    · exact Or.inr (Or.inr (Or.inl (congrArg (fun v => (⟨v,.vertical⟩ : LatticeBond)) hs)))
    · right; right; right
      have hx := congrArg Prod.fst ht
      have hy := congrArg Prod.snd ht
      congr 1
      apply Prod.ext <;> dsimp [LatticeBond.target] at hx hy ⊢ <;> omega

/-- Either face of any genuine sampled closed incident bond is an actual
four-cycle port. This realizes ports from original bonds even at corners. -/
theorem rectangle_closed_star_bond_face_is_actual_port
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (z : LatticeVertex) (b : RectanglePrimalBond a w h)
    (hincident : b.val.source = z ∨ b.val.target = z)
    (hclosed : rectanglePrimalBondToEdge a w h b ∉ A) (f : LatticeVertex)
    (hf : f = b.val.faceBase false ∨ f = b.val.faceBase true) :
    fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) f := by
  have hstep := rectangleSampledClosedDualGraph_adj_of_closed_bond a w h A b hclosed
  rw [dualBondOfPrimal_source,dualBondOfPrimal_target] at hstep
  rcases latticeBond_incident_cases b.val z hincident with hb | hb | hb | hb
  · rw [hb] at hstep hf
    exact Or.inr (Or.inl ⟨hstep,hf⟩)
  · rw [hb] at hstep hf
    exact Or.inr (Or.inr (Or.inr ⟨hstep.symm,hf.symm⟩))
  · rw [hb] at hstep hf
    exact Or.inr (Or.inr (Or.inl ⟨hstep.symm,hf.symm⟩))
  · rw [hb] at hstep hf
    exact Or.inl ⟨hstep,hf⟩

/-- Closing the genuine sampled star joins faces supplied by any two of its
actual original incident bonds, including boundary and corner cases. -/
theorem rectangle_closed_star_incident_bond_faces_connected
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (A : Configuration (rectangleGraph a w h)) (z : RectangleVertex a w h)
    (hclosed : ∀ b : RectanglePrimalBond a w h,
      b.val.source = z.val ∨ b.val.target = z.val → rectanglePrimalBondToEdge a w h b ∉ A)
    (b c : RectanglePrimalBond a w h)
    (hb : b.val.source = z.val ∨ b.val.target = z.val)
    (hc : c.val.source = z.val ∨ c.val.target = z.val)
    (f g : LatticeVertex)
    (hf : f = b.val.faceBase false ∨ f = b.val.faceBase true)
    (hg : g = c.val.faceBase false ∨ g = c.val.faceBase true) :
    (rectangleSampledClosedDualGraph a w h A).Reachable f g :=
  rectangle_closed_boundary_star_ports_connected a w h hw hh A z hclosed f g
    (rectangle_closed_star_bond_face_is_actual_port a w h A z.val b hb (hclosed b hb) f hf)
    (rectangle_closed_star_bond_face_is_actual_port a w h A z.val c hc (hclosed c hc) g hg)

end PottsContinuity.PlanarTopology
