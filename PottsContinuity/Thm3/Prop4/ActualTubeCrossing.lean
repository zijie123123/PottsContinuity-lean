module

public import PottsContinuity.Thm3.Prop4.RadiusTube
public import PottsContinuity.BD12.RectangleOpenGraphs

/-!
# The actual horizontal crossing event in a Euclidean tube

The finite graph retains every tube vertex. Crossing uses original open
edges and endpoints on the two original box faces, with no boundary wiring.
Negative or zero tube radii give the genuine empty carrier.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite
noncomputable section

/-- Original-state horizontal crossing of the finite Euclidean tube. -/
def tubeHorizontalCrossingEvent (n : ℕ) (R : ℝ) (u v : LatticeVertex) : Set LatticeConfiguration :=
  BD12.embeddedRestriction (PD.squareLattice.induce (radiusTube n R u v : Set LatticeVertex))
    (frozenEdgeEmbedding (radiusTube n R u v)) ⁻¹'
    {A | ∃ a b : (radiusTube n R u v : Set LatticeVertex),
      a.val.1 = -(n : ℤ) ∧ b.val.1 = (n : ℤ) ∧ ActualConnected _ A a b}

/-- This complete tube crossing event depends on finitely many original edges. -/
theorem tubeHorizontalCrossingEvent_isCylinder (n : ℕ) (R : ℝ) (u v : LatticeVertex) :
    IsCylinder (tubeHorizontalCrossingEvent n R u v) :=
  BD12.embeddedRestriction_isCylinder _ _ _

/-- Any genuine original walk confined to the tube gives its actual finite crossing. -/
theorem tubeHorizontalCrossingEvent_of_walk (n : ℕ) (R : ℝ) (u v : LatticeVertex)
    (ω : LatticeConfiguration) {a b : LatticeVertex}
    (p : (PD.rcInfiniteOpenGraph ω).Walk a b)
    (ha : a.1 = -(n : ℤ)) (hb : b.1 = (n : ℤ))
    (hp : ∀ z ∈ p.support, z ∈ radiusTube n R u v) :
    ω ∈ tubeHorizontalCrossingEvent n R u v := by
  let a' : (radiusTube n R u v : Set LatticeVertex) := ⟨a,hp a p.start_mem_support⟩
  let b' : (radiusTube n R u v : Set LatticeVertex) := ⟨b,hp b p.end_mem_support⟩
  refine ⟨a',b',ha,hb,?_⟩
  change (openGraph _ _).Reachable a' b'
  rw [BD12.embeddedRestriction_domainGraph]
  exact ⟨p.induce _ hp⟩

end
end PottsContinuity.Thm3.Prop4
