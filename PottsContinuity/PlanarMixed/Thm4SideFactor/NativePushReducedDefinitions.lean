module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushBridge
public import PottsContinuity.PD.FK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open RSW PD.FK PD.Duality
noncomputable section

abbrev NativeSideVertex (m : ℕ) := RectangleVertex (-16*(m:ℤ)-1,0) (32*m+1) (15*m)
abbrev nativeSideFullGraph (m : ℕ) := rectangleGraph (-16*(m:ℤ)-1,0) (32*m+1) (15*m)
def nativeSideFullBoundary (m : ℕ) : BoundaryCondition (NativeSideVertex m) :=
  BoundaryCondition.wired {v | v.val.1 = -16*(m:ℤ)-1 ∨
    v.val.1 = 16*(m:ℤ) ∨ v.val.2 = 15*(m:ℤ)}
def nativeSideWiredEdges (m : ℕ) : Configuration (nativeSideFullGraph m) := by
  classical
  exact Finset.univ.filter (fun e => ∀ z ∈ e.val, z ∈ (nativeSideFullBoundary m).boundary)
def nativeSideReducedGraph (m : ℕ) :=
  edgeRestriction (nativeSideFullGraph m) (nativeSideWiredEdges m)
def nativeSideReducedCrossingEvent (m : ℕ) : Set (Configuration (nativeSideReducedGraph m)) :=
  {C | (edgeRestrictionConfigurationEquiv (nativeSideFullGraph m) (nativeSideWiredEdges m) C).val ∈
    Push.rectangleBandConnectionEvent (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)}

theorem mem_nativeSideWiredEdges_pair (m : ℕ) (u v : NativeSideVertex m)
    (huv : (nativeSideFullGraph m).Adj u v) :
    (⟨s(u,v),(nativeSideFullGraph m).mem_edgeSet.mpr huv⟩ : (nativeSideFullGraph m).edgeSet) ∈
      nativeSideWiredEdges m ↔
    u ∈ (nativeSideFullBoundary m).boundary ∧ v ∈ (nativeSideFullBoundary m).boundary := by
  classical
  simp only [nativeSideWiredEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h
    exact ⟨h u (by simp),h v (by simp)⟩
  · rintro ⟨hu,hv⟩ z hz
    rcases (Sym2.mem_iff').mp hz with rfl | rfl
    · exact hu
    · exact hv

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
