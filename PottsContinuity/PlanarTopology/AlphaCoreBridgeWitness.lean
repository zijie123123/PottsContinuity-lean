module

public import PottsContinuity.PlanarTopology.KSTArmCoreBridge
public import PottsContinuity.PlanarTopology.AlphaCoreToBottom

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The induced core connection has an original open walk in the literal box. -/
theorem alpha_core_bridge_walk_witness (k : ℕ) (hk : 1 ≤ k) (ω : LatticeConfiguration)
    (hω : ω ∈ alphaCoreBridge k) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u ∈ alphaCoreLeftTargets k ∧ v ∈ alphaCoreRightTargets k ∧
      kstPathIn p (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1) := by
  have hS := rectangleDualInterior_eq_rectangle (-65*(k : ℤ),-64*(k : ℤ))
    (130*k) (128*k) (by omega) (by omega)
  change ∃ u, u.val ∈ alphaCoreLeftTargets k ∧ ∃ v, v.val ∈ alphaCoreRightTargets k ∧
    ActualConnected (PD.squareLattice.induce (rectangleDualInterior
      (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) : Set LatticeVertex))
      (embeddedRestriction _ (frozenEdgeEmbedding (rectangleDualInterior
        (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) ω) u v at hω
  rw [hS] at hω
  obtain ⟨u,hu,v,hv,hconn⟩ := hω
  obtain ⟨r,hr⟩ := hconn.exists_isPath
  let p := r.map (rectangleOpenGraphToSquare _ _ _ _)
  refine ⟨u.val,v.val,p,kstPathOpen_of_rectangle_walk _ _ _ ω r,hu,hv,?_⟩
  intro z hz
  obtain ⟨z',_,he⟩ := rectangleOpenWalk_mapped_support_preimage _ _ _ _ r hz
  have hh := (mem_latticeRectangle _ z'.val (130*k-1) (128*k-1)).mp z'.property
  rw [he] at hh
  simp only at hh
  exact ⟨hh.1.1,by omega,hh.2.1,by omega⟩

end
end PottsContinuity.PlanarTopology
