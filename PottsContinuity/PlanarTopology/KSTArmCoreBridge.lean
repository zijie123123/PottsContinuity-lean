module

public import PottsContinuity.PlanarTopology.AlphaCoreTargets
public import PottsContinuity.PlanarTopology.KSTArmDuality

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial BD12
noncomputable section

/-- An original open connection in the odd-sided interior dual face box,
between its literal left/right three-piece targets. All edges are ordinary
whole-plane lattice bonds, with the supplied configuration read directly. -/
def alphaCoreBridge (k : ℕ) : Set LatticeConfiguration :=
  {η | ∃ u : {z : LatticeVertex // z ∈ rectangleDualInterior
      (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)},
    u.val ∈ alphaCoreLeftTargets k ∧
    ∃ v : {z : LatticeVertex // z ∈ rectangleDualInterior
      (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)},
      v.val ∈ alphaCoreRightTargets k ∧
      ActualConnected (PD.squareLattice.induce (rectangleDualInterior
        (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) : Set LatticeVertex))
        (embeddedRestriction _ (frozenEdgeEmbedding (rectangleDualInterior
          (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) η) u v}

/-- Contract all exterior dual-port pendants. Connectivity, target ordering,
and every retained original open bond survive in the exact interior face box. -/
theorem alpha_dual_ports_subset_core_bridge (k : ℕ) (hk : 1 ≤ k) :
    alphaDualPortEvent k ⊆ alphaCoreBridge k := by
  rintro η ⟨b,hb,d,hd,hbd⟩
  have hcore := rectangle_dual_reachable_core (-65*(k : ℤ),-64*(k : ℤ))
    (130*k) (128*k) (by omega) (by omega) η hbd
  rw [← embeddedRestriction_domainGraph] at hcore
  exact ⟨_,alpha_left_port_core_target k hk b.val hb,
    _,alpha_right_port_core_target k hk d.val hd,hcore⟩

/-- Absence of the actual arm forces the genuine odd-sided dual core bridge.
This inclusion is enough for the dual estimate; no converse is asserted after
contracting possibly closed pendant bonds. -/
theorem kstArm_compl_subset_dual_core_bridge (k : ℕ) (hk : 1 ≤ k) :
    (kstArm (64*k))ᶜ ⊆ wholePlaneDualConfigurationHomeomorph ⁻¹' alphaCoreBridge k := by
  intro ω hω
  apply alpha_dual_ports_subset_core_bridge k hk
  have hh : ω ∈ wholePlaneDualConfigurationHomeomorph ⁻¹' alphaDualPortEvent k := by
    rwa [← kstArm_compl_eq_dualPortEvent k hk]
  exact hh

end
end PottsContinuity.PlanarTopology
