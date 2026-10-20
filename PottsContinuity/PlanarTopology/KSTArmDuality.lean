module

public import PottsContinuity.PlanarTopology.KSTArmRectangleBridge
public import PottsContinuity.BD12.WholePlaneRectangleDuality

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.Duality BD12
noncomputable section

/-- A genuine open dual connection between the literal alpha-complementary
face-base ports. This reads only actual dual bonds of the sampled rectangle;
no virtual caps, boundary wiring, or same-centred-target convention occurs. -/
def alphaDualPortEvent (k : ℕ) : Set LatticeConfiguration :=
  {η | ∃ b : RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
    b.val ∈ alphaLeftDualPorts k ∧
    ∃ d : RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
      d.val ∈ alphaRightDualPorts k ∧
      ActualConnected (rectangleDualGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))
        (embeddedRestriction _ (rectangleDualEdgeToSquareEdge
          (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)) η) b d}

/-- The actual whole-plane dual restriction equals the true finite complement,
including every exterior face-base port. -/
theorem alphaDualPortEvent_dual_iff (k : ℕ) (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph ω ∈ alphaDualPortEvent k ↔
      alphaTargetDualCrossing k
        (embeddedRestriction (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))
          (frozenEdgeEmbedding (PD.FK.latticeRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) ω) := by
  unfold alphaDualPortEvent alphaTargetDualCrossing
  simp only [Set.mem_ofPred_eq]
  rw [embeddedRestriction_dual,rectanglePrimalDualConfigurationEquiv_apply]
  rfl

/-- Corrected exact arm-complement identity: the dual targets carry their true
half-cell offsets. This replaces the source's informal same-centred bridge
identity and is valid for every whole-plane state at integral alpha scale. -/
theorem kstArm_compl_eq_dualPortEvent (k : ℕ) (hk : 1 ≤ k) :
    (kstArm (64*k))ᶜ = wholePlaneDualConfigurationHomeomorph ⁻¹' alphaDualPortEvent k := by
  classical
  ext ω
  change (¬ω ∈ kstArm (64*k)) ↔ wholePlaneDualConfigurationHomeomorph ω ∈ alphaDualPortEvent k
  rw [kstArm_iff_alpha_target_primal,alphaDualPortEvent_dual_iff]
  simpa only [not_not] using not_congr (alpha_target_crossing_iff_not_dual k hk
    (embeddedRestriction (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))
      (frozenEdgeEmbedding (PD.FK.latticeRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) ω))

end
end PottsContinuity.PlanarTopology
