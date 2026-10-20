module

public import PottsContinuity.PlanarTopology.SlitScreenCrosscut

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.FiniteFK FKC.Medial Thm4Plane
noncomputable section

/-- The source three-screen event supplies a genuine separating sampled arch,
with the original two bottom terminal labels and its exact crossed-bond cut. -/
theorem generalCEvent_exists_separating_arch (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16*m))) (hC : A ∈ generalCEvent (16*m)) :
    ∃ lb ∈ generalScreenBottomTerminals (16*m) (generalScreenLeftFaceBases (16*m)),
    ∃ rb ∈ generalScreenBottomTerminals (16*m) (generalScreenRightFaceBases (16*m)),
    ∃ p : (generalScreenActualClosedDualGraph (16*m) A
      (generalScreenArchFaceBases (16*m))).Walk lb rb,
      p.IsPath ∧
      (∀ e ∈ screenArchCrossedBondConfiguration m A p, e ∉ A) ∧
      (∀ e ∈ screenArchCrossedBondConfiguration m A p, ¬ screenTargetCapInternalEdge m e) ∧
      (∀ v ∈ slitBoxWiredArc (16*m),
        v ∉ screenTargetCapEdgeDeletedComponent m (screenArchCrossedBondConfiguration m A p)) := by
  obtain ⟨lb,hlb,rb,hrb,p,hp,hExterior⟩ :=
    generalCEvent_implies_bottomDualSimpleArch_outsideTargetBox m hm A hC
  exact ⟨lb,hlb,rb,hrb,p,hp,
    fun e he => screenArchCrossedBondConfiguration_mem_closed m hm A p e he,
    screenArchCrossedBondConfiguration_avoids_capInternalEdge_of_exteriorSupport m A p hExterior,
    slitScreen_crossedDualWalk_separatesCapFromWiredArc m hm A lb rb hlb hrb p⟩

end
end PottsContinuity.PlanarTopology
