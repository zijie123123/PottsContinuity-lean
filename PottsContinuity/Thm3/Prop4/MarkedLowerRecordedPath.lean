module

public import PottsContinuity.Thm3.Prop4.RecordedWalkPullback
public import PottsContinuity.Thm3.Prop4.MarkedBoxRawAccess

/-! # Whole-support recorded paths for the actual lower box trace -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite PlanarTopology
noncomputable section
local instance markedLowerPathBoxEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _
local instance markedLowerPathRectangleEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The SAME nonempty lower box trace is the entire support of an actual
prescribed open walk in its original raw recorded configuration. -/
theorem markedLowerBoxTrace_recorded_walk (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hne : (markedLowerBoxTrace n u v A).Nonempty) :
    ∃ p : (openGraph (finiteLatticeGraph (box n))
      (A ∩ markedLowerBoxRawReveal n u v A)).Walk u v,
      p.support.toFinset = markedLowerBoxTrace n u v A := by
  classical
  obtain ⟨z,hz⟩ := hne
  obtain ⟨y,hy,_⟩ := Finset.mem_map.mp hz
  obtain ⟨p,hp⟩ := recordedConnectingFrontierTrace_exists_recorded_walk
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
      (configurationIso (boxTubeRectangleIso n) A))
    (configurationIso (boxTubeRectangleIso n) A ∩
      markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
        (configurationIso (boxTubeRectangleIso n) A))
    (rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
    (boxTubeRectangleIso n u) (boxTubeRectangleIso n v) ⟨y,hy⟩
  have hB : (configurationIso (boxTubeRectangleIso n)).symm
      (configurationIso (boxTubeRectangleIso n) A ∩
        markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
          (configurationIso (boxTubeRectangleIso n) A)) =
      A ∩ markedLowerBoxRawReveal n u v A := by
    erw [Push.configurationIso_symm_inter,Equiv.symm_apply_apply]
    rfl
  have hh := recorded_walk_pullback_support (boxTubeRectangleIso n) _ u v p _ hp
  erw [hB] at hh
  obtain ⟨q,hq⟩ := hh
  refine ⟨q,?_⟩
  ext x
  simp only [markedLowerBoxTrace,List.mem_toFinset]
  have h := Finset.ext_iff.mp hq x
  simp only [List.mem_toFinset] at h
  convert h using 1
  rfl

end
end PottsContinuity.Thm3.Prop4
