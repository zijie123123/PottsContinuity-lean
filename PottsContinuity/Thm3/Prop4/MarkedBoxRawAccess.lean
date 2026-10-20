module

public import PottsContinuity.Thm3.Prop4.MarkedRectangleRawAccess
public import PottsContinuity.Thm3.Prop4.MarkedBoxRawReveal

/-! # Actual raw endpoint access on the original sampled box -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedBoxRawAccessEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _
local instance markedBoxRawAccessRectangleEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Exact original labels on the lower trace in the actual transported sample. -/
theorem markedLowerBoxTrace_labels (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    (markedLowerBoxTrace n u v A).image Subtype.val =
      markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)
        (configurationIso (boxTubeRectangleIso n) A) := by
  have hh := congrFun (boxTraceOnRectangle_markedLowerBoxTrace n u v)
    (configurationIso (boxTubeRectangleIso n) A)
  dsimp only [boxTraceOnRectangle] at hh
  erw [Equiv.symm_apply_apply] at hh
  exact hh

/-- Every actual original-box lower raw query endpoint has no top access
avoiding the SAME nonempty concrete lower trace. -/
theorem markedLowerBoxRawReveal_endpoint_no_top_access (n : ℕ)
    (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hne : (markedLowerBoxTrace n u v A).Nonempty)
    (e : (finiteLatticeGraph (box n)).edgeSet)
    (he : e ∈ markedLowerBoxRawReveal n u v A)
    (x : (box n : Set LatticeVertex)) (hx : x ∈ e.val) :
    ¬traceTopAccessible n ((markedLowerBoxTrace n u v A).image Subtype.val) x.val := by
  classical
  have hemap : configurationIsoEdgeEquiv (boxTubeRectangleIso n) e ∈
      configurationIso (boxTubeRectangleIso n) (markedLowerBoxRawReveal n u v A) :=
    Finset.mem_map.mpr ⟨e,he,rfl⟩
  dsimp only [markedLowerBoxRawReveal] at hemap
  erw [Equiv.apply_symm_apply] at hemap
  have hxmap : boxTubeRectangleIso n x ∈
      (configurationIsoEdgeEquiv (boxTubeRectangleIso n) e).val := by
    change boxTubeRectangleIso n x ∈ Sym2.map (boxTubeRectangleIso n) e.val
    exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  have hnerect : (markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)
      (configurationIso (boxTubeRectangleIso n) A)).Nonempty := by
    rw [← markedLowerBoxTrace_labels]
    exact hne.image _
  rw [markedLowerBoxTrace_labels]
  exact markedLowerDualReveal_endpoint_no_top_access n (boxTubeRectangleIso n u)
    (boxTubeRectangleIso n v) hu hv _ hnerect _ hemap (boxTubeRectangleIso n x) hxmap

end
end PottsContinuity.Thm3.Prop4
