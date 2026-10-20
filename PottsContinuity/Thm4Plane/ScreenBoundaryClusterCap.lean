module

public import PottsContinuity.Thm4Plane.GeneralScreenSetup
public import PottsContinuity.Thm4Plane.ScreenFreeComponent
public import PottsContinuity.Exploration.BoundaryClusterDMP
public import PottsContinuity.PlanarTopology.SlitScreenSeparatingArch

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Exploration

/-- The connector arch prevents every vertex of the clipped target cap from
belonging to the open cluster touching the wired slit boundary. -/
theorem screenTargetCap_subset_boundaryClusterInterior_of_sourceScreen_and_connector
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m))
    (hC : A ∈ slitScreenConnectorEvent m) :
    screenTargetCap m ⊆
      boundaryClusterInterior
        (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) A := by
  have hC' : A ∈ generalCEvent (16 * m) := by
    rw [generalCEvent_sixteen_eq]
    exact hC
  obtain ⟨lb, hlb, rb, hrb, p, hp, _hclosed, _havoid, hcrosscut⟩ :=
    PottsContinuity.PlanarTopology.generalCEvent_exists_separating_arch
      m hm A hC'
  have hseparated := screenTargetCap_openConnectionToWiredArc_false_of_crosscut
    m hm A hE lb rb hlb hrb p hp
      (by
        intro _ _ v hv
        exact hcrosscut v hv)
  intro u hu
  change u ∉ boundaryTouchCluster
    (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) A
  rintro ⟨b, hb, hconnect⟩
  exact hseparated u hu b hb hconnect.symm

end PottsContinuity.Thm4Plane
