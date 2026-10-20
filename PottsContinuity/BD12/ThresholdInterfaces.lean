module

public import PottsContinuity.BD12.ReverseThresholdContracts
public import PottsContinuity.Coincidence.Countability
public import PottsContinuity.PlanarTopology.Noncoexistence

/-! The independent inputs to genuine-threshold identification are discharged. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK

/-- `PlanarTopology.planar_noncoexistence` supplies precisely the full planar
non-coexistence input. -/
theorem planar_noncoexistence_contract : PlanarNonCoexistenceContract :=
  PlanarTopology.planar_noncoexistence

/-- The dense-coincidence theorem
`Coincidence.exists_coincident_free_wired_limits_in_interval` gives precisely the frozen
every-exhaustion limits requested by the reverse-threshold argument. -/
theorem dense_coincidence_contract (q : Set.Ici (1 : ℝ)) : DenseCoincidenceContract q := by
  intro a b ha hab hb
  obtain ⟨p,hpa,hpb,μ₀,μ₁,hμ₀,hμ₁,heq⟩ :=
    Coincidence.exists_coincident_free_wired_limits_in_interval q a b ha.le hab hb.le
  refine ⟨⟨p,⟨p.property.1.le,p.property.2.le⟩⟩,⟨hpa,hpb⟩,μ₀,μ₁,?_,?_,heq⟩
  · exact hμ₀
  · exact hμ₁

end PottsContinuity.BD12
