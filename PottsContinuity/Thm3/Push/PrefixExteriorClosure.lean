module

public import PottsContinuity.Thm3.Push.ConfinedPrefixCrosscutGeometry
public import PottsContinuity.Thm3.Push.FirstContactPrefix
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarTopology
noncomputable section

/-- A first-contact prefix meets the upward ray from its endpoint only at
that endpoint. No choice rule or extremality is involved. -/
theorem firstContact_prefix_upper_ray_unique
    (a x y t : ℤ) (hyt : y ≤ t)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,t))
    (hfirst : firstContactTrace {z | z.1 = x-1 ∧ y ≤ z.2} p.support = some p.support)
    (z : LatticeVertex) (hz : z ∈ p.support)
    (hcol : z.1 = x-1) (hheight : t ≤ z.2) : z = (x-1,t) := by
  have hc := (firstContactTrace_fixed_iff_firstContact_at_length p
    {z | z.1 = x-1 ∧ y ≤ z.2} ⟨rfl,hyt⟩).mp hfirst
  have hs : (p.take p.length).support = p.support := by
    rw [SimpleGraph.Walk.support_take,← p.length_support,List.take_length]
  have he := firstContact_prefix_target_unique p _ p.length hc z (hs.symm ▸ hz)
    ⟨hcol,hyt.trans hheight⟩
  simpa only [SimpleGraph.Walk.getVert_length] using he

end
end PottsContinuity.Push
