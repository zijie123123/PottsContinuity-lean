module

public import PottsContinuity.Thm3.RSW.TiltedReducedActiveGeometry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- The exact frozen boundary produced by genuine finite duality. -/
abbrev tiltedReducedFiniteDualBoundary (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :=
  embeddedSubgraphInducedDualBoundary (tiltedReducedHostEmbedding N M t)
    (tiltedReducedHost_map_le N M t) (tiltedReducedHostRemovedState N M t ht)

end
end PottsContinuity.RSW
