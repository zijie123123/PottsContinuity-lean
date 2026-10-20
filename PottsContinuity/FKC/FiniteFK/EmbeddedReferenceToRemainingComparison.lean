-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EmbeddedReferenceToRemainingComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EmbeddedClosedInteriorBoundary
public import PottsContinuity.FKC.FiniteFK.EmbeddedClosedInteriorOuterComparison
public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryComparison
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  {G : SimpleGraph V} {H K : SimpleGraph W} (f : V ↪ W)
  (hGH : G.map f ≤ H) (hGK : G.map f ≤ K)

include f hGH hGK

/-- Compare a reference connection to its actual finite embedded restriction,
when the reference boundary avoids the embedded interior and wiring the target
set is dominated by the remaining boundary pullback. The event throughout is actual
configuration connectivity to boundary membership. -/
theorem embedded_reference_connection_probability_le_remaining
    (q : ClusterWeight) (ξ η : BoundaryCondition W) (B : Set V) (x : V)
    (hxB : x ∉ B)
    (hclosed : ∀ ⦃v : V⦄, v ∉ B → ∀ ⦃z : W⦄, H.Adj (f v) z →
      ∃ w : V, f w = z ∧ G.Adj v w)
    (hξavoid : ∀ ⦃v : V⦄, v ∉ B → f v ∉ ξ.boundary)
    (hpart : (BoundaryCondition.wired B).partition ≤
      (isolatedExtensionPullbackBoundary f η).partition) :
    (measure H q ξ
      {A | ∃ z ∈ ξ.boundary, ActualConnected H A (f x) z}).toReal ≤
    (measure K q η
      {A | ∃ y ∈ B,
        ActualConnected G (embeddedConfigurationRestriction G K f hGK A) x y}).toReal := by
  let S : Set (Configuration G) :=
    {A | ∃ y ∈ B, ActualConnected G A x y}
  have hS : IsUpperSet S := by
    intro A A' hAA' hA
    obtain ⟨y, hyB, hconn⟩ := hA
    exact ⟨y, hyB, actualConnected_mono hAA' hconn⟩
  have hsubset :
      {A | ∃ z ∈ ξ.boundary, ActualConnected H A (f x) z} ⊆
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S} := by
    intro A hA
    obtain ⟨z, hzBoundary, hconn⟩ := hA
    have hzExterior : z ∉ f '' Bᶜ := by
      rintro ⟨v, hv, hvz⟩
      have hvBoundary : f v ∈ ξ.boundary := by simpa [hvz] using hzBoundary
      exact hξavoid hv hvBoundary
    obtain ⟨y, hyB, hyconn⟩ :=
      embedded_openPath_restrict_hits_boundary_of_exterior
        f hGH B hclosed x hxB z hzExterior A hconn
    exact ⟨y, hyB, hyconn⟩
  have houter :=
    embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
      f hGH q ξ B hclosed hξavoid S hS
  have hboundary := measure_boundary_comparison q
    (BoundaryCondition.wired B) (isolatedExtensionPullbackBoundary f η)
    hpart S hS
  have hremaining := embedded_boundary_probability_le
    G K f hGK q η S hS
  calc
    (measure H q ξ {A | ∃ z ∈ ξ.boundary,
        ActualConnected H A (f x) z}).toReal
      ≤ (measure H q ξ
          {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _)
              (MeasureTheory.measure_mono hsubset)
    _ ≤ (measure G q (BoundaryCondition.wired B) S).toReal := houter
    _ ≤ (measure G q (isolatedExtensionPullbackBoundary f η) S).toReal := hboundary
    _ ≤ (measure K q η
          {A | embeddedConfigurationRestriction G K f hGK A ∈ S}).toReal := hremaining

end

end PottsContinuity.FKC.FiniteFK

