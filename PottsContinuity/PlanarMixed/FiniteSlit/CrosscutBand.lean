module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutSeparation
public import PottsContinuity.PlanarMixed.FiniteSlit.ReferenceConsumers
public import PottsContinuity.PlanarMixed.OrderedCutBands
public import PottsContinuity.PlanarMixed.RankedBandGeometry

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 MeasureTheory
noncomputable section

/-- Actual bottom-to-slit paths, with their source coordinate bounds and
ordered roots. This contains geometry only, with no probability or separation field. -/
structure CrosscutData (M : ℕ) (x y : ℤ) where
  firstStart : Vertex M x
  secondStart : Vertex M x
  firstEnd : Vertex M x
  secondEnd : Vertex M x
  first : (graph M x y).Walk firstStart firstEnd
  second : (graph M x y).Walk secondStart secondEnd
  first_bottom : firstStart.val.2 = 0
  second_bottom : secondStart.val.2 = 0
  first_start_right : x ≤ firstStart.val.1
  starts_order : firstStart.val.1 < secondStart.val.1
  first_end_column : firstEnd.val.1 = x-1
  first_end_height : y ≤ firstEnd.val.2
  second_end : secondEnd.val = (x,y)
  first_bounds : ∀ w ∈ first.support,
    x-(M:ℤ) < w.val.1 ∧ w.val.1 < x+(M:ℤ)-1 ∧
    0 ≤ w.val.2 ∧ w.val.2 < (M:ℤ)
  second_bounds : ∀ w ∈ second.support,
    x ≤ w.val.1 ∧ w.val.1 < x+(M:ℤ)-1 ∧
    0 ≤ w.val.2 ∧ w.val.2 < (M:ℤ)
  disjoint : ∀ w ∈ first.support, w ∉ second.support

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
include hM hy

/-- The ordered-cut geometry is derived from the actual paths. -/
theorem orderedCuts : OrderedCutPair (graph M x y) (alpha M x) (beta M x y)
    {w | w ∈ D.first.support} {w | w ∈ D.second.support} :=
  orderedCutPair_of_slit_crosscuts M x y hM hy D.first D.second D.first_bottom
    D.second_bottom D.first_start_right D.starts_order D.first_end_column
    D.first_end_height D.second_end D.first_bounds D.second_bounds D.disjoint

/-- Five exhaustive geometric classes, using exterior reachability from the
two actual wired reference arcs and the original path supports. -/
def rank : Vertex M x → ℤ :=
  orderedCutRank (graph M x y) (alpha M x) (beta M x y)
    {w | w ∈ D.first.support} {w | w ∈ D.second.support} (D.orderedCuts hM hy)

/-- The first marked band arc is the original first path. -/
theorem rank_first_iff (v : Vertex M x) : D.rank hM hy v = 1 ↔ v ∈ D.first.support :=
  orderedCutRank_eq_one_iff (D.orderedCuts hM hy) v

/-- The second marked band arc is the original second path. -/
theorem rank_second_iff (v : Vertex M x) : D.rank hM hy v = 3 ↔ v ∈ D.second.support :=
  orderedCutRank_eq_three_iff (D.orderedCuts hM hy) v

/-- Every actual reference connection restricts to the canonical induced
band between the two given slit crosscuts. -/
theorem reference_connection_restricts (C : Configuration (graph M x y))
    (hC : C ∈ connectionEvent M x y) :
    embeddedConfigurationRestriction (rankedBandGraph (graph M x y) (D.rank hM hy))
      (graph M x y) (rankedBandEmbedding (D.rank hM hy))
      (rankedBandGraph_map_le _ _) C ∈
      arcsConnectionEvent _ (rankedBandFirstArc (D.rank hM hy))
        (rankedBandSecondArc (D.rank hM hy)) :=
  rankedBand_arcs_connection_restricts (graph M x y) (D.rank hM hy)
    (orderedCutRank_edges (D.orderedCuts hM hy)) (alpha M x) (beta M x y)
    (orderedCutRank_left (D.orderedCuts hM hy))
    (orderedCutRank_right (D.orderedCuts hM hy)) C hC

/-- The entire exterior-state partition upper bound follows geometrically;
no assumption is made on the states of any outside bonds. -/
theorem exterior_partition_le (hyM : y < (M:ℤ)) :
    ∀ K : RemovedConfiguration (graph M x y)
      (subgraphRemovedEdges
        ((rankedBandGraph (graph M x y) (D.rank hM hy)).map
          (rankedBandEmbedding (D.rank hM hy))) (graph M x y)),
      (isolatedExtensionPullbackBoundary (rankedBandEmbedding (D.rank hM hy))
        (frozenBoundary (boundary M x y hM hy hyM) K.val)).partition ≤
          (rankedBandBoundary (D.rank hM hy)).partition :=
  rankedBand_exterior_partition_le (graph M x y) (D.rank hM hy)
    (orderedCutRank_edges (D.orderedCuts hM hy)) (alpha M x) (beta M x y)
    (alpha_disjoint_beta M x y hM hy hyM)
    (orderedCutRank_left (D.orderedCuts hM hy))
    (orderedCutRank_right (D.orderedCuts hM hy))

/-- The finite reference estimate on the genuine induced crosscut band.
All reference duality, connection restriction and exterior geometry are proved. -/
theorem wiredArc_lower_bound (q : Set.Ici (1 : ℝ)) (hyM : y < (M:ℤ)) :
    1/(1+(q:ℝ)^2) ≤
      (measure (rankedBandGraph (graph M x y) (D.rank hM hy)) (criticalParameters q)
        (rankedBandBoundary (D.rank hM hy))
        (arcsConnectionEvent _ {v | v.val ∈ D.first.support}
          {v | v.val ∈ D.second.support})).toReal := by
  have h := omega_lower_bound_of_geometry q M x y hM hy hyM
    (rankedBandGraph (graph M x y) (D.rank hM hy)) (rankedBandEmbedding _)
    (rankedBandGraph_map_le _ _) (rankedBandFirstArc _) (rankedBandSecondArc _)
    (rankedBand_arcs_disjoint _) (rankedBandBoundary _) le_rfl
    (D.reference_connection_restricts hM hy) (D.exterior_partition_le hM hy hyM)
  simpa only [rankedBandFirstArc,rankedBandSecondArc,D.rank_first_iff,D.rank_second_iff]
    using h

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
