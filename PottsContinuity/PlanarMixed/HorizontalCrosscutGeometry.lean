module

public import PottsContinuity.PlanarMixed.SourceCrosscutComparison
public import PottsContinuity.PlanarMixed.BandComparisonGeometry
public import PottsContinuity.PlanarMixed.Square.RectangleCrossingSymmetry

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Translate and rotate the actual reference square to the origin square. -/
def horizontalSquareNormalizationIso (a : LatticeVertex) (N : ℕ) :
    rectangleGraph a N N ≃g rectangleGraph (0,0) N N :=
  (Square.squareTranslationIso a N).symm.trans
    (Square.rectangleGraphCoordinateSwapIso (0,0) N N)

/-- The coordinate formula keeps all original square vertices. -/
theorem horizontalSquareNormalizationIso_val (a : LatticeVertex) (N : ℕ)
    (v : RectangleVertex a N N) :
    (horizontalSquareNormalizationIso a N v).val =
      (v.val.2-a.2, v.val.1-a.1) := by
  change (v.val.2 + (-a).2, v.val.1 + (-a).1) = _
  rfl

/-- Actual open horizontal paths, with the lower left start preceding the
upper one. This is path data, and does not select a path. -/
abbrev HorizontalSquareCrosscutData (a : LatticeVertex) (N : ℕ) :=
  OpenCrosscutPair (rectangleGraph a N N)
    (fun v => (v.val.2-a.2,v.val.1-a.1)) (N : ℤ)

namespace HorizontalSquareCrosscutData
variable {a : LatticeVertex} {N : ℕ} (D : HorizontalSquareCrosscutData a N)

/-- The same given paths in normalized coordinates, with their full supports. -/
def normalized : SquareCrosscutData N where
  state := configurationIso (horizontalSquareNormalizationIso a N) D.state
  firstStart := horizontalSquareNormalizationIso a N D.firstStart
  secondStart := horizontalSquareNormalizationIso a N D.secondStart
  firstEnd := horizontalSquareNormalizationIso a N D.firstEnd
  secondEnd := horizontalSquareNormalizationIso a N D.secondEnd
  first := D.first.map (openGraphIso (horizontalSquareNormalizationIso a N) D.state).toHom
  second := D.second.map (openGraphIso (horizontalSquareNormalizationIso a N) D.state).toHom
  first_bottom := by rw [horizontalSquareNormalizationIso_val]; exact D.first_bottom
  second_bottom := by rw [horizontalSquareNormalizationIso_val]; exact D.second_bottom
  first_top := by rw [horizontalSquareNormalizationIso_val]; exact D.first_top
  second_top := by rw [horizontalSquareNormalizationIso_val]; exact D.second_top
  ordered := by simp only [horizontalSquareNormalizationIso_val]; exact D.ordered
  disjoint := by
    intro z hz hz'
    dsimp only [openGraphIso] at hz hz'
    rw [SimpleGraph.Walk.support_map] at hz hz'
    obtain ⟨u,hu,huz⟩ := List.mem_map.mp hz
    obtain ⟨v,hv,hvz⟩ := List.mem_map.mp hz'
    have huv : u = v := (horizontalSquareNormalizationIso a N).injective (huz.trans hvz.symm)
    exact D.disjoint u hu (huv ▸ hv)

/-- Labels are constructed from the original two horizontal traces. -/
def rank (v : RectangleVertex a N N) : ℤ :=
  D.normalized.rank (horizontalSquareNormalizationIso a N v)

theorem rank_edges : RankedBandEdges (rectangleGraph a N N) D.rank := by
  intro u v huv
  exact orderedCutRank_edges D.normalized.orderedCuts _ _
    ((horizontalSquareNormalizationIso a N).toHom.map_rel huv)

theorem rank_first_iff (v : RectangleVertex a N N) :
    D.rank v = 1 ↔ v ∈ D.first.support := by
  rw [rank,D.normalized.rank_first_iff]
  change horizontalSquareNormalizationIso a N v ∈
    (D.first.map (openGraphIso (horizontalSquareNormalizationIso a N) D.state).toHom).support ↔ _
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hv
    obtain ⟨u,hu,huv⟩ := List.mem_map.mp hv
    exact (horizontalSquareNormalizationIso a N).injective huv ▸ hu
  · intro hv
    exact List.mem_map.mpr ⟨v,hv,rfl⟩

theorem rank_second_iff (v : RectangleVertex a N N) :
    D.rank v = 3 ↔ v ∈ D.second.support := by
  rw [rank,D.normalized.rank_second_iff]
  change horizontalSquareNormalizationIso a N v ∈
    (D.second.map (openGraphIso (horizontalSquareNormalizationIso a N) D.state).toHom).support ↔ _
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hv
    obtain ⟨u,hu,huv⟩ := List.mem_map.mp hv
    exact (horizontalSquareNormalizationIso a N).injective huv ▸ hu
  · intro hv
    exact List.mem_map.mpr ⟨v,hv,rfl⟩

theorem rank_bottom (v : RectangleVertex a N N)
    (hv : v ∈ Square.rectangleDoubleCollarInnerBottom a N N) : D.rank v ≤ 1 := by
  apply orderedCutRank_left D.normalized.orderedCuts
  change (horizontalSquareNormalizationIso a N v).val.1 = 0
  rw [horizontalSquareNormalizationIso_val]
  change v.val.2 = a.2 at hv
  dsimp
  omega

theorem rank_top (v : RectangleVertex a N N)
    (hv : v ∈ Square.rectangleDoubleCollarInnerTop a N N) : 3 ≤ D.rank v := by
  apply orderedCutRank_right D.normalized.orderedCuts
  change (horizontalSquareNormalizationIso a N v).val.1 = 0 + (N : ℤ)
  rw [horizontalSquareNormalizationIso_val]
  change v.val.2 = a.2 + (N : ℤ) at hv
  dsimp
  omega

/-- G2 partition order for every actual exterior configuration of R*. -/
theorem reference_partition_le (hN : 1 ≤ N)
    (K : RemovedConfiguration (rectangleGraph a N N)
      (subgraphRemovedEdges
        ((rankedBandGraph (rectangleGraph a N N) D.rank).map (rankedBandEmbedding D.rank))
        (rectangleGraph a N N))) :
    (isolatedExtensionPullbackBoundary (rankedBandEmbedding D.rank)
      (frozenBoundary (twoBlockBoundary
        (Square.rectangleDoubleCollarInnerBottom a N N)
        (Square.rectangleDoubleCollarInnerTop a N N)
        (Square.rectangleDoubleCollarInnerBottom_disjoint_top a N N hN)) K.val)).partition ≤
      (rankedBandBoundary D.rank).partition :=
  band_reference_partition_le _ D.rank D.rank_edges _ _ _ D.rank_bottom D.rank_top K

/-- Recorded open paths supply the inherited arc wiring in any finite host. -/
theorem frozen_boundary_order
    {U : Type*} [Finite U] (H : SimpleGraph U)
    (i : RectangleVertex a N N ↪ U) (hSquare : (rectangleGraph a N N).map i ≤ H)
    (K : Configuration H)
    (hstate : D.state = embeddedConfigurationRestriction (rectangleGraph a N N) H i hSquare K)
    (ξ : BoundaryCondition U) :
    (rankedBandBoundary D.rank).partition ≤
      (isolatedExtensionPullbackBoundary ((rankedBandEmbedding D.rank).trans i)
        (frozenBoundary ξ K)).partition := by
  apply twoBlockBoundary_le_pullback_frozen_of_arcConnections H _ ξ K
    (rankedBandFirstArc D.rank) (rankedBandSecondArc D.rank) (rankedBand_arcs_disjoint D.rank)
  · intro v hv w hw
    have hc := openWalk_support_actualConnected _ D.state D.first
      ((D.rank_first_iff v.val).mp hv) ((D.rank_first_iff w.val).mp hw)
    rw [hstate] at hc
    obtain ⟨walk⟩ := hc
    exact ⟨walk.map (embeddedOpenRestrictionHom _ H i hSquare K)⟩
  · intro v hv w hw
    have hc := openWalk_support_actualConnected _ D.state D.second
      ((D.rank_second_iff v.val).mp hv) ((D.rank_second_iff w.val).mp hw)
    rw [hstate] at hc
    obtain ⟨walk⟩ := hc
    exact ⟨walk.map (embeddedOpenRestrictionHom _ H i hSquare K)⟩

/-- The full reference-to-record partition inequality, with both halves
proved from the actual crosscuts and the literal frozen sample. -/
theorem reference_partition_le_frozen
    (hN : 1 ≤ N) {U : Type*} [Finite U] (H : SimpleGraph U)
    (i : RectangleVertex a N N ↪ U) (hSquare : (rectangleGraph a N N).map i ≤ H)
    (K : Configuration H)
    (hstate : D.state = embeddedConfigurationRestriction (rectangleGraph a N N) H i hSquare K)
    (ξ : BoundaryCondition U)
    (B : RemovedConfiguration (rectangleGraph a N N)
      (subgraphRemovedEdges
        ((rankedBandGraph (rectangleGraph a N N) D.rank).map (rankedBandEmbedding D.rank))
        (rectangleGraph a N N))) :
    (isolatedExtensionPullbackBoundary (rankedBandEmbedding D.rank)
      (frozenBoundary (twoBlockBoundary
        (Square.rectangleDoubleCollarInnerBottom a N N)
        (Square.rectangleDoubleCollarInnerTop a N N)
        (Square.rectangleDoubleCollarInnerBottom_disjoint_top a N N hN)) B.val)).partition ≤
      (isolatedExtensionPullbackBoundary ((rankedBandEmbedding D.rank).trans i)
        (frozenBoundary ξ K)).partition :=
  (D.reference_partition_le hN B).trans (D.frozen_boundary_order H i hSquare K hstate ξ)

/-- G2 clipping to the literal lower and upper path supports. -/
theorem reference_crossing_restricts (C : Configuration (rectangleGraph a N N))
    (hC : C ∈ arcsConnectionEvent (rectangleGraph a N N)
      (Square.rectangleDoubleCollarInnerBottom a N N) (Square.rectangleDoubleCollarInnerTop a N N)) :
    embeddedConfigurationRestriction (rankedBandGraph (rectangleGraph a N N) D.rank) _
      (rankedBandEmbedding D.rank) (rankedBandGraph_map_le _ D.rank) C ∈
        arcsConnectionEvent _ {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support} := by
  simpa only [rankedBandFirstArc,rankedBandSecondArc,D.rank_first_iff,D.rank_second_iff] using
    band_reference_crossing_restricts _ D.rank D.rank_edges _ _ D.rank_bottom D.rank_top C hC

/-- The clipped sampled connection and the two retained original paths
join their original starting vertices inside the original reference square. -/
theorem original_starts_connected
    (C : Configuration (rectangleGraph a N N)) (hstate : D.state ⊆ C)
    (hconn : embeddedConfigurationRestriction
      (rankedBandGraph (rectangleGraph a N N) D.rank) _
      (rankedBandEmbedding D.rank) (rankedBandGraph_map_le _ D.rank) C ∈
        arcsConnectionEvent _ {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support}) :
    ActualConnected (rectangleGraph a N N) C D.firstStart D.secondStart := by
  obtain ⟨u,hu,v,hv,⟨p⟩⟩ := hconn
  have hfirst := openWalk_support_actualConnected _ D.state D.first
    D.first.start_mem_support hu
  have hsecond := openWalk_support_actualConnected _ D.state D.second
    hv D.second.start_mem_support
  have hmiddle : ActualConnected (rectangleGraph a N N) C u.val v.val :=
    ⟨p.map (embeddedOpenRestrictionHom _ _ (rankedBandEmbedding D.rank)
      (rankedBandGraph_map_le _ D.rank) C)⟩
  exact (actualConnected_mono hstate hfirst).trans
    (hmiddle.trans (actualConnected_mono hstate hsecond))

/-- Any marked sets containing the original starts receive the same sampled
connection; no virtual boundary edge enters the target. -/
theorem original_arcs_connected
    (C : Configuration (rectangleGraph a N N)) (hstate : D.state ⊆ C)
    (I J : Set (RectangleVertex a N N)) (hI : D.firstStart ∈ I) (hJ : D.secondStart ∈ J)
    (hconn : embeddedConfigurationRestriction
      (rankedBandGraph (rectangleGraph a N N) D.rank) _
      (rankedBandEmbedding D.rank) (rankedBandGraph_map_le _ D.rank) C ∈
        arcsConnectionEvent _ {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support}) :
    C ∈ arcsConnectionEvent (rectangleGraph a N N) I J :=
  ⟨D.firstStart,hI,D.secondStart,hJ,D.original_starts_connected C hstate hconn⟩

end HorizontalSquareCrosscutData
end
end PottsContinuity.PlanarMixed
