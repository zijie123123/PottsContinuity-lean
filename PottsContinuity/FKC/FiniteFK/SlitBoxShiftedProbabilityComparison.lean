-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxShiftedProbabilityComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitShiftedEmbedding
public import PottsContinuity.FKC.FiniteFK.EmbeddedClosedInteriorBoundary
public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryUpper
public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitExteriorPathRestriction
public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitConnectionLaw
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory
noncomputable section

private theorem slitBoxSplitShifted_interior_neighbor_closed
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ))
    {x : SlitBoxSplitCoverVertex n}
    (hx : x ∉ slitBoxSplitCoverBoundary n)
    {z : ParafermionicCoverBoxVertex n}
    (hadj : (parafermionicCoverBoxGraph n).Adj
      (slitBoxSplitShiftedEmbedding n hn k hlo hhi x) z) :
    ∃ y : SlitBoxSplitCoverVertex n,
      slitBoxSplitShiftedEmbedding n hn k hlo hhi y = z ∧
      (slitBoxSplitCoverGraph n).Adj x y := by
  cases x with
  | inl u =>
      exact slitBoxSplitShiftedEmbedding_interior_neighbor_closed
        n hn k hlo hhi u z hadj
  | inr a => exact (hx ⟨a, rfl⟩).elim

/-- Every outer cover-box vertex based on the retained slit arc is outside the
shifted image of the split interior, for every allowed sheet translation. -/
theorem slitBoxSplitShiftedCover_arc_base_not_interior_image
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ))
    (v : ParafermionicCoverBoxVertex n)
    (hv : v.val.1.1 = 0 ∧ 0 ≤ v.val.1.2 ∧ v.val.1.2 ≤ n) :
    v ∉ Set.range (fun u : SlitBoxSplitInterior n =>
      slitBoxSplitShiftedEmbedding n hn k hlo hhi (Sum.inl u)) := by
  rintro ⟨u, heq⟩
  have hproj :
      (slitBoxSplitShiftedEmbedding n hn k hlo hhi (Sum.inl u)).val.1 =
        v.val.1 := congrArg Prod.fst (congrArg Subtype.val heq)
  have hx' := congrArg Prod.fst hproj
  have hx : u.1.val.1 = 0 := by
    simpa [slitBoxSplitShiftedEmbedding_val,
      parafermionicCoverSheetTranslate, slitBoxSplitCoverMap,
      slitBoxInteriorCoverLift] using hx'.trans hv.1
  have hy' := congrArg Prod.snd hproj
  have hy : 0 ≤ u.1.val.2 ∧ u.1.val.2 ≤ n := by
    constructor
    · exact hy'.symm ▸ hv.2.1
    · exact hy'.symm ▸ hv.2.2
  have huArc : u.1 ∈ slitBoxWiredArc n :=
    (mem_slitBoxWiredArc_iff n u.1).2 ⟨hx, hy.1, hy.2⟩
  exact u.2 huArc

theorem slitBoxShiftedCover_connection_probability_le_slit_wired_arc_hit
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight) (k : ℤ)
    (hlo : -((n ^ 5 : ℕ) : ℤ) ≤ k)
    (hhi : k + 1 ≤ ((n ^ 5 : ℕ) : ℤ))
    (u : SlitBoxSplitInterior n) (v : ParafermionicCoverBoxVertex n)
    (hv : v ∉ Set.range (fun w : SlitBoxSplitInterior n =>
      slitBoxSplitShiftedEmbedding n hn k hlo hhi (Sum.inl w))) :
    (measure (parafermionicCoverBoxGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex n)))
      {A : Configuration (parafermionicCoverBoxGraph n) |
        ActualConnected (parafermionicCoverBoxGraph n) A
          (slitBoxSplitShiftedEmbedding n hn k hlo hhi (Sum.inl u)) v}).toReal ≤
      (measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n u.1)).toReal := by
  classical
  let G := slitBoxSplitCoverGraph n
  let H := parafermionicCoverBoxGraph n
  let f := slitBoxSplitShiftedEmbedding n hn k hlo hhi
  let hGH : G.map f ≤ H := slitBoxSplitShiftedGraph_map_le_coverBox n hn k hlo hhi
  let B : Set (SlitBoxSplitCoverVertex n) := slitBoxSplitCoverBoundary n
  let ξ : BoundaryCondition (ParafermionicCoverBoxVertex n) :=
    BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex n))
  let η : BoundaryCondition (SlitBoxSplitCoverVertex n) := BoundaryCondition.wired B
  let S : Set (Configuration G) := {A |
    ∃ y ∈ B, ActualConnected G A (Sum.inl u) y}
  let restr : Configuration H → Configuration G :=
    embeddedConfigurationRestriction G H f hGH
  have hclosed : ∀ ⦃x : SlitBoxSplitCoverVertex n⦄, x ∉ B →
      ∀ ⦃z : ParafermionicCoverBoxVertex n⦄, H.Adj (f x) z →
        ∃ y : SlitBoxSplitCoverVertex n, f y = z ∧ G.Adj x y := by
    intro x hx z hadj
    exact slitBoxSplitShifted_interior_neighbor_closed n hn k hlo hhi hx hadj
  have hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary ξ K.val)).partition ≤ η.partition := by
    intro K
    exact isolatedExtensionPullback_frozenFree_partition_le_wired_of_closedInterior
      f hGH B hclosed K
  have hS : IsUpperSet S := by
    intro A A' hAA' hA
    rcases hA with ⟨y, hy, hconn⟩
    exact ⟨y, hy, actualConnected_mono hAA' hconn⟩
  have hvout : v ∉ f '' Bᶜ := by
    rintro ⟨x, hx, heq⟩
    cases x with
    | inl w => exact hv ⟨w, heq⟩
    | inr a => exact hx ⟨a, rfl⟩
  have hfirst : ∀ A : Configuration H,
      ActualConnected H A (f (Sum.inl u)) v → restr A ∈ S := by
    intro A hpath
    obtain ⟨y, hy, hconn⟩ := embedded_openPath_restrict_hits_boundary_of_exterior
      f hGH B hclosed (Sum.inl u)
      (slitBoxSplitCoverMap_inl_not_boundary n u) v hvout A hpath
    exact ⟨y, hy, hconn⟩
  let T : Set (Configuration H) :=
    {A | ActualConnected H A (f (Sum.inl u)) v}
  have hsubset : T ⊆ {A | restr A ∈ S} := by
    intro A hA
    exact hfirst A hA
  have hmono : (measure H q ξ T).toReal ≤
      (measure H q ξ {A | restr A ∈ S}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  have hupper := embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
    G H f hGH q ξ η S hS hpart
  have htransport := congrArg ENNReal.toReal
    (slitBoxSplitWiredArcConnection_measure_eq n q (Sum.inl u))
  calc
    (measure H q ξ T).toReal ≤ (measure H q ξ {A | restr A ∈ S}).toReal := hmono
    _ ≤ (measure G q η S).toReal := by simpa [G, ξ, η, S] using hupper
    _ = (measure (slitBoxGraph n) q (slitBoxBoundary n)
          (slitBoxWiredArcConnectionEvent n u.1)).toReal := by
            simpa [S, slitBoxSplitBaseVertex, G, η] using htransport

end
end PottsContinuity.FKC.FiniteFK
