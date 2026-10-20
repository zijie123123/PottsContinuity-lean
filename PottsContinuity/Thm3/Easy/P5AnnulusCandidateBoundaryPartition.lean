module

public import PottsContinuity.Thm3.Easy.P5AnnulusDoubleDualActiveGeometry
public import PottsContinuity.DualityExt.PositiveP5aAnnulusDualMapBridge
public import PottsContinuity.DualityExt.PositiveAnnulusPrimalPartition
public import PottsContinuity.DualityExt.AnnulusOuterHostOuterConnectivity
public import PottsContinuity.DualityExt.AnnulusOuterHostGeometry
public import PottsContinuity.DualityExt.AnnulusCandidateBoundaryPartition
public import PottsContinuity.DualityExt.AnnulusWiredBoxDMP
public import PottsContinuity.DualityExt.AnnulusRemovedDualEdgeClassification

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.DualityExt

noncomputable section

noncomputable def annulusCandidateDoubleDualActiveHostEmbedding
    (N : ℕ) (_hN : 2 ≤ N) :
    positiveActiveVertexSet (rectangleSubgraphDualGraph
      (annulusExpandedHostDualCandidateGraph_le_rectangle N)) ↪
      RectangleVertex (annulusDualExpandedHostAnchor N) (4 * N + 2) (4 * N + 2) := {
  toFun := fun z => annulusCandidateDualOuterHostVertexEquiv N
    (positiveActiveInclusion (rectangleSubgraphDualGraph
      (annulusExpandedHostDualCandidateGraph_le_rectangle N)) z)
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact (annulusCandidateDualOuterHostVertexEquiv N).injective hxy }

theorem annulusCandidateDoubleDualActiveHostGraph_map_eq
    (N : ℕ) (hN : 2 ≤ N) :
    (positiveActiveGraph (rectangleSubgraphDualGraph
      (annulusExpandedHostDualCandidateGraph_le_rectangle N))).map
        (annulusCandidateDoubleDualActiveHostEmbedding N hN) =
      (annulusSourceGraph N).map (annulusExpandedHostEmbedding N) := by
  classical
  let G := rectangleSubgraphDualGraph
    (annulusExpandedHostDualCandidateGraph_le_rectangle N)
  let A := positiveActiveGraph G
  let e := annulusCandidateDoubleDualActiveVertexEquiv N hN
  let φ := annulusCandidateDualOuterHostVertexEquiv N
  let f := annulusExpandedHostEmbedding N
  let γ := annulusCandidateDoubleDualActiveHostEmbedding N hN
  have hactive := annulusCandidateDoubleDualActiveGraph_map_eq N hN
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [SimpleGraph.map_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, hφa, hφb⟩
    have hmap : (A.map e.toEmbedding).Adj (e a) (e b) := by
      rw [SimpleGraph.map_adj]
      exact ⟨a, b, hab, rfl, rfl⟩
    have hsrc : (annulusSourceGraph N).Adj (e a) (e b) :=
      hactive ▸ hmap
    have hφa' : γ a = f (e a) := by
      apply Subtype.ext
      change (φ (positiveActiveInclusion G a)).1 = (f (e a)).1
      have hcoord := annulusCandidateActive_toExpandedHostEmbedding_eq N hN (e a)
      rw [Equiv.symm_apply_apply] at hcoord
      exact hcoord
    have hφb' : γ b = f (e b) := by
      apply Subtype.ext
      change (φ (positiveActiveInclusion G b)).1 = (f (e b)).1
      have hcoord := annulusCandidateActive_toExpandedHostEmbedding_eq N hN (e b)
      rw [Equiv.symm_apply_apply] at hcoord
      exact hcoord
    exact ⟨e a, e b, hsrc, hφa'.symm.trans hφa, hφb'.symm.trans hφb⟩
  · rintro ⟨x, y, hxy, hfx, hfy⟩
    have hactiveMap : (A.map e.toEmbedding).Adj x y := hactive.symm ▸ hxy
    rw [SimpleGraph.map_adj] at hactiveMap
    rcases hactiveMap with ⟨xA, yA, hA, hxA, hyA⟩
    have hxA' : xA = e.symm x := by
      apply e.injective
      simpa using hxA
    have hyA' : yA = e.symm y := by
      apply e.injective
      simpa using hyA
    subst xA
    subst yA
    have hD : A.Adj (e.symm x) (e.symm y) := hA
    have hφx : γ (e.symm x) = f x := by
      apply Subtype.ext
      change (φ (positiveActiveInclusion G (e.symm x))).1 = (f x).1
      exact annulusCandidateActive_toExpandedHostEmbedding_eq N hN x
    have hφy : γ (e.symm y) = f y := by
      apply Subtype.ext
      change (φ (positiveActiveInclusion G (e.symm y))).1 = (f y).1
      exact annulusCandidateActive_toExpandedHostEmbedding_eq N hN y
    exact ⟨e.symm x, e.symm y, hD,
      hφx.trans hfx, hφy.trans hfy⟩

private theorem annulusCandidate_eqvGen_of_hostOpenAdj
    (N : ℕ) (hN : 2 ≤ N)
    (x y : RectangleVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hxy : (openGraph
      (rectangleGraph (annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2)))).Adj x y) :
    Relation.EqvGen
      (fun u v : RectangleDualVertex (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1) =>
        ActualConnected
            (rectangleDualGraph (annulusDualExpandedHostAnchor N)
              (4 * N + 1) (4 * N + 1))
            (rectangleSubgraphRemovedDualEdges
              (annulusExpandedHostDualCandidateGraph_le_rectangle N)) u v ∨
          (rectangleDualBoundaryCondition (annulusDualExpandedHostAnchor N)
            (4 * N + 1) (4 * N + 1)).partition.r u v)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm x)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm y) := by
  let H := rectangleGraph (annulusDualExpandedHostAnchor N)
    (4 * N + 2) (4 * N + 2)
  let D := rectangleDualGraph (annulusDualExpandedHostAnchor N)
    (4 * N + 1) (4 * N + 1)
  let K := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let G := rectangleSubgraphDualGraph K
  let A := positiveActiveGraph G
  let Rh := subgraphRemovedEdges
    ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N)) H
  let Rd := rectangleSubgraphRemovedDualEdges K
  let f := annulusCandidateDualOuterHostVertexEquiv N
  have hhost : H.Adj x y := (openGraph_le H Rh) hxy
  have hmap : (rectangleDualAmbientGraph
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)).map
        f.toEmbedding |>.Adj x y := by
    rw [annulusCandidateDualAmbientGraph_map_toOuterRectangle_eq N]
    exact hhost
  rw [SimpleGraph.map_adj] at hmap
  rcases hmap with ⟨u, v, huv, hux, hvy⟩
  have hu : u = f.symm x := by
    calc
      u = f.symm (f u) := (f.left_inv u).symm
      _ = f.symm x := by change f u = x at hux; rw [hux]
  have hv : v = f.symm y := by
    calc
      v = f.symm (f v) := (f.left_inv v).symm
      _ = f.symm y := by change f v = y at hvy; rw [hvy]
  subst u
  subst v
  by_cases hD : D.Adj (f.symm x) (f.symm y)
  · let d : D.edgeSet := ⟨s(f.symm x, f.symm y), D.mem_edgeSet.mpr hD⟩
    have hnotSource : (s(x, y) : Sym2 _)
        ∉ ((annulusSourceGraph N).map
          (annulusExpandedHostEmbedding N)).edgeSet := by
      rw [openGraph_adj, openEdges] at hxy
      rcases hxy with ⟨b, hb, hbxy⟩
      have hbmiss := (mem_subgraphRemovedEdges
        (G := (annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (H := H) b).mp hb
      intro hsource
      apply hbmiss
      rw [hbxy]
      exact hsource
    have hnotG : d.1 ∉ G.edgeSet := by
      intro hdG
      have hGadj : G.Adj (f.symm x) (f.symm y) := G.mem_edgeSet.mp hdG
      have huA : f.symm x ∈ positiveActiveVertexSet G := by
        refine ⟨⟨d.1, hdG⟩, ?_⟩
        simp [d]
      have hvA : f.symm y ∈ positiveActiveVertexSet G := by
        refine ⟨⟨d.1, hdG⟩, ?_⟩
        simp [d]
      have hAadj : A.Adj ⟨f.symm x, huA⟩ ⟨f.symm y, hvA⟩ := by
        change G.Adj (f.symm x) (f.symm y)
        exact hGadj
      have hsource : ((annulusSourceGraph N).map
          (annulusExpandedHostEmbedding N)).Adj x y := by
        rw [← annulusCandidateDoubleDualActiveHostGraph_map_eq N hN]
        rw [SimpleGraph.map_adj]
        refine ⟨⟨f.symm x, huA⟩, ⟨f.symm y, hvA⟩, hAadj, ?_, ?_⟩
        · change f (f.symm x) = x
          exact f.apply_symm_apply x
        · change f (f.symm y) = y
          exact f.apply_symm_apply y
      have hsourceEdge : s(x, y) ∈ ((annulusSourceGraph N).map
          (annulusExpandedHostEmbedding N)).edgeSet := by
        rw [((annulusSourceGraph N).map
          (annulusExpandedHostEmbedding N)).mem_edgeSet]
        exact hsource
      exact hnotSource hsourceEdge
    have hdOpen : d.1 ∈ openEdges D Rd := by
      by_contra h
      have hDsub : d.1 ∈ G.edgeSet := by
        change d.1 ∈ (edgeRestriction D Rd).edgeSet
        rw [edgeRestriction_edgeSet, Set.mem_sdiff]
        exact ⟨d.property, h⟩
      exact hnotG hDsub
    have hd : d ∈ Rd := by
      rw [openEdges] at hdOpen
      rcases hdOpen with ⟨e, he, heq⟩
      have he' : e = d := by
        apply Subtype.ext
        exact heq
      simpa [he'] using he
    have hopen : (openGraph D Rd).Adj (f.symm x) (f.symm y) := by
      apply (openGraph_adj D Rd _ _).2
      rw [openEdges]
      exact ⟨d, hd, rfl⟩
    apply Relation.EqvGen.rel
    exact Or.inl (actualConnected_of_adj D Rd hopen)
  · have hbd := annulusCandidateDualAmbient_extraEdge_endpoints_outerBoundary
      N (f.symm x) (f.symm y) huv hD
    apply Relation.EqvGen.rel
    right
    rw [rectangleDualBoundaryCondition_rel]
    right
    exact ⟨(annulusCandidateDualOuterHostBoundary_iff N (f.symm x)).mpr hbd.1,
      (annulusCandidateDualOuterHostBoundary_iff N (f.symm y)).mpr hbd.2⟩

private theorem annulusCandidate_eqvGen_of_hostWalk
    (N : ℕ) (hN : 2 ≤ N)
    {x y : RectangleVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)}
    (w : (openGraph
      (rectangleGraph (annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2)))).Walk x y) :
    Relation.EqvGen
      (fun u v : RectangleDualVertex (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1) =>
        ActualConnected
            (rectangleDualGraph (annulusDualExpandedHostAnchor N)
              (4 * N + 1) (4 * N + 1))
            (rectangleSubgraphRemovedDualEdges
              (annulusExpandedHostDualCandidateGraph_le_rectangle N)) u v ∨
          (rectangleDualBoundaryCondition (annulusDualExpandedHostAnchor N)
            (4 * N + 1) (4 * N + 1)).partition.r u v)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm x)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm y) := by
  induction w with
  | nil => exact Relation.EqvGen.refl _
  | @cons u v z huv tail ih =>
      exact Relation.EqvGen.trans _ _ _
        (annulusCandidate_eqvGen_of_hostOpenAdj N hN u v huv) ih

private theorem annulusCandidate_eqvGen_of_hostActualConnected
    (N : ℕ) (hN : 2 ≤ N)
    (x y : RectangleVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hxy : ActualConnected
      (rectangleGraph (annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2))) x y) :
    Relation.EqvGen
      (fun u v : RectangleDualVertex (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1) =>
        ActualConnected
            (rectangleDualGraph (annulusDualExpandedHostAnchor N)
              (4 * N + 1) (4 * N + 1))
            (rectangleSubgraphRemovedDualEdges
              (annulusExpandedHostDualCandidateGraph_le_rectangle N)) u v ∨
          (rectangleDualBoundaryCondition (annulusDualExpandedHostAnchor N)
            (4 * N + 1) (4 * N + 1)).partition.r u v)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm x)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm y) := by
  exact annulusCandidate_eqvGen_of_hostWalk N hN
    (Classical.choice ((actualConnected_iff_walk _ _ x y).1 hxy))

private theorem annulusCandidate_component_of_hostComponent
    (N : ℕ) (hN : 2 ≤ N)
    (x y : RectangleVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2))
    (hxy : (componentSetoid
      (rectangleGraph (annulusDualExpandedHostAnchor N)
        (4 * N + 2) (4 * N + 2))
      (BoundaryCondition.wired (expandedHostOuterBoundary N))
      (subgraphRemovedEdges
        ((annulusSourceGraph N).map (annulusExpandedHostEmbedding N))
        (rectangleGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 2) (4 * N + 2)))).r x y) :
    (componentSetoid
      (rectangleDualGraph (annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1))
      (rectangleDualBoundaryCondition (annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1))
      (rectangleSubgraphRemovedDualEdges
        (annulusExpandedHostDualCandidateGraph_le_rectangle N))).r
      ((annulusCandidateDualOuterHostVertexEquiv N).symm x)
      ((annulusCandidateDualOuterHostVertexEquiv N).symm y) := by
  let R := fun u v : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) =>
    ActualConnected
        (rectangleDualGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1))
        (rectangleSubgraphRemovedDualEdges
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)) u v ∨
    (rectangleDualBoundaryCondition (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)).partition.r u v
  rw [componentSetoid_rel_iff] at hxy ⊢
  induction hxy with
  | rel a b hab =>
      rcases hab with hconn | hboundary
      · exact annulusCandidate_eqvGen_of_hostActualConnected N hN a b hconn
      · rcases (BoundaryCondition.wired_rel
          (expandedHostOuterBoundary N) a b).1 hboundary with heq | ⟨ha, hb⟩
        · subst b
          exact Relation.EqvGen.refl _
        · apply Relation.EqvGen.rel
          right
          rw [rectangleDualBoundaryCondition_rel]
          right
          exact ⟨(annulusCandidateDualOuterHostBoundary_iff N
              ((annulusCandidateDualOuterHostVertexEquiv N).symm a)).mpr
                (by simpa [expandedHostOuterBoundary,
                  expandedHostOuterBoundaryCoord] using ha),
            (annulusCandidateDualOuterHostBoundary_iff N
              ((annulusCandidateDualOuterHostVertexEquiv N).symm b)).mpr
                (by simpa [expandedHostOuterBoundary,
                  expandedHostOuterBoundaryCoord] using hb)⟩
  | refl z => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The candidate boundary identity follows once the two wired classes on the
full double-dual carrier have the stated edge containment and connectivity
properties, and their restriction to active vertices is the source annulus
partition. -/
theorem p5aAnnulusCandidate_wiredBoundary_partition_of_classConnected
    (N : ℕ) (hN : 2 ≤ N)
    (I O : Set (RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)))
    (hIO : Disjoint I O)
    (hR : ∀ ⦃d : (rectangleDualGraph
        (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)).edgeSet⦄,
      d ∈ rectangleSubgraphRemovedDualEdges
        (annulusExpandedHostDualCandidateGraph_le_rectangle N) →
      (∀ ⦃u⦄, u ∈ d.1 → u ∈ I) ∨ (∀ ⦃u⦄, u ∈ d.1 → u ∈ O))
    (hξ : (rectangleDualBoundaryCondition
        (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)).partition ≤
      (positiveTwoBlockBoundary I O hIO).partition)
    (hI : ∀ ⦃u v : RectangleDualVertex
        (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)⦄,
      u ∈ I → v ∈ I →
      (componentSetoid
        (rectangleDualGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1))
        (rectangleDualBoundaryCondition
          (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1))
        (rectangleSubgraphRemovedDualEdges
          (annulusExpandedHostDualCandidateGraph_le_rectangle N))).r u v)
    (hO : ∀ ⦃u v : RectangleDualVertex
        (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)⦄,
      u ∈ O → v ∈ O →
      (componentSetoid
        (rectangleDualGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1))
        (rectangleDualBoundaryCondition
          (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1))
        (rectangleSubgraphRemovedDualEdges
          (annulusExpandedHostDualCandidateGraph_le_rectangle N))).r u v)
    (hactive : ∀ u v : {x : LatticeVertex // x ∈ annulusVertexSet N},
      ((positiveTwoBlockBoundary I O hIO).partition.r
        ((positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))
        ((positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm v))) ↔
      (annulusPrimalSeparatedBoundary N (by omega)).partition.r u v) :
    (positiveWiredSubgraphDualBoundary
      (annulusExpandedHostDualCandidateGraph_le_rectangle N)
      (annulusCandidateDoubleDualActiveVertexEquiv N hN)).partition =
    (annulusPrimalSeparatedBoundary N (by omega)).partition := by
  let hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let e := annulusCandidateDoubleDualActiveVertexEquiv N hN
  let G := rectangleDualGraph (annulusDualExpandedHostAnchor N)
    (4 * N + 1) (4 * N + 1)
  let ξ := rectangleDualBoundaryCondition
    (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)
  let R := rectangleSubgraphRemovedDualEdges hK
  have hfull : (frozenBoundary ξ R).partition =
      (positiveTwoBlockBoundary I O hIO).partition :=
    frozenBoundary_partition_eq_twoBlock_of_class_connected ξ R I O
      hIO hR hξ hI hO
  apply Setoid.ext
  intro u v
  change ((positiveBoundaryTransport e
      (isolatedExtensionPullbackBoundary
        (positiveActiveInclusion (rectangleSubgraphDualGraph hK))
        (frozenBoundary ξ R))).partition).r u v ↔
    (annulusPrimalSeparatedBoundary N (by omega)).partition.r u v
  change (frozenBoundary ξ R).partition.r
      ((positiveActiveInclusion (rectangleSubgraphDualGraph hK)) (e.symm u))
      ((positiveActiveInclusion (rectangleSubgraphDualGraph hK)) (e.symm v)) ↔ _
  rw [hfull]
  exact hactive u v

theorem p5aAnnulusCandidate_wiredBoundary_partition
    (N : ℕ) (hN : 2 ≤ N) :
    (positiveWiredSubgraphDualBoundary
      (annulusExpandedHostDualCandidateGraph_le_rectangle N)
      (annulusCandidateDoubleDualActiveVertexEquiv N hN)).partition =
    (annulusPrimalSeparatedBoundary N (by omega)).partition := by
  let I := annulusCandidateInnerBoundaryClass N
  let O := annulusCandidateOuterBoundaryClass N
  let hIO := annulusCandidateBoundaryClasses_disjoint N (by omega)
  have hR : ∀ ⦃d : (rectangleDualGraph
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)).edgeSet⦄,
      d ∈ rectangleSubgraphRemovedDualEdges
        (annulusExpandedHostDualCandidateGraph_le_rectangle N) →
      (∀ ⦃u⦄, u ∈ d.1 → u ∈ I) ∨ (∀ ⦃u⦄, u ∈ d.1 → u ∈ O) := by
    intro d hd
    rcases annulusCandidateRemovedDualEdge_missingAndTwoBlock N hN d hd with
      ⟨_, hI⟩ | ⟨_, hO⟩
    · left
      intro u hu
      have huPair : u ∈ s(d.1.out.1, d.1.out.2) := by
        have hpair : s(d.1.out.1, d.1.out.2) = d.1 := Quot.out_eq _
        rw [hpair]
        exact hu
      rcases Sym2.mem_iff.mp huPair with hu | hu
      · subst u
        change annulusCandidateDualOuterHostVertexEquiv N d.1.out.1 ∈
          annulusExpandedHostPrimalInnerClass N
        exact hI (Sym2.mem_mk_left _ _)
      · subst u
        change annulusCandidateDualOuterHostVertexEquiv N d.1.out.2 ∈
          annulusExpandedHostPrimalInnerClass N
        exact hI (Sym2.mem_mk_right _ _)
    · right
      intro u hu
      have huPair : u ∈ s(d.1.out.1, d.1.out.2) := by
        have hpair : s(d.1.out.1, d.1.out.2) = d.1 := Quot.out_eq _
        rw [hpair]
        exact hu
      rcases Sym2.mem_iff.mp huPair with hu | hu
      · subst u
        change annulusCandidateDualOuterHostVertexEquiv N d.1.out.1 ∈
          annulusExpandedHostPrimalOuterClass N
        exact hO (Sym2.mem_mk_left _ _)
      · subst u
        change annulusCandidateDualOuterHostVertexEquiv N d.1.out.2 ∈
          annulusExpandedHostPrimalOuterClass N
        exact hO (Sym2.mem_mk_right _ _)
  have hξ : (rectangleDualBoundaryCondition
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)).partition ≤
      (positiveTwoBlockBoundary I O hIO).partition := by
    exact annulusCandidateDualBoundary_le_twoBlock N (by omega)
  have hI : ∀ ⦃u v : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)⦄,
      u ∈ I → v ∈ I →
      (componentSetoid
        (rectangleDualGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1))
        (rectangleDualBoundaryCondition
          (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1))
        (rectangleSubgraphRemovedDualEdges
          (annulusExpandedHostDualCandidateGraph_le_rectangle N))).r u v := by
    intro u v hu hv
    change annulusCandidateDualOuterHostVertexEquiv N u ∈
        annulusExpandedHostPrimalInnerClass N at hu
    change annulusCandidateDualOuterHostVertexEquiv N v ∈
        annulusExpandedHostPrimalInnerClass N at hv
    have huC := annulusExpandedHost_innerClass_connected_to_center N (by omega)
      (annulusCandidateDualOuterHostVertexEquiv N u) hu
    have hvC := annulusExpandedHost_innerClass_connected_to_center N (by omega)
      (annulusCandidateDualOuterHostVertexEquiv N v) hv
    let H := rectangleGraph (annulusDualExpandedHostAnchor N)
      (4 * N + 2) (4 * N + 2)
    let R := subgraphRemovedEdges ((annulusSourceGraph N).map
      (annulusExpandedHostEmbedding N)) H
    let ξ := BoundaryCondition.wired (expandedHostOuterBoundary N)
    have hfreeze : annulusExpandedHostPrimalFrozenPartition N ≤
        componentSetoid H ξ R := by
      change componentSetoid H (BoundaryCondition.wired (∅ : Set _)) R ≤
        componentSetoid H ξ R
      apply componentSetoid_le H (BoundaryCondition.wired (∅ : Set _)) R
        (componentSetoid H ξ R)
      · intro a b hab
        exact actualConnected_component H ξ R hab
      · intro a b hab
        rcases (BoundaryCondition.wired_rel (∅ : Set _) a b).mp hab with heq | h
        · subst b
          exact (componentSetoid H ξ R).refl a
        · simp at h
    have huvF : (annulusExpandedHostPrimalFrozenPartition N).r
        (annulusCandidateDualOuterHostVertexEquiv N u)
        (annulusCandidateDualOuterHostVertexEquiv N v) := by
      exact (annulusExpandedHostPrimalFrozenPartition N).iseqv.trans
        ((annulusExpandedHostPrimalFrozenPartition N).iseqv.symm huC) hvC
    have huvHost := hfreeze huvF
    simpa only [Equiv.symm_apply_apply] using
      annulusCandidate_component_of_hostComponent N hN
        (annulusCandidateDualOuterHostVertexEquiv N u)
        (annulusCandidateDualOuterHostVertexEquiv N v) huvHost
  have hO : ∀ ⦃u v : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1)⦄,
      u ∈ O → v ∈ O →
      (componentSetoid
        (rectangleDualGraph (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1))
        (rectangleDualBoundaryCondition
          (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1))
        (rectangleSubgraphRemovedDualEdges
          (annulusExpandedHostDualCandidateGraph_le_rectangle N))).r u v := by
    intro u v hu hv
    change annulusCandidateDualOuterHostVertexEquiv N u ∈
        annulusExpandedHostPrimalOuterClass N at hu
    change annulusCandidateDualOuterHostVertexEquiv N v ∈
        annulusExpandedHostPrimalOuterClass N at hv
    simpa only [Equiv.symm_apply_apply] using
      annulusCandidate_component_of_hostComponent N hN
        (annulusCandidateDualOuterHostVertexEquiv N u)
        (annulusCandidateDualOuterHostVertexEquiv N v)
        (annulusExpandedHost_outerClass_component_connected N hu hv)
  have hactive : ∀ u v : {x : LatticeVertex // x ∈ annulusVertexSet N},
      (positiveTwoBlockBoundary I O hIO).partition.r
        ((positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))
        ((positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm v)) ↔
      (annulusPrimalSeparatedBoundary N (by omega)).partition.r u v := by
    intro u v
    exact annulusCandidateActive_twoBlock_partition_iff N hN u v
  exact p5aAnnulusCandidate_wiredBoundary_partition_of_classConnected
    N hN I O hIO hR hξ hI hO hactive

end

end PottsContinuity.Thm3.Easy
