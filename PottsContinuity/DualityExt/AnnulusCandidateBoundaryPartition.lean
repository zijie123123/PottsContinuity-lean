module

public import PottsContinuity.DualityExt.PositiveAnnulusPrimalPartition
public import PottsContinuity.Thm3.Easy.P5AnnulusDoubleDualActiveGeometry
public import PottsContinuity.DualityExt.AnnulusOuterHostOuterConnectivity

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.Thm3.Easy

noncomputable section

def annulusCandidateInnerBoundaryClass (N : ℕ) :
    Set (RectangleDualVertex (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) :=
  (annulusCandidateDualOuterHostVertexEquiv N).toEmbedding ⁻¹'
    annulusExpandedHostPrimalInnerClass N

def annulusCandidateOuterBoundaryClass (N : ℕ) :
    Set (RectangleDualVertex (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) :=
  (annulusCandidateDualOuterHostVertexEquiv N).toEmbedding ⁻¹'
    annulusExpandedHostPrimalOuterClass N

theorem annulusCandidateBoundaryClasses_disjoint (N : ℕ) (hN : 1 ≤ N) :
    Disjoint (annulusCandidateInnerBoundaryClass N)
      (annulusCandidateOuterBoundaryClass N) := by
  apply Set.disjoint_left.mpr
  intro z hzI hzO
  exact (Set.disjoint_left.mp (annulusExpandedHost_outerClass_disjoint N hN))
    hzI hzO

theorem annulusCandidateActive_twoBlock_partition_iff
    (N : ℕ) (hN : 2 ≤ N)
    (u v : {x : LatticeVertex // x ∈ annulusVertexSet N}) :
    (positiveTwoBlockBoundary (annulusCandidateInnerBoundaryClass N)
      (annulusCandidateOuterBoundaryClass N)
      (annulusCandidateBoundaryClasses_disjoint N (by omega))).partition.r
        ((positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm u))
        ((positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N)))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm v)) ↔
      (annulusPrimalSeparatedBoundary N (by omega)).partition.r u v := by
  let j := fun x : {z : LatticeVertex // z ∈ annulusVertexSet N} =>
    positiveActiveInclusion (rectangleSubgraphDualGraph
      (annulusExpandedHostDualCandidateGraph_le_rectangle N))
      ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm x)
  have hj : Function.Injective j := by
    intro x y hxy
    have hactive := (positiveActiveInclusion
      (rectangleSubgraphDualGraph
        (annulusExpandedHostDualCandidateGraph_le_rectangle N))).injective hxy
    exact (annulusCandidateDoubleDualActiveVertexEquiv N hN).symm.injective
      (by simpa [j] using hactive)
  have hinner (x : {z : LatticeVertex // z ∈ annulusVertexSet N}) :
      j x ∈ annulusCandidateInnerBoundaryClass N ↔
        x ∈ annulusPrimalInnerBoundaryClass N (by omega) := by
    change annulusCandidateDualOuterHostVertexEquiv N
        (positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm x)) ∈
          annulusExpandedHostPrimalInnerClass N ↔ _
    exact annulusCandidateActive_innerClass_iff N hN x
  have houter (x : {z : LatticeVertex // z ∈ annulusVertexSet N}) :
      j x ∈ annulusCandidateOuterBoundaryClass N ↔
        x ∈ annulusPrimalOuterBoundaryClass N (by omega) := by
    change annulusCandidateDualOuterHostVertexEquiv N
        (positiveActiveInclusion (rectangleSubgraphDualGraph
          (annulusExpandedHostDualCandidateGraph_le_rectangle N))
          ((annulusCandidateDoubleDualActiveVertexEquiv N hN).symm x)) ∈
          annulusExpandedHostPrimalOuterClass N ↔ _
    exact annulusCandidateActive_outerClass_iff N hN x
  rw [annulusPrimalSeparatedBoundary_partition_eq_twoBlock]
  rw [positiveTwoBlockBoundary_rel_iff,
    positiveTwoBlockBoundary_rel_iff]
  constructor
  · rintro (heq | hI | hO)
    · exact Or.inl (hj heq)
    · exact Or.inr (Or.inl ⟨(hinner u).mp hI.1, (hinner v).mp hI.2⟩)
    · exact Or.inr (Or.inr ⟨(houter u).mp hO.1, (houter v).mp hO.2⟩)
  · rintro (heq | hI | hO)
    · exact Or.inl (congrArg j heq)
    · exact Or.inr (Or.inl ⟨(hinner u).mpr hI.1, (hinner v).mpr hI.2⟩)
    · exact Or.inr (Or.inr ⟨(houter u).mpr hO.1, (houter v).mpr hO.2⟩)

theorem annulusCandidateDualBoundary_le_twoBlock
    (N : ℕ) (hN : 1 ≤ N) :
    (rectangleDualBoundaryCondition
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)).partition ≤
    (positiveTwoBlockBoundary (annulusCandidateInnerBoundaryClass N)
      (annulusCandidateOuterBoundaryClass N)
      (annulusCandidateBoundaryClasses_disjoint N hN)).partition := by
  intro u v huv
  rw [rectangleDualBoundaryCondition_rel] at huv
  change ((BoundaryCondition.wired (annulusCandidateInnerBoundaryClass N)).partition ⊔
    (BoundaryCondition.wired (annulusCandidateOuterBoundaryClass N)).partition).r u v
  rcases huv with rfl | ⟨hu, hv⟩
  · exact Setoid.refl' _ _
  · have huO : u ∈ annulusCandidateOuterBoundaryClass N := by
      have hu' := (annulusCandidateDualOuterHostBoundary_iff N u).mp hu
      change (annulusCandidateDualOuterHostVertexEquiv N u) ∈
        annulusExpandedHostPrimalOuterClass N
      change (annulusCandidateDualOuterHostVertexEquiv N u).1 ∈
          expandedHostOuterBoundaryCoord N ∨ _
      exact Or.inl (by simpa [expandedHostOuterBoundaryCoord] using hu')
    have hvO : v ∈ annulusCandidateOuterBoundaryClass N := by
      have hv' := (annulusCandidateDualOuterHostBoundary_iff N v).mp hv
      change (annulusCandidateDualOuterHostVertexEquiv N v) ∈
        annulusExpandedHostPrimalOuterClass N
      change (annulusCandidateDualOuterHostVertexEquiv N v).1 ∈
          expandedHostOuterBoundaryCoord N ∨ _
      exact Or.inl (by simpa [expandedHostOuterBoundaryCoord] using hv')
    exact (le_sup_right : (BoundaryCondition.wired
      (annulusCandidateOuterBoundaryClass N)).partition ≤
      (BoundaryCondition.wired (annulusCandidateInnerBoundaryClass N)).partition ⊔
        (BoundaryCondition.wired (annulusCandidateOuterBoundaryClass N)).partition)
      ((BoundaryCondition.wired_rel
        (annulusCandidateOuterBoundaryClass N) u v).2 (Or.inr ⟨huO, hvO⟩))

end

end PottsContinuity.DualityExt
