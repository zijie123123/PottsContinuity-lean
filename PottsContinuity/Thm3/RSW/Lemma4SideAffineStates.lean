module

public import PottsContinuity.Thm3.RSW.Lemma4SideAffineGeometry
public import PottsContinuity.Thm3.RSW.ClosedExtensionEmbedding

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Undoing the rectangle coordinates and including the side retains exactly
its image of the sampled original lattice bonds. -/
theorem lemma4SideInverse_sampledEdges (n : ℕ) (i : Fin 2)
    (A : Configuration (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n))) :
    (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
      ((configurationIso (lemma4SideFullRectangleIso n (lemma4SideSign i)
        (lemma4SideSign_eq_one_or_neg_one i))).symm A)).map
      (frozenEdgeEmbedding (box (56*n))) =
    (A.map (frozenEdgeEmbedding (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n)))).map
      (lemma4SideInversePrimalEmbedding n i).mapEdgeSet := by
  classical
  let e := (configurationIsoEdgeEquiv (lemma4SideFullRectangleIso n (lemma4SideSign i)
    (lemma4SideSign_eq_one_or_neg_one i))).symm.toEmbedding
  let f : (lemma4SideFullGraph n (lemma4SideSign i)).edgeSet ↪
      (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)).edgeSet :=
    embeddedEdgeEmbedding _ _ (inducedVertexEmbedding (lemma4SideVertices n (lemma4SideSign i)))
      (inducedVertexEmbedding_map_le (lemma4SideVertices n (lemma4SideSign i)))
  let g := frozenEdgeEmbedding (box (56*n))
  let k := frozenEdgeEmbedding (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n))
  let j := (lemma4SideInversePrimalEmbedding n i).mapEdgeSet
  have hf : (e.trans f).trans g = k.trans j := by
    apply Function.Embedding.ext
    intro d
    apply Subtype.ext
    change Sym2.map Subtype.val (Sym2.map Subtype.val
      (Sym2.map (lemma4SideRectangleVertexEquiv n (lemma4SideSign i)
        (lemma4SideSign_eq_one_or_neg_one i)).symm d.val)) =
      Sym2.map (lemma4SideInversePrimal n i) (Sym2.map Subtype.val d.val)
    simp only [Sym2.map_map]
    rfl
  have hleft :
      (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
        ((configurationIso (lemma4SideFullRectangleIso n (lemma4SideSign i)
          (lemma4SideSign_eq_one_or_neg_one i))).symm A)).map g =
      ((A.map e).map f).map g := by
    exact congrArg (fun S => S.map g)
      (embeddedConfigurationEmbedding_eq_map _ _ _ _
        ((configurationIso (lemma4SideFullRectangleIso n (lemma4SideSign i)
          (lemma4SideSign_eq_one_or_neg_one i))).symm A))
  have hmaps := (congrArg (fun S => S.map g) (Finset.map_map e f A)).trans
    (Finset.map_map (e.trans f) g A)
  exact hleft.trans (hmaps.trans ((congrArg (fun t => A.map t) hf).trans
    (Finset.map_map k j A).symm))

/-- Every transformed bond has the same state in the included original side
as its normalized bond in the normalized rectangle. -/
theorem lemma4SideInverse_bondState (n : ℕ) (i : Fin 2)
    (A : Configuration (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n)))
    (b : LatticeBond) :
    latticeConfigurationBondState (finiteSubgraphConfiguration (box (56*n)) 0
      (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
        ((configurationIso (lemma4SideFullRectangleIso n (lemma4SideSign i)
          (lemma4SideSign_eq_one_or_neg_one i))).symm A)))
      (lemma4SideInverseBond n i b) =
    latticeConfigurationBondState (finiteSubgraphConfiguration
      (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n)) 0 A) b := by
  classical
  have he : latticeBondEdge (lemma4SideInverseBond n i b) =
      (lemma4SideInversePrimalEmbedding n i).mapEdgeSet (latticeBondEdge b) := by
    apply Subtype.ext
    exact lemma4SideInverseBond_edge n i b
  change decide (_ ∈ _) = decide (_ ∈ _)
  have hm := lemma4SideInverse_sampledEdges n i A
  have hm' := congrArg (fun S => latticeBondEdge (lemma4SideInverseBond n i b) ∈ S) hm
  have hmem := (Iff.of_eq hm').trans (he ▸ Finset.mem_map'
    (lemma4SideInversePrimalEmbedding n i).mapEdgeSet)
  exact Bool.decide_congr hmem


end
end PottsContinuity.RSW
