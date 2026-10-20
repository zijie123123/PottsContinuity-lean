-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceTopTree.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceTopRemoval
public import PottsContinuity.FKC.Medial.ParafermionicCoverFiniteEdgeCount
public import PottsContinuity.FKC.Medial.ParafermionicCoverFiniteFaceCount
public import PottsContinuity.FKC.Medial.ParafermionicCoverEulerCount
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

noncomputable section

noncomputable def parafermionicCoverFaceTopEdgeBox {n : ℕ}
    (f : {f // f ∈ parafermionicCoverFiniteOrdinaryFaces n}) :
    Sym2 (ParafermionicCoverBoxVertex n) :=
  s(⟨parafermionicCoverFaceRightUpLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).1⟩,
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).2⟩)

private theorem parafermionicCoverFaceTopEdgeBox_map {n : ℕ}
    (f : {f // f ∈ parafermionicCoverFiniteOrdinaryFaces n}) :
    Sym2.map Subtype.val (parafermionicCoverFaceTopEdgeBox f) =
      parafermionicCoverFiniteFaceTopEdge f.1 := by
  simp [parafermionicCoverFaceTopEdgeBox, parafermionicCoverFiniteFaceTopEdge,
    Sym2.map_mk]

noncomputable def parafermionicCoverFiniteFaceTopEdges (n : ℕ) :
    Finset (Sym2 (ParafermionicCoverBoxVertex n)) :=
  (parafermionicCoverFiniteOrdinaryFaces n).attach.image parafermionicCoverFaceTopEdgeBox

private theorem parafermionicCoverFiniteFaceTopEdges_subset (n : ℕ)
    [Fintype (parafermionicCoverBoxGraph n).edgeSet] :
    parafermionicCoverFiniteFaceTopEdges n ⊆ (parafermionicCoverBoxGraph n).edgeFinset := by
  classical
  intro e he
  rcases Finset.mem_image.mp he with ⟨f,hf,rfl⟩
  exact SimpleGraph.mem_edgeFinset.mpr
    (parafermionicCoverFiniteFaceTopEdge_mem_edgeSet n f.1 f.2)

private theorem parafermionicCoverFiniteFaceTopEdges_card (n : ℕ) :
    (parafermionicCoverFiniteFaceTopEdges n).card =
      (parafermionicCoverFiniteOrdinaryFaces n).card := by
  classical
  rw [parafermionicCoverFiniteFaceTopEdges, Finset.card_image_of_injOn]
  · simp
  · intro f hf g hg he
    apply Subtype.ext
    apply parafermionicCoverFiniteFaceTopEdge_injective n f.2 g.2
    have hm := congrArg (Sym2.map Subtype.val) he
    rw [parafermionicCoverFaceTopEdgeBox_map, parafermionicCoverFaceTopEdgeBox_map] at hm
    exact hm

private theorem parafermionicCoverBoxGraphWithoutFaceTops_edgeSet_eq (n : ℕ) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).edgeSet =
      (parafermionicCoverBoxGraph n).edgeSet \ (parafermionicCoverFiniteFaceTopEdges n : Set _) := by
  classical
  ext e
  let u := e.out.1
  let v := e.out.2
  have hout : s(u,v) = e := e.out_eq
  rw [← hout]
  simp only [SimpleGraph.mem_edgeSet, Set.mem_sdiff]
  constructor
  · rintro ⟨hAdj,hnot⟩
    refine ⟨hAdj,?_⟩
    intro he
    rcases Finset.mem_image.mp he with ⟨f,hf,hfe⟩
    have hm := congrArg (Sym2.map Subtype.val) hfe
    rw [parafermionicCoverFaceTopEdgeBox_map] at hm
    rw [Sym2.map_mk] at hm
    have htop : parafermionicCoverFiniteFaceTopEdge f.1 = s(u.1,v.1) := by
      simpa [u,v] using hm
    exact hnot f.1 f.2 htop
  · rintro ⟨hAdj,hnot⟩
    refine ⟨hAdj,?_⟩
    intro f hf htop
    apply hnot
    apply Finset.mem_image.mpr
    refine ⟨⟨f,hf⟩,by simp,?_⟩
    apply Sym2.map.injective Subtype.val_injective
    rw [parafermionicCoverFaceTopEdgeBox_map, htop, Sym2.map_mk]

private theorem parafermionicCoverBoxGraphWithoutFaceTops_edgeFinset_card_add
    (n : ℕ) [Fintype (parafermionicCoverBoxGraph n).edgeSet]
    [Fintype (parafermionicCoverBoxGraphWithoutFaceTops n).edgeSet] :
    (parafermionicCoverBoxGraphWithoutFaceTops n).edgeFinset.card +
      (parafermionicCoverFiniteOrdinaryFaces n).card =
        (parafermionicCoverBoxGraph n).edgeFinset.card := by
  classical
  have heq : (parafermionicCoverBoxGraphWithoutFaceTops n).edgeFinset =
      (parafermionicCoverBoxGraph n).edgeFinset \ parafermionicCoverFiniteFaceTopEdges n := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff, Finset.mem_coe,
      parafermionicCoverBoxGraphWithoutFaceTops_edgeSet_eq,Set.mem_sdiff]
  have hsub : parafermionicCoverFiniteFaceTopEdges n ⊆
      (parafermionicCoverBoxGraph n).edgeFinset :=
    parafermionicCoverFiniteFaceTopEdges_subset n
  have hdiff : ((parafermionicCoverBoxGraph n).edgeFinset \
      parafermionicCoverFiniteFaceTopEdges n).card =
        (parafermionicCoverBoxGraph n).edgeFinset.card -
          (parafermionicCoverFiniteFaceTopEdges n).card :=
    Finset.card_sdiff_of_subset hsub
  have hfaces : (parafermionicCoverFiniteFaceTopEdges n).card =
      (parafermionicCoverFiniteOrdinaryFaces n).card :=
    parafermionicCoverFiniteFaceTopEdges_card n
  rw [heq]
  rw [hdiff, ← hfaces]
  exact Nat.sub_add_cancel (Finset.card_le_card hsub)

 theorem parafermionicCoverBoxGraphWithoutFaceTops_isTree
    (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).IsTree := by
  classical
  have hconn := parafermionicCoverBoxGraphWithoutFaceTops_connected n hn
  have hremove := parafermionicCoverBoxGraphWithoutFaceTops_edgeFinset_card_add n
  have heuler := parafermionicCoverFiniteEulerCount n hn
  have hcancel :
      ((parafermionicCoverBoxGraphWithoutFaceTops n).edgeFinset.card + 1) +
          (parafermionicCoverFiniteOrdinaryFaces n).card =
        Fintype.card (ParafermionicCoverBoxVertex n) +
          (parafermionicCoverFiniteOrdinaryFaces n).card := by
    calc
      _ = ((parafermionicCoverBoxGraphWithoutFaceTops n).edgeFinset.card +
          (parafermionicCoverFiniteOrdinaryFaces n).card) + 1 := by omega
      _ = (parafermionicCoverBoxGraph n).edgeFinset.card + 1 :=
        congrArg (fun x => x + 1) hremove
      _ = Fintype.card (ParafermionicCoverBoxVertex n) +
          (parafermionicCoverFiniteOrdinaryFaces n).card := heuler.symm
  have hcard : (parafermionicCoverBoxGraphWithoutFaceTops n).edgeFinset.card + 1 =
      Fintype.card (ParafermionicCoverBoxVertex n) := Nat.add_right_cancel hcancel
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using hcard

end

end PottsContinuity.FKC.Medial
