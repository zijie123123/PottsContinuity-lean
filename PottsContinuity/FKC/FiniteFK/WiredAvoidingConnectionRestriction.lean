-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingConnectionRestriction.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterComplement
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance wiredAvoidingPathEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance wiredAvoidingPathEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance wiredAvoidingInnerPathFintype (W : Set V) (S : Finset V)
    (A : Configuration G) : Fintype
      (G.induce (wiredAvoidingComplementSet G W S A)).edgeSet := Fintype.ofFinite _
local instance wiredAvoidingInnerPathDecidableEq (W : Set V) (S : Finset V)
    (A : Configuration G) : DecidableEq
      (G.induce (wiredAvoidingComplementSet G W S A)).edgeSet := Classical.decEq _

/-- Restricting the original configuration to the induced complement preserves
actual open adjacency between its vertices. -/
theorem wiredAvoidingComplement_openAdj_iff
    (W : Set V) (S : Finset V) (A : Configuration G)
    (x y : wiredAvoidingComplementSet G W S A) :
    (openGraph (G.induce (wiredAvoidingComplementSet G W S A))
      (embeddedConfigurationRestriction
        (G.induce (wiredAvoidingComplementSet G W S A)) G
        (wiredAvoidingComplementEmbedding G W S A)
        (wiredAvoidingComplementGraph_le (G := G) W S A) A)).Adj x y ↔
      (openGraph G A).Adj x.val y.val := by
  constructor
  · intro h
    rw [openGraph_adj] at h ⊢
    rcases h with ⟨ei, hei, heval⟩
    let eo := embeddedEdgeEmbedding (G.induce (wiredAvoidingComplementSet G W S A)) G
      (wiredAvoidingComplementEmbedding G W S A)
      (wiredAvoidingComplementGraph_le (G := G) W S A) ei
    have heo : eo ∈ A :=
      (mem_embeddedConfigurationRestriction
        (G.induce (wiredAvoidingComplementSet G W S A)) G
        (wiredAvoidingComplementEmbedding G W S A)
        (wiredAvoidingComplementGraph_le (G := G) W S A) A ei).mp hei
    refine ⟨eo, heo, ?_⟩
    change (wiredAvoidingComplementEmbedding G W S A).sym2Map ei.val = s(x.val, y.val)
    simp [wiredAvoidingComplementEmbedding, Function.Embedding.sym2Map_apply, heval]
  · intro h
    rw [openGraph_adj] at h ⊢
    rcases h with ⟨eo, heo, heval⟩
    have hAdj : G.Adj x.val y.val := G.mem_edgeSet.mp
      ((openGraph_le G A) ((openGraph_adj G A x.val y.val).mpr ⟨eo, heo, heval⟩))
    have hAdjInner : (G.induce (wiredAvoidingComplementSet G W S A)).Adj x y :=
      SimpleGraph.induce_adj.mpr hAdj
    let ei : (G.induce (wiredAvoidingComplementSet G W S A)).edgeSet :=
      ⟨s(x,y), hAdjInner⟩
    have heq : embeddedEdgeEmbedding (G.induce (wiredAvoidingComplementSet G W S A)) G
        (wiredAvoidingComplementEmbedding G W S A)
        (wiredAvoidingComplementGraph_le (G := G) W S A) ei = eo := by
      apply Subtype.ext
      change (wiredAvoidingComplementEmbedding G W S A).sym2Map ei.val = eo.val
      simp [ei, wiredAvoidingComplementEmbedding, Function.Embedding.sym2Map_apply, heval]
    refine ⟨ei, ?_, ?_⟩
    · have hmem : ei ∈ embeddedConfigurationRestriction
          (G.induce (wiredAvoidingComplementSet G W S A)) G
          (wiredAvoidingComplementEmbedding G W S A)
          (wiredAvoidingComplementGraph_le (G := G) W S A) A := by
        exact (mem_embeddedConfigurationRestriction
          (G.induce (wiredAvoidingComplementSet G W S A)) G
          (wiredAvoidingComplementEmbedding G W S A)
          (wiredAvoidingComplementGraph_le (G := G) W S A) A ei).2 (by
            rw [heq]
            exact heo)
      exact hmem
    · rfl

private theorem wiredAvoidingComplement_actualConnected_lift
    (W : Set V) (S : Finset V) (A : Configuration G)
    {x y : wiredAvoidingComplementSet G W S A}
    (h : ActualConnected (G.induce (wiredAvoidingComplementSet G W S A))
      (embeddedConfigurationRestriction
        (G.induce (wiredAvoidingComplementSet G W S A)) G
        (wiredAvoidingComplementEmbedding G W S A)
        (wiredAvoidingComplementGraph_le (G := G) W S A) A) x y) :
    ActualConnected G A x.val y.val := by
  change (openGraph (G.induce (wiredAvoidingComplementSet G W S A))
      (embeddedConfigurationRestriction
        (G.induce (wiredAvoidingComplementSet G W S A)) G
        (wiredAvoidingComplementEmbedding G W S A)
        (wiredAvoidingComplementGraph_le (G := G) W S A) A)).Reachable x y at h
  change (openGraph G A).Reachable x.val y.val
  exact (SimpleGraph.Reachable.map
    (show openGraph (G.induce (wiredAvoidingComplementSet G W S A))
        (embeddedConfigurationRestriction (G.induce (wiredAvoidingComplementSet G W S A)) G
          (wiredAvoidingComplementEmbedding G W S A)
          (wiredAvoidingComplementGraph_le (G := G) W S A) A) →g openGraph G A from
      { toFun := Subtype.val
        map_rel' := by
          intro u v huv
          exact (wiredAvoidingComplement_openAdj_iff W S A u v).mp huv }) h)

theorem wiredAvoidingConnection_toW_iff_complement
    (W : Set V) (S : Finset V) (A : Configuration G) {x : V}
    (hx : x ∉ wiredAvoidingClusterSet G W S A) :
    (∃ w : V, w ∈ W ∧ ActualConnected G A x w) ↔
      ∃ y : wiredAvoidingComplementSet G W S A,
        y.val ∈ W ∧ ActualConnected (G.induce (wiredAvoidingComplementSet G W S A))
          (embeddedConfigurationRestriction
            (G.induce (wiredAvoidingComplementSet G W S A)) G
            (wiredAvoidingComplementEmbedding G W S A)
            (wiredAvoidingComplementGraph_le (G := G) W S A) A) ⟨x, hx⟩ y := by
  constructor
  · rintro ⟨w, hw, hconn⟩
    have hWNotC : ∀ v, v ∈ W → v ∉ wiredAvoidingClusterSet G W S A := by
      intro v hv hvC
      exact (Set.disjoint_left.mp (wiredAvoidingClusterSet_disjoint W S A) hvC hv)
    let f : wiredAvoidingComplementSet G W S A ↪ V :=
      wiredAvoidingComplementEmbedding G W S A
    let R : Configuration (G.induce (wiredAvoidingComplementSet G W S A)) :=
      embeddedConfigurationRestriction (G.induce (wiredAvoidingComplementSet G W S A)) G f
        (wiredAvoidingComplementGraph_le (G := G) W S A) A
    have hprefix : ∀ y : V,
        (openGraph G A).Reachable x y →
        (∃ z : wiredAvoidingComplementSet G W S A,
          z.val ∈ W ∧ Relation.ReflTransGen (openGraph (G.induce (wiredAvoidingComplementSet G W S A)) R).Adj
            ⟨x, hx⟩ z) ∨
        (y ∉ W ∧ ∃ hyC : y ∉ wiredAvoidingClusterSet G W S A,
          Relation.ReflTransGen (openGraph (G.induce (wiredAvoidingComplementSet G W S A)) R).Adj
            ⟨x, hx⟩ ⟨y, hyC⟩) := by
      intro y hpath
      rw [SimpleGraph.reachable_iff_reflTransGen] at hpath
      induction hpath with
      | refl =>
          by_cases hxW : x ∈ W
          · exact Or.inl ⟨⟨x, hWNotC x hxW⟩, hxW,
              Relation.ReflTransGen.refl⟩
          · exact Or.inr ⟨hxW, ⟨hx, Relation.ReflTransGen.refl⟩⟩
      | @tail z y hprefix hedge ih =>
          rcases ih with hhit | ⟨hzW, hzC, hinner⟩
          · exact Or.inl hhit
          · by_cases hyW : y ∈ W
            · have hyC : y ∉ wiredAvoidingClusterSet G W S A := hWNotC y hyW
              have hinnerAdj : (openGraph (G.induce (wiredAvoidingComplementSet G W S A)) R).Adj
                  ⟨z, hzC⟩ ⟨y, hyC⟩ :=
                (wiredAvoidingComplement_openAdj_iff W S A ⟨z, hzC⟩ ⟨y, hyC⟩).2 hedge
              exact Or.inl ⟨⟨y, hyC⟩, hyW, hinner.tail hinnerAdj⟩
            · have hyC : y ∉ wiredAvoidingClusterSet G W S A := by
                intro hyIn
                have hzIn : z ∈ wiredAvoidingClusterSet G W S A :=
                  wiredAvoidingClusterSet_openEdge_closed W S A hyIn hzW hedge.symm
                exact hzC hzIn
              have hinnerAdj : (openGraph (G.induce (wiredAvoidingComplementSet G W S A)) R).Adj
                  ⟨z, hzC⟩ ⟨y, hyC⟩ :=
                (wiredAvoidingComplement_openAdj_iff W S A ⟨z, hzC⟩ ⟨y, hyC⟩).2 hedge
              exact Or.inr ⟨hyW, hyC, hinner.tail hinnerAdj⟩
    have houter : (openGraph G A).Reachable x w := hconn
    rcases hprefix w houter with hhit | ⟨hwNotW, _, hinner⟩
    · rcases hhit with ⟨y, hyW, hyPath⟩
      exact ⟨y, hyW, (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hyPath⟩
    · exact (hwNotW hw).elim
  · rintro ⟨y, hyW, hinner⟩
    exact ⟨y.val, hyW, wiredAvoidingComplement_actualConnected_lift W S A hinner⟩

end
end PottsContinuity.FKC.FiniteFK
