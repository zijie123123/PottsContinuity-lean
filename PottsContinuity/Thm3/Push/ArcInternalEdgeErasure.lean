module

public import PottsContinuity.BD12.WiredArcRemoval
public import PottsContinuity.PlanarMixed.CanonicalCutBonds

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance arcErasureEdgeEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Erasing bonds internal to either endpoint arc preserves actual
arc-to-arc connection, including empty or overlapping endpoint sets. -/
theorem arcsConnectionEvent_sdiff_internal_edges (A B : Set V)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u,v),G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R →
        (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (C : Configuration G) :
    C \ R ∈ arcsConnectionEvent G A B ↔ C ∈ arcsConnectionEvent G A B := by
  classical
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · by_cases hAB : Disjoint A B
      · have hpre : ∀ (u v : V) (huv : G.Adj u v),
            (⟨s(u,v),G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R →
              (twoBlockBoundary A B hAB).partition.r u v := by
          intro u v huv he
          exact (twoBlockBoundary_partition_rel A B hAB u v).mpr (Or.inr (hR u v huv he))
        have h := arcsConnectionEvent_union_removed A B hAB hA hB R hpre
          (C \ R) ⟨C ∩ R,Finset.inter_subset_right⟩
        simpa only [Finset.sdiff_union_inter] using h.symm
      · obtain ⟨v,hvA,hvB⟩ := Set.not_disjoint_iff.mp hAB
        exact iff_of_true ⟨v,hvA,v,hvB,⟨SimpleGraph.Walk.nil⟩⟩
          ⟨v,hvA,v,hvB,⟨SimpleGraph.Walk.nil⟩⟩
    · have hBempty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      subst B
      simp only [arcsConnectionEvent,Set.mem_ofPred_eq,Set.mem_empty_iff_false,
        false_and,exists_false,and_false]
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp only [arcsConnectionEvent,Set.mem_ofPred_eq,Set.mem_empty_iff_false,
      false_and,exists_false]

end
end PottsContinuity.Push
