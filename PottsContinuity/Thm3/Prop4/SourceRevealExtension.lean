module

public import PottsContinuity.Thm3.RSW.StoppingAverage

/-!
# Completing source records by a deterministic function of the raw record

The extra queried edges can depend on the already recorded set and open
states. Retaining the raw reveal makes the completion a stopping set and
preserves every raw complete observation.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Agreement on a larger queried set implies agreement on each subset. -/
theorem finset_inter_eq_of_agree_on_superset {E : Type*} [edgeEq : DecidableEq E]
    (A C R S : Finset E) (hRS : R ⊆ S) (hS : C ∩ S = A ∩ S) : C ∩ R = A ∩ R := by
  ext e
  by_cases he : e ∈ R
  · have heS := hRS he
    have hh := Finset.ext_iff.mp hS e
    simpa only [Finset.mem_inter,he,heS,and_true] using hh
  · simp only [Finset.mem_inter,he,and_false]

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance sourceExtensionEdgeEq : DecidableEq G.edgeSet := Classical.decEq _

omit [Finite V] in
/-- The union of two actual stable reveals is again stable. Agreement on the
union determines both original recorded sets separately. -/
theorem sourceRevealUnion_stable
    (left right : Configuration G → Configuration G)
    (hleft : ∀ A C, C ∩ left A = A ∩ left A → left C = left A)
    (hright : ∀ A C, C ∩ right A = A ∩ right A → right C = right A)
    (A C : Configuration G)
    (hagree : C ∩ (left A ∪ right A) = A ∩ (left A ∪ right A)) :
    left C ∪ right C = left A ∪ right A := by
  have hL := finset_inter_eq_of_agree_on_superset A C (left A) _ Finset.subset_union_left hagree
  have hR := finset_inter_eq_of_agree_on_superset A C (right A) _ Finset.subset_union_right hagree
  rw [hleft A C hL,hright A C hR]

omit [Finite V] in

omit [Finite V] in
/-- Every attained complete observation of a larger reveal determines the
raw observation, whenever the raw reveal is stable and retained. -/
theorem raw_stoppingObservation_eq_of_retained_observation
    (raw reveal : Configuration G → Configuration G)
    (hstable : ∀ A C, C ∩ raw A = A ∩ raw A → raw C = raw A)
    (hretain : ∀ A, raw A ⊆ reveal A)
    (A C : Configuration G)
    (hobs : RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C) :
    RSW.stoppingObservationMap raw A = RSW.stoppingObservationMap raw C := by
  have hS : reveal A = reveal C := congrArg Prod.fst (congrArg Subtype.val hobs)
  have hB : A ∩ reveal A = C ∩ reveal C := congrArg Prod.snd (congrArg Subtype.val hobs)
  have hagree : C ∩ reveal A = A ∩ reveal A := by simpa only [hS] using hB.symm
  have hraw := finset_inter_eq_of_agree_on_superset A C (raw A) (reveal A) (hretain A) hagree
  have hR := hstable A C hraw
  apply Subtype.ext
  change (raw A,A ∩ raw A) = (raw C,C ∩ raw C)
  rw [hR,hraw]

end
end PottsContinuity.Thm3.Prop4
