module

public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import Mathlib.Tactic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12
noncomputable section
local instance arcLabelPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Label a left-exterior vertex by its tag, otherwise a right-exterior
vertex by its tag, and every remaining vertex by its literal identity. The
left test has priority; disjoint exteriors have exactly their separate tags. -/
def twoArcAttachmentLabel {W : Type*} (A B : Set W) (u : W) : Bool ⊕ W :=
  if u ∈ A then Sum.inl false else if u ∈ B then Sum.inl true else Sum.inr u

/-- Equality of the labels is exactly equality or membership in one of the
two separate exterior classes, with no extra identifications. -/
theorem twoArcAttachmentLabel_eq_iff {W : Type*} (A B : Set W) (hAB : Disjoint A B)
    (u v : W) :
    twoArcAttachmentLabel A B u = twoArcAttachmentLabel A B v ↔
      u=v ∨ (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
  have hnot : ∀ z, z ∈ A → z ∉ B := fun z hzA hzB => Set.disjoint_left.mp hAB hzA hzB
  by_cases huA : u ∈ A <;> by_cases huB : u ∈ B <;>
    by_cases hvA : v ∈ A <;> by_cases hvB : v ∈ B <;>
    simp_all [twoArcAttachmentLabel] <;> (rintro rfl; contradiction)

/-- The two-class boundary quotient embeds into the actual ambient labels,
for any injective retained carrier. No representative is chosen. -/
def twoArcAttachmentQuotientEmbedding {V W : Type*} [Finite V] (f : V ↪ W)
    (A B : Set W) (hAB : Disjoint A B) :
    Quotient (twoBlockBoundary (f ⁻¹' A) (f ⁻¹' B) (hAB.preimage f)).partition ↪ Bool ⊕ W where
  toFun := Quotient.lift (fun v => twoArcAttachmentLabel A B (f v)) (by
    intro u v huv
    apply (twoArcAttachmentLabel_eq_iff A B hAB (f u) (f v)).mpr
    rcases (twoBlockBoundary_partition_rel _ _ _ u v).mp huv with rfl | ha | hb
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr hb))
  inj' := by
    intro u v
    induction u using Quotient.inductionOn with
    | h u =>
      induction v using Quotient.inductionOn with
      | h v =>
        intro huv
        apply Quotient.sound
        apply (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        rcases (twoArcAttachmentLabel_eq_iff A B hAB (f u) (f v)).mp huv with heq | ha | hb
        · exact Or.inl (f.injective heq)
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr hb)

/-- On every retained vertex the embedding gives exactly its ambient label. -/
theorem twoArcAttachmentQuotientEmbedding_apply {V W : Type*} [Finite V] (f : V ↪ W)
    (A B : Set W) (hAB : Disjoint A B) (v : V) :
    twoArcAttachmentQuotientEmbedding f A B hAB
      (Quotient.mk (twoBlockBoundary (f ⁻¹' A) (f ⁻¹' B) (hAB.preimage f)).partition v) =
      twoArcAttachmentLabel A B (f v) := rfl

end
end PottsContinuity.Push
