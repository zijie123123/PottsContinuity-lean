module

public import PottsContinuity.Thm3.RSW.StripEventLimit

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Translation along the infinite strip preserves all original bonds. -/
def stripTranslationIso (n : ℕ) (a : ℤ) : RSW.stripGraph n ≃g RSW.stripGraph n where
  toFun w := ⟨(w.val.1+a,w.val.2),w.property⟩
  invFun w := ⟨(w.val.1-a,w.val.2),w.property⟩
  left_inv w := by apply Subtype.ext; simp only [add_sub_cancel_right,Prod.eta]
  right_inv w := by apply Subtype.ext; simp only [sub_add_cancel,Prod.eta]
  map_rel_iff' := by
    intro u v
    change |(u.val.1+a)-(v.val.1+a)|+|u.val.2-v.val.2|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    rw [add_sub_add_right_eq_sub]

/-- Read the translated original strip bonds on the whole configuration space. -/
def stripTranslation (n : ℕ) (a : ℤ) (ω : RSW.StripConfiguration n) :
    RSW.StripConfiguration n := fun e => ω ((stripTranslationIso n a).mapEdgeSet e)

/-- Translation is continuous in the original bond-state topology. -/
theorem stripTranslation_continuous (n : ℕ) (a : ℤ) : Continuous (stripTranslation n a) :=
  continuous_pi fun e => continuous_apply ((stripTranslationIso n a).mapEdgeSet e)

/-- The bond translation preserves the coordinate order of states. -/
theorem stripTranslation_monotone (n : ℕ) (a : ℤ) : Monotone (stripTranslation n a) := by
  intro ω η h e
  exact h _

/-- A horizontally translated smaller window embeds in a sufficiently wide
original centred window without changing any heights. -/
def stripWindowTranslationEmbedding (n m M : ℕ) (a : ℤ)
    (hfit : |a|+(m:ℤ) ≤ (M:ℤ)) :
    (RSW.stripWindow n m : Set (ℤ × ℤ)) ↪ (RSW.stripWindow n M : Set (ℤ × ℤ)) where
  toFun w := ⟨(w.val.1+a,w.val.2),by
    have hw := w.property
    have ha := abs_le.mp (le_refl |a|)
    simp only [RSW.stripWindow,latticeRectangle,Finset.mem_coe,Finset.mem_product,
      Finset.mem_Icc] at hw ⊢
    exact ⟨⟨by omega,by omega⟩,hw.2⟩⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    have hx := congrArg (fun w => w.val.1) h
    have hy := congrArg (fun w => w.val.2) h
    exact Prod.ext (by dsimp at hx; omega) hy

/-- Every original edge of the translated smaller window is an actual larger
window edge. -/
theorem stripWindowTranslation_map_le (n m M : ℕ) (a : ℤ)
    (hfit : |a|+(m:ℤ) ≤ (M:ℤ)) :
    (PottsContinuity.squareLattice.induce
      (RSW.stripWindow n m : Set (ℤ × ℤ))).map (stripWindowTranslationEmbedding n m M a hfit) ≤
    PottsContinuity.squareLattice.induce (RSW.stripWindow n M : Set (ℤ × ℤ)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  change |(u.val.1+a)-(v.val.1+a)|+|u.val.2-v.val.2|=1
  rw [add_sub_add_right_eq_sub]
  exact huv

/-- The original top-only partition pulls back exactly under a horizontal
window translation; no lateral wiring is introduced. -/
theorem stripWindowTranslation_top_partition (n m M : ℕ) (a : ℤ)
    (hfit : |a|+(m:ℤ) ≤ (M:ℤ)) :
    (isolatedExtensionPullbackBoundary (stripWindowTranslationEmbedding n m M a hfit)
      (RSW.stripWindowBoundary n M 0)).partition =
    (RSW.stripWindowBoundary n m 0).partition := by
  apply Setoid.ext
  intro u v
  change (_ = _ ∨ _ ∧ _) ↔ (u=v ∨ _ ∧ _)
  rw [(stripWindowTranslationEmbedding n m M a hfit).injective.eq_iff]
  simp only [RSW.stripWindowWiredVertices,Set.mem_ofPred_eq,Fin.zero_ne_one,false_and,or_false]
  rfl

end
end PottsContinuity.Push
