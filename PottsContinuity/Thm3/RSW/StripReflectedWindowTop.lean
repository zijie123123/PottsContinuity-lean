module

public import PottsContinuity.Thm3.RSW.StripTranslatedWindowTop
public import PottsContinuity.Thm3.RSW.StripHorizontalReflection

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- A reflected source window remains in a sufficiently large original window. -/
theorem stripWindow_reflection_containment (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) :
    ∀ z ∈ stripWindow n M, (c-z.1,z.2) ∈ stripWindow n N := by
  intro z hz
  have hMN' : (M:ℤ)+(c.natAbs:ℤ) ≤ N := by exact_mod_cast hMN
  have hpos : c ≤ (c.natAbs:ℤ) := Int.le_natAbs
  have hneg : -(c.natAbs:ℤ) ≤ c := by
    have h : -c ≤ ((-c).natAbs:ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at h
    omega
  simp only [stripWindow,PottsContinuity.latticeRectangle,
    Finset.mem_product,Finset.mem_Icc] at hz ⊢
  exact ⟨⟨by omega,by omega⟩,hz.2⟩

/-- Literal reflection of every source vertex into the larger window. -/
def stripWindowReflectionEmbedding (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) :
    (stripWindow n M : Set (ℤ × ℤ)) ↪ (stripWindow n N : Set (ℤ × ℤ)) where
  toFun := fun z => ⟨(c-z.val.1,z.val.2),stripWindow_reflection_containment n M N c hMN z.val z.property⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    have hx := congrArg (fun z : (stripWindow n N : Set (ℤ × ℤ)) => z.val.1) h
    have hy := congrArg (fun z : (stripWindow n N : Set (ℤ × ℤ)) => z.val.2) h
    apply Prod.ext <;> dsimp at hx hy ⊢ <;> omega

/-- Reflection maps original window edges into original larger-window edges. -/
theorem stripWindowReflection_graph_le (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) :
    (PottsContinuity.squareLattice.induce (stripWindow n M : Set (ℤ × ℤ))).map
      (stripWindowReflectionEmbedding n M N c hMN) ≤
      PottsContinuity.squareLattice.induce (stripWindow n N : Set (ℤ × ℤ)) := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ x y).mp hxy
  change |(c-u.val.1)-(c-v.val.1)|+|u.val.2-v.val.2|=1
  rw [sub_sub_sub_cancel_left,abs_sub_comm v.val.1 u.val.1]
  exact huv

/-- Top-only wiring pulls back exactly under the reflected window embedding. -/
theorem stripWindow_reflected_top_pullback_partition (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) :
    (isolatedExtensionPullbackBoundary (stripWindowReflectionEmbedding n M N c hMN)
      (stripWindowBoundary n N 0)).partition = (stripWindowBoundary n M 0).partition := by
  let f := stripWindowReflectionEmbedding n M N c hMN
  apply Setoid.ext
  intro u v
  change ((f u = f v) ∨ f u ∈ stripWindowWiredVertices n N 0 ∧
      f v ∈ stripWindowWiredVertices n N 0) ↔
    ((u = v) ∨ u ∈ stripWindowWiredVertices n M 0 ∧ v ∈ stripWindowWiredVertices n M 0)
  simp only [stripWindowWiredVertices,Set.mem_ofPred_eq,Fin.zero_ne_one,false_and,or_false]
  exact or_congr f.injective.eq_iff Iff.rfl

end
end PottsContinuity.RSW
