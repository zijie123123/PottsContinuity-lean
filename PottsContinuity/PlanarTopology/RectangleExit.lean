module

public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- A unit-step walk starting inside a closed strip, never below its bottom,
and ending beyond one of the other three sides has a contiguous prefix ending
on one of those sides and entirely confined to the rectangle. Repeated visits
and non-simple walks are allowed. -/
theorem walk_prefix_to_three_sides {V : Type*} {G : SimpleGraph V}
    (f g : V → ℤ)
    (hf : ∀ x y, G.Adj x y → |f x-f y| ≤ 1)
    (hg : ∀ x y, G.Adj x y → |g x-g y| ≤ 1)
    {u v : V} (p : G.Walk u v) (left right bottom top : ℤ)
    (hu : left ≤ f u ∧ f u ≤ right ∧ g u ≤ top)
    (hlow : ∀ z ∈ p.support, bottom ≤ g z)
    (hv : f v ≤ left ∨ right ≤ f v ∨ top ≤ g v) :
    ∃ z, ∃ (r : G.Walk u z) (s : G.Walk z v), p = r.append s ∧
      (f z = left ∨ f z = right ∨ g z = top) ∧
      ∀ x ∈ r.support, left ≤ f x ∧ f x ≤ right ∧ bottom ≤ g x ∧ g x ≤ top := by
  induction p with
  | @nil u =>
      refine ⟨u,.nil,.nil,rfl,?_,?_⟩
      · rcases hv with hv | hv | hv
        · exact Or.inl (le_antisymm hv hu.1)
        · exact Or.inr (Or.inl (le_antisymm hu.2.1 hv))
        · exact Or.inr (Or.inr (le_antisymm hu.2.2 hv))
      · intro x hx
        have hx' : x = u := by simpa using hx
        subst x
        exact ⟨hu.1,hu.2.1,hlow _ (by simp),hu.2.2⟩
  | @cons u w v hadj p ih =>
      by_cases hside : f u = left ∨ f u = right ∨ g u = top
      · refine ⟨u,.nil,p.cons hadj,rfl,hside,?_⟩
        intro x hx
        have hx' : x = u := by simpa using hx
        subst x
        exact ⟨hu.1,hu.2.1,hlow _ (by simp),hu.2.2⟩
      · have hfw := abs_le.mp (hf u w hadj)
        have hgw := abs_le.mp (hg u w hadj)
        have hw : left ≤ f w ∧ f w ≤ right ∧ g w ≤ top := by
          push Not at hside
          omega
        have hlow' : ∀ z ∈ p.support, bottom ≤ g z := fun z hz =>
          hlow z (List.mem_cons.mpr (Or.inr hz))
        obtain ⟨z,r,s,he,hz,hr⟩  := ih hw hlow' hv
        refine ⟨z,r.cons hadj,s,?_,hz,?_⟩
        · rw [he]
          rfl
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hu.1,hu.2.1,hlow _ (by simp),hu.2.2⟩
          · exact hr x hx

end PottsContinuity.PlanarTopology
