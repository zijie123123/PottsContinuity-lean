module

public import PottsContinuity.Thm3.RSW.StripHorizontalReflection

@[expose] public section

namespace PottsContinuity.RSW

/-- Horizontal reflection preserves a symmetric source interval and confines
the entire reflected arm to the same rectangle. -/
theorem stripRectangleArm_reflected_mem (n : ℕ) (l r H a b d : ℤ)
    (hcenter : a+b = l+r) (ω : StripConfiguration n)
    (hω : ω ∈ stripRectangleArm n l r H a b {v | v.val.1 = d}) :
    stripHorizontalReflectionConfiguration n (l+r) ω ∈
      stripRectangleArm n l r H a b {v | v.val.1 = l+r-d} := by
  obtain ⟨u,v,p,hu,hv,hp⟩ := hω
  change a ≤ u.val.1 ∧ u.val.1 ≤ b ∧ u.val.2 = 0 at hu
  let φ := stripHorizontalReflectionOpenHom n (l+r) ω
  refine ⟨φ u,φ v,p.map φ,?_,?_,?_⟩
  · change a ≤ l+r-u.val.1 ∧ l+r-u.val.1 ≤ b ∧ u.val.2 = 0
    exact ⟨by omega,by omega,hu.2.2⟩
  · change l+r-v.val.1 = l+r-d
    change v.val.1 = d at hv
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    have h := hp w hw
    simp only [stripRectangleVertices,Finset.mem_preimage,
      latticeRectangle,Finset.mem_product,Finset.mem_Icc] at h
    rw [stripRectangleVertices,Finset.mem_preimage]
    change (l+r-w.val.1,w.val.2) ∈ latticeRectangle l r 0 H
    simp only [latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    exact ⟨⟨by omega,by omega⟩,h.2⟩

/-- The reflected left-arm event is exactly the original right-arm event. -/
theorem stripRectangleArm_left_reflection_iff (n : ℕ) (l r H a b : ℤ)
    (hcenter : a+b = l+r) (ω : StripConfiguration n) :
    stripHorizontalReflectionConfiguration n (l+r) ω ∈
      stripRectangleArm n l r H a b {v | v.val.1 = l} ↔
    ω ∈ stripRectangleArm n l r H a b {v | v.val.1 = r} := by
  constructor
  · intro h
    have ht := stripRectangleArm_reflected_mem n l r H a b l hcenter
      (stripHorizontalReflectionConfiguration n (l+r) ω) h
    rw [stripHorizontalReflectionConfiguration_involutive n (l+r) ω] at ht
    simpa only [add_sub_cancel_left] using ht
  · intro h
    have ht := stripRectangleArm_reflected_mem n l r H a b r hcenter ω h
    simpa only [add_sub_cancel_right] using ht

end PottsContinuity.RSW
