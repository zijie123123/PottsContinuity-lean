module

public import PottsContinuity.Thm3.RSW.StripBandArm

@[expose] public section

namespace PottsContinuity.RSW

/-- A height-confined source arm exits a smaller rectangle through one of
its three upper sides. The same sampled open path supplies the witness. -/
theorem stripBandArm_subset_three_rectangleArms (n : ℕ) (l r H a b : ℤ)
    (hla : l ≤ a) (hbr : b ≤ r) :
    stripBandArm n H a b ⊆
      stripRectangleArm n l r H a b {v | v.val.2 = H} ∪
      (stripRectangleArm n l r H a b {v | v.val.1 = l} ∪
       stripRectangleArm n l r H a b {v | v.val.1 = r}) := by
  rintro ω ⟨u,v,p,ha,hb,hu,hv,hp⟩
  have hstepx : ∀ {u v : stripVertices n}, (stripOpenGraph n ω).Adj u v →
      |v.val.1-u.val.1| ≤ 1 := by
    intro u v huv
    have h := stripOpenGraph_le n ω huv
    change |u.val.1-v.val.1| + |u.val.2-v.val.2| = 1 at h
    rw [abs_sub_comm]
    have := abs_nonneg (u.val.2-v.val.2)
    omega
  have hstepy : ∀ {u v : stripVertices n}, (stripOpenGraph n ω).Adj u v →
      |v.val.2-u.val.2| ≤ 1 := by
    intro u v huv
    have h := stripOpenGraph_le n ω huv
    change |u.val.1-v.val.1| + |u.val.2-v.val.2| = 1 at h
    rw [abs_sub_comm]
    have := abs_nonneg (u.val.1-v.val.1)
    omega
  have huH := hp u p.start_mem_support
  obtain ⟨t,q,ht,hq,_⟩ := walk_reach_three_sides (stripOpenGraph n ω)
    (fun z => z.val.1) (fun z => z.val.2) hstepx hstepy l r H p
    (by omega) (by omega) (fun z hz => (hp z hz).1)
  have hbox : ∀ z ∈ q.support, z ∈ stripRectangleVertices n l r 0 H := by
    intro z hz
    simp only [stripRectangleVertices, Finset.mem_preimage,
      latticeRectangle, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨(hq z hz).1,(hq z hz).2.1⟩,(hq z hz).2.2⟩
  rcases ht with ht | ht | ht
  · exact Or.inr (Or.inl ⟨u,t,q,⟨ha,hb,hu⟩,ht,hbox⟩)
  · exact Or.inr (Or.inr ⟨u,t,q,⟨ha,hb,hu⟩,ht,hbox⟩)
  · exact Or.inl ⟨u,t,q,⟨ha,hb,hu⟩,ht,hbox⟩

end PottsContinuity.RSW
