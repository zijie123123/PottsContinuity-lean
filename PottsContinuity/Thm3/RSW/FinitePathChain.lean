module

public import PottsContinuity.Thm3.RSW.FinitePath
public import PottsContinuity.Thm3.RSW.WalkClipping

/-! Concatenation and clipping of finite confined paths, used by the corrected
common-box reflected construction. Every walk constraint is retained. -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Enlarging the allowed path region retains the original actual walk. -/
theorem finitePathEvent_mono_region (V S T : Finset (ℤ × ℤ)) (hST : S ⊆ T)
    (x y : ℤ × ℤ) : finitePathEvent V S x y ⊆ finitePathEvent V T x y := by
  rintro ω ⟨hx,hy,w,hw⟩
  exact ⟨hx,hy,w,fun v hv => hST (hw v hv)⟩

/-- Two confined paths with a common endpoint concatenate in the same region. -/
theorem finitePathEvent_trans (V S : Finset (ℤ × ℤ)) (x y z : ℤ × ℤ) :
    finitePathEvent V S x y ∩ finitePathEvent V S y z ⊆ finitePathEvent V S x z := by
  rintro ω ⟨⟨hx,hy,p,hp⟩,⟨_,hz,r,hr⟩⟩
  refine ⟨hx,hz,p.append r,?_⟩
  intro v hv
  rcases (SimpleGraph.Walk.mem_support_append_iff p r).mp hv with hv | hv
  · exact hp v hv
  · exact hr v hv

/-- A positive finite chain with exactly matching endpoints yields a single
confined path. No intersection theorem is needed for these endpoint chains. -/
theorem finitePathEvent_chain (V S : Finset (ℤ × ℤ)) (u : ℕ → ℤ × ℤ)
    (ω : (squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool)
    (k : ℕ) (hk : 1 ≤ k)
    (hpaths : ∀ j : ℕ, j < k → ω ∈ finitePathEvent V S (u j) (u (j+1))) :
    ω ∈ finitePathEvent V S (u 0) (u k) := by
  suffices h : ∀ k : ℕ, 1 ≤ k →
      (∀ j : ℕ, j < k → ω ∈ finitePathEvent V S (u j) (u (j+1))) →
      ω ∈ finitePathEvent V S (u 0) (u k) from h k hk hpaths
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro hk hpaths
    by_cases hk0 : k = 0
    · subst k
      exact hpaths 0 (by omega)
    · exact finitePathEvent_trans V S (u 0) (u k) (u (k+1))
        ⟨ih (by omega) (fun j hj => hpaths j (by omega)), hpaths k (by omega)⟩

/-- Every sampled open edge is an original induced lattice edge. -/
theorem rcOpenGraph_le_induced (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) :
    rcOpenGraph V ω ≤ squareLattice.induce (V:Set (ℤ × ℤ)) := by
  rw [rcOpenGraph,SimpleGraph.fromEdgeSet_le]
  rintro e ⟨⟨he,_⟩,_⟩
  exact he

/-- A confined path spanning the target width clips to an actual frozen
horizontal crossing, even when the original path goes beyond both sides. -/
theorem finitePathEvent_implies_horizontalCrossing
    (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ)
    (a b c d : ℤ) (hab : a ≤ b) (hx : x.1 ≤ a) (hy : b ≤ y.1)
    (hband : ∀ z ∈ S, z.2 ∈ Set.Icc c d)
    (ω : (squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool)
    (hpath : ω ∈ finitePathEvent V S x y) : horizontalCrossing V a b c d ω := by
  obtain ⟨hxV,hyV,w,hw⟩ := hpath
  have hstep : ∀ {u v : (V:Set (ℤ × ℤ))}, (rcOpenGraph V ω).Adj u v →
      v.val.1 ≤ u.val.1+1 := by
    intro u v huv
    have hsq := rcOpenGraph_le_induced V ω huv
    change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at hsq
    have h0 := abs_nonneg (u.val.2-v.val.2)
    have h1 := neg_le_abs (u.val.1-v.val.1)
    omega
  obtain ⟨u,v,p,hu,hv,hp⟩ := walk_clip_coordinate (rcOpenGraph V ω)
    (fun z => z.val.1) hstep a b hab (fun z => z.val.2 ∈ Set.Icc c d) w hx hy
    (fun z hz => hband z.val (hw z hz))
  exact ⟨u,v,p,⟨hu,(hp u p.start_mem_support).2.2⟩,
    ⟨hv,(hp v p.end_mem_support).2.2⟩, fun z hz =>
      ⟨⟨(hp z hz).1,(hp z hz).2.1⟩,(hp z hz).2.2⟩⟩

end PottsContinuity.RSW
