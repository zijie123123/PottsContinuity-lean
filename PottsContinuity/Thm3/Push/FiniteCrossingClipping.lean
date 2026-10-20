module

public import PottsContinuity.Thm3.RSW.WalkClipping
public import PottsContinuity.Thm3.Push.OpenStateEmbedding

@[expose] public section

namespace PottsContinuity.Push

/-- Actual finite crossings can be clipped horizontally and their vertical
support enlarged. Adapted from RSW.WalkClipping's strip crossing proof,
using the same original-edge no-jump bound on a finite induced graph. -/
theorem horizontalCrossing_clip (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (a b c d A B C D : ℤ)
    (hA : A ≤ a) (hab : a ≤ b) (hB : b ≤ B) (hC : c ≤ C) (hD : D ≤ d) :
    horizontalCrossing V A B C D ω → horizontalCrossing V a b c d ω := by
  rintro ⟨u, v, w, hu, hv, hw⟩
  have hstep : ∀ {u v : (V : Set (ℤ × ℤ))}, (rcOpenGraph V ω).Adj u v →
      v.val.1 ≤ u.val.1 + 1 := by
    intro u v huv
    have he := (booleanOpenGraph_adj (squareLattice.induce (V : Set (ℤ × ℤ))) ω u v).mp huv
    have hsq := (squareLattice.induce (V : Set (ℤ × ℤ))).mem_edgeSet.mp he.1
    change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at hsq
    have hn := abs_nonneg (u.val.2-v.val.2)
    have hd := neg_le_abs (u.val.1-v.val.1)
    omega
  obtain ⟨x, y, p, hx, hy, hp⟩ := RSW.walk_clip_coordinate (rcOpenGraph V ω)
    (fun z => z.val.1) hstep a b hab (fun z => C ≤ z.val.2 ∧ z.val.2 ≤ D) w
    (by have := hu.1; simp only [Set.mem_singleton_iff] at this; omega)
    (by have := hv.1; simp only [Set.mem_singleton_iff] at this; omega)
    (fun z hz => (hw z hz).2)
  refine ⟨x, y, p, ⟨hx, ?_⟩, ⟨hy, ?_⟩, ?_⟩
  · exact ⟨hC.trans (hp x p.start_mem_support).2.2.1,
      (hp x p.start_mem_support).2.2.2.trans hD⟩
  · exact ⟨hC.trans (hp y p.end_mem_support).2.2.1,
      (hp y p.end_mem_support).2.2.2.trans hD⟩
  · intro z hz
    exact ⟨⟨(hp z hz).1, (hp z hz).2.1⟩,
      hC.trans (hp z hz).2.2.1, (hp z hz).2.2.2.trans hD⟩

end PottsContinuity.Push
