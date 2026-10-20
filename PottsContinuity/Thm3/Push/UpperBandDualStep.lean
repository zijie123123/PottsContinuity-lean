module

public import PottsContinuity.Thm3.Push.UpperBandCarrier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- An actual closed-dual step in the outer rectangle pulls back to the
band's TRUE complementary dual, provided it is not along the band's bottom
port row. This is the step transport required by first-arrival clipping. -/
theorem upper_band_closed_dual_step_pullback (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H)
    (A : Configuration (rectangleGraph a w H))
    (u v : RectangleDualVertex (a.1,a.2+(t : ℤ)) w (H-t))
    (hxy : (openGraph (rectangleDualGraph a w H) (rectangleDualConfiguration a w H A)).Adj
      (rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht) u)
      (rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht) v))
    (hnot : ¬ (u.val.2=a.2+(t : ℤ)-1 ∧ v.val.2=a.2+(t : ℤ)-1)) :
    (openGraph (rectangleDualGraph (a.1,a.2+(t : ℤ)) w (H-t))
      (rectangleDualConfiguration (a.1,a.2+(t : ℤ)) w (H-t)
        (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A))).Adj u v := by
  obtain ⟨f,hf,hpair⟩ := rectangle_closed_dual_step_original_bond a w H A hxy
  change s(u.val,v.val)=_ at hpair
  have hu := (mem_latticeRectangle (a.1-1,a.2+(t : ℤ)-1) u.val (w+1) (H-t+1)).mp u.property
  have hv := (mem_latticeRectangle (a.1-1,a.2+(t : ℤ)-1) v.val (w+1) (H-t+1)).mp v.property
  have hulo : a.2+(t : ℤ)-1 ≤ u.val.2 := by simpa only [Prod.snd] using hu.2.1
  have hvlo : a.2+(t : ℤ)-1 ≤ v.val.2 := by simpa only [Prod.snd] using hv.2.1
  exact rectangle_closed_dual_step_pullback (rectangle_upper_band_subset a w H t ht) A f hf
    (upper_band_crossed_bond_endpoints_mem a w H t ht f u.val v.val hpair hulo hvlo hnot) u v hpair

end
end PottsContinuity.Push
