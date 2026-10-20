module

public import PottsContinuity.Thm3.Prop4.ClosedTubeConnectorWalks
public import PottsContinuity.Thm3.Prop4.SampledRectangleDualArms

/-!
# Moving both stopped sampled arms to their original cut roots

All four walks belong to the same restored primal sample. The lower walk
ends at its cut root and the upper walk starts at its cut root.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
local instance connectorSpliceOriginalEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Closing the two retained connector sets moves the actual stopped arms
to the original two cut roots, preserving their complementary target arcs. -/
theorem closed_connectors_splice_sampled_arms {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : LatticeVertex) (lo hi L U : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi)
    (hL : -(n : ℤ)-1 ≤ L ∧ L ≤ lo-1) (hU : hi ≤ U ∧ U ≤ n)
    (C : Configuration (tubePrimalRemainingGraph n r u v))
    (hC : Disjoint C (tubeRemainingCentralRows n r u v (L+1) (lo-1) ∪
      tubeRemainingCentralRows n r u v (hi+1) U))
    (lower upper : Set LatticeVertex)
    (harms : (edgeRestrictionConfigurationEquiv _ (rectangleTubeRevealedEdges n r u v) C).val ∪
      rectangleTubeRevealedEdges n r u v ∈
      sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        {(0,L)} {(0,U)} lower upper (fun _ => True) (fun _ => True)) :
    (edgeRestrictionConfigurationEquiv _ (rectangleTubeRevealedEdges n r u v) C).val ∪
      rectangleTubeRevealedEdges n r u v ∈
      sampledRectangleDualArmsEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        {(0,lo-1)} {(0,hi)} lower upper (fun _ => True) (fun _ => True) := by
  obtain ⟨minus,plus,_,_⟩ := closed_rows_sampled_cut_connectors hn r u v lo hi L U
    hlohi hrows hL hU C hC
  obtain ⟨f,hf,g,hg,s,hs,t,ht,pminus,pplus,_,_⟩ := harms
  have hf' : f = (0,L) := Set.mem_singleton_iff.mp hf
  have hg' : g = (0,U) := Set.mem_singleton_iff.mp hg
  subst f
  subst g
  exact ⟨(0,lo-1),rfl,(0,hi),rfl,s,hs,t,ht,pminus.append minus,plus.append pplus,
    fun _ _ => True.intro,fun _ _ => True.intro⟩

end
end PottsContinuity.Thm3.Prop4
