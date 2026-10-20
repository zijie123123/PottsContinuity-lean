module

public import PottsContinuity.Thm3.Push.CompleteSourcePrefixSelector
public import PottsContinuity.Thm3.Push.StrictFirstHitPrefixSelection
public import PottsContinuity.PlanarMixed.FiniteSlit.RectanglePrefixCrosscuts

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 RSW Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- A fixed first-hit trace is exactly first contact at the full walk length. -/
theorem firstContactTrace_fixed_iff_firstContact_at_length
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (hb : b ∈ S) :
    firstContactTrace S p.support = some p.support ↔ IsFirstContact p S p.length := by
  constructor
  · intro hfixed
    obtain ⟨k,hk,hcrop⟩ := firstContactTrace_exists_prefix p S hb
    have hs : (p.take k).support = p.support := Option.some.inj (hcrop.symm.trans hfixed)
    have hlen := congrArg List.length hs
    simp only [SimpleGraph.Walk.length_support,SimpleGraph.Walk.take_length] at hlen
    have hkle : k ≤ p.length := hk.1
    have heq : k = p.length := by omega
    simpa only [heq] using hk
  · intro hk
    have hcrop := firstContactTrace_eq_support_take p S p.length hk
    have hs : (p.take p.length).support = p.support := by
      rw [SimpleGraph.Walk.support_take,← p.length_support,List.take_length]
    simpa only [hs] using hcrop

end
end PottsContinuity.Push
