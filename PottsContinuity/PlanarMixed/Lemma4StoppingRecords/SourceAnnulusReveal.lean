module

public import PottsContinuity.Thm3.RSW.Lemma4DualBands
public import PottsContinuity.Thm3.Push.CommonExplorationEvents

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Exploration Push RSW
noncomputable section
local instance routeSixAnnulusEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- Only original bonds internal to one of the two annulus outer boxes are
read. The entire middle band is deliberately not revealed. -/
def lemma4AnnulusBondReveal (n : ℕ) : Configuration (lemma4AmbientGraph n) := by
  classical
  letI sourceAnnulusRevealFintype : Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _
  exact Finset.univ.filter (fun e =>
    (∀ v ∈ e.val, v ∈ vertexBoxRegion (box (56*n)) (5*(n:ℤ),0) (2*n)) ∨
    (∀ v ∈ e.val, v ∈ vertexBoxRegion (box (56*n)) (-5*(n:ℤ),0) (2*n)))

theorem lemma4AnnulusPairEvent_read_from_annulusBonds (n : ℕ) :
    ReadFromReveal (fun _ => lemma4AnnulusBondReveal n) (lemma4AnnulusPairEvent n) := by
  intro A B hB
  have hs : B ∩ lemma4AnnulusBondReveal n=A ∩ lemma4AnnulusBondReveal n := hB.2
  apply (annulus_event_visible_in_recorded_outerBonds (box (56*n)) (5*(n:ℤ),0) n
    (lemma4AnnulusBondReveal n) (by
      intro e he
      classical
      simp only [lemma4AnnulusBondReveal,Finset.mem_filter,Finset.mem_univ,true_and]
      exact Or.inl he) B A hs).and
    (annulus_event_visible_in_recorded_outerBonds (box (56*n)) (-5*(n:ℤ),0) n
      (lemma4AnnulusBondReveal n) (by
        intro e he
        classical
        simp only [lemma4AnnulusBondReveal,Finset.mem_filter,Finset.mem_univ,true_and]
        exact Or.inr he) B A hs)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
