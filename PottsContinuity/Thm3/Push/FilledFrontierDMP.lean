module

public import PottsContinuity.Thm3.Push.RectangleFilledFrontier
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
local instance filledRevealPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance filledRevealEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance filledRevealRemainingFintype (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) :
    Fintype (RemainingConfiguration (rectangleGraph a w h) R) := Fintype.ofFinite _

/-- All original bonds incident, through the actual dual edge bijection, to
an auxiliary region. This also records closed original bonds inside it. -/
def auxiliaryRegionReveal {V W : Type*} [Finite V]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G.edgeSet ≃ H.edgeSet)
    (S : Set W) : Configuration G := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact Finset.univ.filter fun f => ∃ v ∈ (e f).val, v ∈ S

@[simp] theorem mem_auxiliaryRegionReveal {V W : Type*} [Finite V]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G.edgeSet ≃ H.edgeSet)
    (S : Set W) (f : G.edgeSet) :
    f ∈ auxiliaryRegionReveal e S ↔ ∃ v ∈ (e f).val, v ∈ S := by
  simp only [auxiliaryRegionReveal, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Reveal the reached upper region AND the filled holes. The remaining
original bonds have both true dual endpoints in the bottom-connected region. -/
def rectangleFilledTopReveal (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Configuration (rectangleGraph a w h) :=
  auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv a w h)
    (rectangleBottomRegion a w h A)ᶜ

theorem rectangleTopReveal_subset_filled (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectangleTopReveal a w h A ⊆ rectangleFilledTopReveal a w h A := by
  intro f hf
  obtain ⟨v,hv,hvs⟩ := (mem_closedClusterReveal_iff_endpoint _ _ A f).mp hf
  apply (mem_auxiliaryRegionReveal _ _ f).mpr
  refine ⟨v,hv,?_⟩
  intro hbot
  exact (outsideSeedRegion_subset_compl _ _ _ hbot) hvs

/-- Enlarging the original stable reveal by filling the record-determined
holes preserves stopping-set locality. No one-sided-stability premise remains. -/
theorem rectangleFilledTopReveal_stable (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (hagree : B ∩ rectangleFilledTopReveal a w h A = A ∩ rectangleFilledTopReveal a w h A) :
    rectangleFilledTopReveal a w h B = rectangleFilledTopReveal a w h A := by
  have hsmall : B ∩ rectangleTopReveal a w h A = A ∩ rectangleTopReveal a w h A := by
    ext f
    have hstate := Finset.ext_iff.mp hagree f
    simp only [Finset.mem_inter] at hstate ⊢
    constructor
    · rintro ⟨hb,hr⟩
      exact ⟨(hstate.mp ⟨hb,rectangleTopReveal_subset_filled a w h A hr⟩).1,hr⟩
    · rintro ⟨ha,hr⟩
      exact ⟨(hstate.mpr ⟨ha,rectangleTopReveal_subset_filled a w h A hr⟩).1,hr⟩
  exact congrArg (fun C => auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv a w h) Cᶜ)
    (rectangleBottomRegion_eq_of_reveal_agreement a w h A B hsmall)

end
end PottsContinuity.Push
