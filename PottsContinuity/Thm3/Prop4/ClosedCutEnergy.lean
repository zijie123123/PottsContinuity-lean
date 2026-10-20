module

public import PottsContinuity.PD.FK.FiniteEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Uniform conditional closing of a finite cut

The strip side-independence argument needs a closed cut with a positive
probability uniform in all previously exposed exterior states. This lemma
uses the actual finite FK law and edge-stable events, without independence.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance closedCutEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance closedCutEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Uniform one-edge closing bound, indexed by an actual original edge. -/
theorem finite_closed_edge_energy (θ : Parameters) (ξ : BoundaryCondition V)
    (e : G.edgeSet) (B : Set (Configuration G))
    (hstable : ∀ A, A ∈ B ↔ A.erase e ∈ B) :
    (1-edgeParameter θ)*(measure G θ ξ B).toReal ≤
      (measure G θ ξ (B ∩ {A | e ∉ A})).toReal := by
  classical
  let p := e.val.out
  have hrepr : s(p.1,p.2) = e.val := Quot.out_eq _
  have hadj : G.Adj p.1 p.2 := G.mem_edgeSet.mp (by rw [hrepr]; exact e.property)
  have heq : (⟨s(p.1,p.2),G.mem_edgeSet.mpr hadj⟩ : G.edgeSet) = e := Subtype.ext hrepr
  have h := (configurationProbability_edge_finite_energy_closed θ ξ B hadj
    (by simpa only [heq] using hstable)).1
  simpa only [heq] using h

/-- Close every edge of a finite cut while retaining any event determined by
other edges. The lower bound is uniform in the event and boundary partition. -/
theorem finite_closed_cut_energy (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) (B : Set (Configuration G))
    (hstable : ∀ e ∈ F, ∀ A, A ∈ B ↔ A.erase e ∈ B) :
    (1-edgeParameter θ)^F.card*(measure G θ ξ B).toReal ≤
      (measure G θ ξ (B ∩ {A | Disjoint A F})).toReal := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert e F he ih =>
    have hF : ∀ f ∈ F, ∀ A, A ∈ B ↔ A.erase f ∈ B := fun f hf =>
      hstable f (Finset.mem_insert_of_mem hf)
    have hprev := ih hF
    have hdisj (A : Configuration G) : Disjoint A F ↔ Disjoint (A.erase e) F := by
      constructor
      · intro h
        exact h.mono_left (Finset.erase_subset e A)
      · intro h
        apply Finset.disjoint_left.mpr
        intro f hfA hfF
        have hfe : f ≠ e := by intro hfe; subst f; exact he hfF
        exact (Finset.disjoint_left.mp h) (Finset.mem_erase.mpr ⟨hfe,hfA⟩) hfF
    have hnext := finite_closed_edge_energy G θ ξ e (B ∩ {A | Disjoint A F}) (by
      intro A
      exact and_congr (hstable e (Finset.mem_insert_self e F) A) (hdisj A))
    have hsets : (B ∩ {A | Disjoint A F}) ∩ {A | e ∉ A} =
        B ∩ {A | Disjoint A (insert e F)} := by
      ext A
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Finset.disjoint_insert_right]
      tauto
    rw [hsets] at hnext
    calc
      _ = (1-edgeParameter θ)*((1-edgeParameter θ)^F.card*(measure G θ ξ B).toReal) := by
        rw [Finset.card_insert_of_notMem he]
        ring
      _ ≤ (1-edgeParameter θ)*(measure G θ ξ (B ∩ {A | Disjoint A F})).toReal :=
        mul_le_mul_of_nonneg_left hprev (one_sub_edgeParameter_pos θ).le
      _ ≤ _ := hnext

end

end PottsContinuity.Thm3.Prop4
