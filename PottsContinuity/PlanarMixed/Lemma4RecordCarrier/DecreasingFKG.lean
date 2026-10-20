module

public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Decreasing events are positively correlated in the same finite FK law. -/
theorem finiteLaw_lower_event_association {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    (S T : Set (Configuration G)) (hS : IsLowerSet S) (hT : IsLowerSet T) :
    (measure G θ ξ S).toReal * (measure G θ ξ T).toReal ≤
      (measure G θ ξ (S ∩ T)).toReal := by
  have h := measure_positive_association θ ξ Sᶜ Tᶜ hS.compl hT.compl
  have hmS : MeasurableSet S := MeasurableSpace.measurableSet_top
  have hmT : MeasurableSet T := MeasurableSpace.measurableSet_top
  have hmU : MeasurableSet (S ∪ T) := MeasurableSpace.measurableSet_top
  change (measure G θ ξ).real Sᶜ * (measure G θ ξ).real Tᶜ ≤
    (measure G θ ξ).real (Sᶜ ∩ Tᶜ) at h
  rw [← Set.compl_union,probReal_compl_eq_one_sub hmS,
    probReal_compl_eq_one_sub hmT,probReal_compl_eq_one_sub hmU] at h
  have hu := measureReal_union_add_inter (μ := measure G θ ξ) hmT
    (measure_ne_top _ S) (measure_ne_top _ T)
  change (measure G θ ξ).real S * (measure G θ ξ).real T ≤
    (measure G θ ξ).real (S ∩ T)
  nlinarith

/-- All factors are taken in one native FK law; no independence is needed. -/
theorem finiteLaw_lower_event_product {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    {ι : Type*} (s : Finset ι) (E : ι → Set (Configuration G))
    (hE : ∀ j ∈ s, IsLowerSet (E j)) :
    (∏ j ∈ s, (measure G θ ξ (E j)).toReal) ≤
      (measure G θ ξ {A | ∀ j ∈ s, A ∈ E j}).toReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
    have hs := ih (fun k hk => hE k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert hjs]
    calc
      _ ≤ (measure G θ ξ (E j)).toReal *
          (measure G θ ξ {A | ∀ k ∈ s, A ∈ E k}).toReal :=
        mul_le_mul_of_nonneg_left hs ENNReal.toReal_nonneg
      _ ≤ (measure G θ ξ (E j ∩ {A | ∀ k ∈ s, A ∈ E k})).toReal :=
        finiteLaw_lower_event_association G θ ξ _ _
          (hE j (Finset.mem_insert_self _ _))
          (fun _ _ h hA k hk => hE k (Finset.mem_insert_of_mem hk) h (hA k hk))
      _ = _ := by
        apply congrArg (fun S => (measure G θ ξ S).toReal)
        ext A
        simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Finset.mem_insert,forall_eq_or_imp]

/-- Uniform decreasing-event bounds multiply with the exact cubic factor. -/
theorem finiteLaw_three_lower_events_of_local_bounds {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    (E : Fin 3 → Set (Configuration G)) (hE : ∀ j, IsLowerSet (E j))
    (c : ℝ) (hc : 0 ≤ c)
    (hlocal : ∀ j, c ≤ (measure G θ ξ (E j)).toReal) :
    c^3 ≤ (measure G θ ξ {A | ∀ j, A ∈ E j}).toReal := by
  have h := finiteLaw_lower_event_product G θ ξ Finset.univ E (fun j _ => hE j)
  have hp : c^3 ≤ ∏ j : Fin 3, (measure G θ ξ (E j)).toReal := by
    calc
      _ = ∏ _j : Fin 3, c := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc) (fun j _ => hlocal j)
  exact hp.trans (by simpa only [Finset.mem_univ,forall_const] using h)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
