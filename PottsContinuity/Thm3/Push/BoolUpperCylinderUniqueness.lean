module

public import PottsContinuity.PD.Infra.CylinderUniqueness
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open MeasureTheory Topology

/-- A constant finite Boolean pattern is a clopen original-coordinate event. -/
theorem boolConstantCylinder_isClopen {ι : Type*} (A : Finset ι) (b : Bool) :
    IsClopen {ω : ι → Bool | ∀ e ∈ A, ω e = b} := by
  have hset : {ω : ι → Bool | ∀ e ∈ A, ω e = b} = ⋂ e ∈ A, {ω | ω e = b} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
  rw [hset]
  exact isClopen_biInter_finset fun e _ =>
    (isClopen_discrete ({b} : Set Bool)).preimage (continuous_apply e)

/-- Finite Boolean product measures are determined by their increasing
all-open cylinders. Closed coordinates are recovered by finite disjoint splitting. -/
theorem finite_bool_measure_eq_of_upper_cylinders {ι : Type*}
    (μ ν : Measure (ι → Bool)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ A : Finset ι, μ.real {ω | ∀ e ∈ A, ω e = true} =
      ν.real {ω | ∀ e ∈ A, ω e = true}) : μ = ν := by
  classical
  let E (Q R : Finset ι) : Set (ι → Bool) :=
    {ω | (∀ e ∈ Q, ω e = true) ∧ ∀ e ∈ R, ω e = false}
  have hmeas (Q R : Finset ι) : MeasurableSet (E Q R) := by
    change MeasurableSet ({ω : ι → Bool | ∀ e ∈ Q, ω e = true} ∩
      {ω : ι → Bool | ∀ e ∈ R, ω e = false})
    have hconst (A : Finset ι) (b : Bool) :
        MeasurableSet {ω : ι → Bool | ∀ e ∈ A, ω e = b} := by
      have hs : {ω : ι → Bool | ∀ e ∈ A, ω e = b} = ⋂ e ∈ A, {ω | ω e = b} := by
        ext ω
        simp only [Set.mem_ofPred_eq,Set.mem_iInter]
      rw [hs]
      exact MeasurableSet.biInter A.countable_toSet fun e _ =>
        measurableSet_eq_fun (measurable_pi_apply e) measurable_const
    exact (hconst Q true).inter (hconst R false)
  have hall : ∀ R Q : Finset ι, μ.real (E Q R) = ν.real (E Q R) := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro Q
      simpa [E] using h Q
    | @insert e R he ih =>
      intro Q
      have hsplit : E Q R = E (insert e Q) R ∪ E Q (insert e R) := by
        ext ω
        constructor
        · rintro ⟨hQ,hR⟩
          cases hb : ω e with
          | false =>
            apply Or.inr
            refine ⟨hQ,?_⟩
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hb
            · exact hR i hi
          | true =>
            apply Or.inl
            refine ⟨?_,hR⟩
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hb
            · exact hQ i hi
        · rintro (⟨hQ,hR⟩ | ⟨hQ,hR⟩)
          · exact ⟨fun i hi => hQ i (Finset.mem_insert_of_mem hi),hR⟩
          · exact ⟨hQ,fun i hi => hR i (Finset.mem_insert_of_mem hi)⟩
      have hd : Disjoint (E (insert e Q) R) (E Q (insert e R)) := by
        apply Set.disjoint_left.mpr
        intro ω h₁ h₂
        have ht := h₁.1 e (Finset.mem_insert_self e Q)
        have hf := h₂.2 e (Finset.mem_insert_self e R)
        exact Bool.noConfusion (ht.symm.trans hf)
      have hμ : μ.real (E Q R) = μ.real (E (insert e Q) R) + μ.real (E Q (insert e R)) := by
        rw [hsplit,measureReal_union hd (hmeas Q (insert e R))]
      have hν : ν.real (E Q R) = ν.real (E (insert e Q) R) + ν.real (E Q (insert e R)) := by
        rw [hsplit,measureReal_union hd (hmeas Q (insert e R))]
      linarith only [hμ,hν,ih Q,ih (insert e Q)]
  apply PD.ext_of_cylinders μ ν (fun _ => true)
  intro A ξ
  let Q := A.filter fun e => ξ e = true
  let R := A.filter fun e => ξ e = false
  have hpattern : {ω : ι → Bool | ∀ e ∈ A, ω e = ξ e} = E Q R := by
    ext ω
    constructor
    · intro hω
      constructor
      · intro e he
        obtain ⟨heA,heξ⟩ := Finset.mem_filter.mp he
        exact (hω e heA).trans heξ
      · intro e he
        obtain ⟨heA,heξ⟩ := Finset.mem_filter.mp he
        exact (hω e heA).trans heξ
    · rintro ⟨hQ,hR⟩ e he
      cases hb : ξ e with
      | false => simpa only [hb] using hR e (Finset.mem_filter.mpr ⟨he,hb⟩)
      | true => simpa only [hb] using hQ e (Finset.mem_filter.mpr ⟨he,hb⟩)
  have hreal := hall R Q
  rw [← hpattern] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end PottsContinuity.Push
