module

public import PottsContinuity.Thm3.RSW.WiredAnnulusLower
public import PottsContinuity.Thm3.RSW.TranslatedAnnulusPositivity

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

private theorem source_inner_box_containment (n : ℕ) (z : LatticeVertex)
    (hc : -5*(n:ℤ) ≤ z.1 ∧ z.1 ≤ 5*n ∧ -5*(n:ℤ) ≤ z.2 ∧ z.2 ≤ 5*n) :
    latticeBox z (2*n) ⊆ latticeBox (0,0) (56*n) := by
  intro v hv
  have hb := (mem_latticeBox z v (2*n)).mp hv
  apply (mem_latticeBox (0,0) v (56*n)).mpr
  simp only [Nat.cast_mul,Nat.cast_ofNat,zero_sub,zero_add] at hb ⊢
  omega

private theorem source_reference_window (n : ℕ) (z : LatticeVertex)
    (hc : -5*(n:ℤ) ≤ z.1 ∧ z.1 ≤ 5*n ∧ -5*(n:ℤ) ≤ z.2 ∧ z.2 ≤ 5*n) :
    ∀ v ∈ box (8*n), (v.1+z.1,v.2+z.2) ∈ box (56*n) := by
  intro v hv
  rw [Foundations.mem_box_iff_interval] at hv ⊢
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hv ⊢
  omega

/-- Every positive source scale has a nonempty actual wired two-annulus
intersection, before any uniform estimate is applied. -/
theorem lemma4_wired_two_annuli_probability_pos (θ : Parameters) (n : ℕ) (hn : 1 ≤ n) :
    0 < finiteBoundaryEventProbability (box (56*n)) θ
      (frozenBoundaryCondition (box (56*n)) 1)
      (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (5*(n:ℤ),0) n ∧
        ω ∈ annulusCircuitEvent (box (56*n)) (-5*(n:ℤ),0) n) := by
  apply finite_annulus_pair_pos_of_reference_containment _ θ _ _ _ n hn
  · exact source_reference_window n (5*(n:ℤ),0) (by dsimp; omega)
  · exact source_reference_window n (-5*(n:ℤ),0) (by dsimp; omega)

/-- The wired lower-bound half of source eq9: both actual source annulus
circuits have a uniform positive probability, with every positive scale
retained. The conditioning-on-the-large-circuit comparison is separate. -/
theorem selfDual_lemma4_wired_two_annuli_lower (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ finiteBoundaryEventProbability (box (56*n)) (selfDualParameters q)
        (frozenBoundaryCondition (box (56*n)) 1)
        (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (5*(n:ℤ),0) n ∧
          ω ∈ annulusCircuitEvent (box (56*n)) (-5*(n:ℤ),0) n) := by
  obtain ⟨a,ha,hbound⟩ := selfDual_finite_wired_annulus_lower_from_two q
  let θ := selfDualParameters q
  let b : ℕ → ℝ := fun n => finiteBoundaryEventProbability (box (56*n)) θ
    (frozenBoundaryCondition (box (56*n)) 1)
    (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (5*(n:ℤ),0) n ∧
      ω ∈ annulusCircuitEvent (box (56*n)) (-5*(n:ℤ),0) n)
  let p₁ := b 1
  have hp₁ : 0 < p₁ := lemma4_wired_two_annuli_probability_pos θ 1 (by norm_num)
  refine ⟨min p₁ (a^2),lt_min hp₁ (sq_pos_of_pos ha),?_⟩
  intro n hn
  by_cases hn₂ : 2 ≤ n
  · let V := box (56*n)
    let ξ := frozenBoundaryCondition V 1
    let E := fun ω => ω ∈ annulusCircuitEvent V (5*(n:ℤ),0) n
    let F := fun ω => ω ∈ annulusCircuitEvent V (-5*(n:ℤ),0) n
    have hplus : a ≤ finiteBoundaryEventProbability V θ ξ E :=
      hbound n (56*n) (5*(n:ℤ),0) hn₂
        (source_inner_box_containment n _ (by dsimp; omega))
    have hminus : a ≤ finiteBoundaryEventProbability V θ ξ F :=
      hbound n (56*n) (-5*(n:ℤ),0) hn₂
        (source_inner_box_containment n _ (by dsimp; omega))
    have hprod := mul_le_mul hplus hminus ha.le
      (ENNReal.toReal_nonneg : 0 ≤ finiteBoundaryEventProbability V θ ξ E)
    have hfkg := finiteBoundaryEventProbability_fkg V θ ξ E F
      (annulusCircuitEvent_isUpperSet V _ n) (annulusCircuitEvent_isUpperSet V _ n)
    apply (min_le_right p₁ (a^2)).trans
    exact (show a^2 ≤ _ by simpa only [pow_two] using hprod).trans hfkg
  · have hn₁ : n = 1 := by omega
    subst n
    exact min_le_left p₁ (a^2)

end
end PottsContinuity.RSW
