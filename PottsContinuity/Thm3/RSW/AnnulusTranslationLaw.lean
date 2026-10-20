module

public import PottsContinuity.Thm3.RSW.AnnulusTranslation
public import PottsContinuity.PD.FK.BoxLimits
public import PottsContinuity.Foundations.Bridges

/-! # Exact translated finite free annulus probabilities, every real q≥1 -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- A translated graph isomorphism preserves the exact annulus probability.
The entire sampled finite law, polygon and Jordan interior are transported. -/
theorem finite_free_annulus_probability_translation
    (U V : Finset (ℤ × ℤ))
    (e : (squareLattice.induce (U : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (V : Set (ℤ × ℤ)))
    (θ : Parameters) (c : ℤ × ℤ)
    (hpos : ∀ u, (e u).val = FKC.latticeTranslate c u.val) (z : ℤ × ℤ) (n : ℕ) :
    finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
      (fun ω => ω ∈ annulusCircuitEvent V (FKC.latticeTranslate c z) n) =
    finiteBoundaryEventProbability U θ (frozenBoundaryCondition U 0)
      (fun ω => ω ∈ annulusCircuitEvent U z n) := by
  have hprob := finite_free_probability_iso U V e θ
    (fun ω => ω ∈ annulusCircuitEvent V (FKC.latticeTranslate c z) n)
  have hevent : (fun ω => finiteBoolIso U V e ω ∈
      annulusCircuitEvent V (FKC.latticeTranslate c z) n) =
      (fun ω => ω ∈ annulusCircuitEvent U z n) := by
    funext ω
    apply propext
    exact annulusCircuit_translate_iff_openIso U V ω (finiteBoolIso U V e ω) c
      (finiteBoolOpenIso U V e ω) hpos z n
  rw [hevent] at hprob
  exact hprob

/-- The literal free annulus law in a translated radius-Rn box equals a_n.
No translation invariance of a fixed ambient box is asserted. -/
theorem translated_box_annulus_probability_eq (θ : Parameters) (c : ℤ × ℤ) (R n : ℕ) :
    finiteBoundaryEventProbability (latticeBox c (R*n)) θ
      (frozenBoundaryCondition (latticeBox c (R*n)) 0)
      (fun ω => ω ∈ annulusCircuitEvent (latticeBox c (R*n)) c n) =
        annulusProbability θ R n := by
  have h := finite_free_annulus_probability_translation
    (latticeBox (0,0) (R*n)) (latticeBox (latticeTranslate c (0,0)) (R*n))
    (boxVertexTranslationIso c (0,0) (R*n)) θ c (fun _ => rfl) (0,0) n
  have hc : FKC.latticeTranslate c (0,0) = c := by
    ext <;> simp [FKC.latticeTranslate]
  have hc' : latticeTranslate c (0,0) = c := hc
  rw [hc,hc',latticeBox_origin_eq_box] at h
  exact h

end
end PottsContinuity.RSW
