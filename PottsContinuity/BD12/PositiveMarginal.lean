module

public import PottsContinuity.BD12.FinitePinnedAssociation
public import Mathlib.Data.Finset.Sum

/-! A true marginal of a positive Boolean-cube weight. Summation over the
entire complementary cube preserves log-supermodularity by Four Functions.
This is the inner-edge marginal needed for the DRT shell exploration; no
outside configuration is fixed. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped BigOperators
noncomputable section
variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

/-- Unnormalised marginal weight on the left coordinates. -/
def finiteLeftMarginalWeight (w : Finset (E ⊕ F) → Set.Ioi (0 : ℝ))
    (A : Finset E) : Set.Ioi (0 : ℝ) :=
  ⟨∑ D : Finset F, (w (A.disjSum D) : ℝ),
    by
      change 0 < ∑ D : Finset F, (w (A.disjSum D) : ℝ)
      exact Finset.sum_pos' (fun D _ => (w (A.disjSum D)).property.le)
        ⟨∅, Finset.mem_univ _, (w (A.disjSum ∅)).property⟩⟩

omit [Fintype E] [Fintype F] in
theorem finite_disjSum_inter (A B : Finset E) (C D : Finset F) :
    (A.disjSum C) ∩ (B.disjSum D) = (A ∩ B).disjSum (C ∩ D) := by
  ext x
  cases x <;> simp

omit [Fintype E] [Fintype F] in
theorem finite_disjSum_union (A B : Finset E) (C D : Finset F) :
    (A.disjSum C) ∪ (B.disjSum D) = (A ∪ B).disjSum (C ∪ D) := by
  ext x
  cases x <;> simp

omit [Fintype E] in
/-- Marginalisation preserves the finite FKG lattice condition. -/
theorem finiteLeftMarginalWeight_lattice_condition
    (w : Finset (E ⊕ F) → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (A B : Finset E) :
    (finiteLeftMarginalWeight w A : ℝ) * finiteLeftMarginalWeight w B ≤
      (finiteLeftMarginalWeight w (A ∩ B) : ℝ) * finiteLeftMarginalWeight w (A ∪ B) := by
  apply four_functions_theorem_univ
    (fun C : Finset F => (w (A.disjSum C) : ℝ))
    (fun C : Finset F => (w (B.disjSum C) : ℝ))
    (fun C : Finset F => (w ((A ∩ B).disjSum C) : ℝ))
    (fun C : Finset F => (w ((A ∪ B).disjSum C) : ℝ))
    (fun C => (w _).property.le) (fun C => (w _).property.le)
    (fun C => (w _).property.le) (fun C => (w _).property.le)
  intro C D
  simpa only [Finset.inf_eq_inter, Finset.sup_eq_union, finite_disjSum_inter,
    finite_disjSum_union] using hw (A.disjSum C) (B.disjSum D)

omit [DecidableEq E] [DecidableEq F] in
/-- Summing over the two coordinate cubes is exactly summing over the full cube. -/
theorem finite_sum_disjSum (g : Finset (E ⊕ F) → ℝ) :
    (∑ A : Finset E, ∑ D : Finset F, g (A.disjSum D)) = ∑ C, g C := by
  calc
    _ = ∑ p : Finset E × Finset F, g (p.1.disjSum p.2) :=
      (Fintype.sum_prod_type (fun p : Finset E × Finset F => g (p.1.disjSum p.2))).symm
    _ = _ := Fintype.sum_equiv (Finset.sumEquiv.toEquiv.symm) _ _ (fun _ => rfl)


/-- Every observable of the retained coordinates has its actual outer-law mean. -/
theorem finiteLeftMarginalWeight_mean
    (w : Finset (E ⊕ F) → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) :
    finitePinnedMean (finiteLeftMarginalWeight w) ∅ ∅ f =
      finitePinnedMean w ∅ ∅ (fun C => f C.toLeft) := by
  simp only [finitePinnedMean, finitePinnedWeight, Finset.inter_empty, ite_true]
  change ((∑ A : Finset E, (∑ D : Finset F, (w (A.disjSum D) : ℝ)) * f A) /
    ∑ A : Finset E, ∑ D : Finset F, (w (A.disjSum D) : ℝ)) = _
  simp_rw [Finset.sum_mul]
  rw [finite_sum_disjSum (fun C => (w C : ℝ))]
  congr 1
  simpa only [Finset.toLeft_disjSum] using
    finite_sum_disjSum (fun C => (w C : ℝ) * f C.toLeft)

end
end PottsContinuity.BD12
