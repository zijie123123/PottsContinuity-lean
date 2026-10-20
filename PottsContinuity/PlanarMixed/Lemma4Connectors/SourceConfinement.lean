module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.PrimalWindow

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW
noncomputable section

def lemma4PrimalNoncrossings (V : Finset (ℤ × ℤ))
    (Ω : Set (V : Set (ℤ × ℤ))) (n : ℕ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | ∀ j : Fin 3, A ∈ primalWindowNoncrossing V Ω
    ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))}

/-- The corrected primal windows confine both entire source cores, once the
original closed trace pair supplies its between-trace component constraint. -/
theorem lemma4_core_rectangles_of_noncrossings_and_strip
    (V : Finset (ℤ × ℤ)) (Ω : Set (V : Set (ℤ × ℤ)))
    (n : ℕ) (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hstrip : ∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set (ℤ × ℤ)),
      ∀ u ∈ vertexBoxRegion V z (2*n), ∀ w, ActualConnected _ A u w →
      w ∈ Ω ∧ -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ))
    (hA : A ∈ lemma4PrimalNoncrossings V Ω n) :
    A ∈ fullCoreConfined V
      {w | -13*(n:ℤ) < w.val.1 ∧ w.val.1 < 3*(n:ℤ) ∧
        -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ)} (-5*(n:ℤ),0) n ∧
    A ∈ fullCoreConfined V
      {w | -3*(n:ℤ) < w.val.1 ∧ w.val.1 < 13*(n:ℤ) ∧
        -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ)} (5*(n:ℤ),0) n := by
  have hcore (z : ℤ × ℤ) (u : (V : Set (ℤ × ℤ)))
      (hu : u ∈ vertexBoxRegion V z (2*n)) :
      z.1-2*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ z.1+2*(n:ℤ) := by
    change max |u.val.1-z.1| |u.val.2-z.2| ≤ ((2*n:ℕ):ℤ) at hu
    have h := le_trans (le_max_left _ _) hu
    rw [abs_le] at h
    push_cast at h
    omega
  constructor
  · apply fullCoreConfined_of_strip_and_two_noncrossings V Ω A (-5*(n:ℤ),0) n
      (-13*(n:ℤ)) (-7*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))
      (by omega) (by omega)
    · intro u hu
      have := hcore (-5*(n:ℤ),0) u hu
      dsimp at this
      omega
    · exact hstrip _ (by simp)
    · simpa using hA 0
    · simpa using hA 1
  · apply fullCoreConfined_of_strip_and_two_noncrossings V Ω A (5*(n:ℤ),0) n
      (-3*(n:ℤ)) (3*(n:ℤ)) (7*(n:ℤ)) (13*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))
      (by omega) (by omega)
    · intro u hu
      have := hcore (5*(n:ℤ),0) u hu
      dsimp at this
      omega
    · exact hstrip _ (by simp)
    · simpa using hA 1
    · simpa using hA 2

/-- Both strict trapping rectangles lie inside the original radius-eight boxes. -/
theorem lemma4_confined_boxes_of_noncrossings_and_strip
    (V : Finset (ℤ × ℤ)) (Ω : Set (V : Set (ℤ × ℤ)))
    (n : ℕ) (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hstrip : ∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set (ℤ × ℤ)),
      ∀ u ∈ vertexBoxRegion V z (2*n), ∀ w, ActualConnected _ A u w →
      w ∈ Ω ∧ -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ))
    (hA : A ∈ lemma4PrimalNoncrossings V Ω n) :
    A ∈ fullCoreConfined V (finiteVertexRegion (latticeBox (-5*(n:ℤ),0) (8*n)) V) (-5*(n:ℤ),0) n ∧
    A ∈ fullCoreConfined V (finiteVertexRegion (latticeBox (5*(n:ℤ),0) (8*n)) V) (5*(n:ℤ),0) n := by
  obtain ⟨hleft,hright⟩ := lemma4_core_rectangles_of_noncrossings_and_strip V Ω n A hstrip hA
  constructor
  · intro u hu w huw
    have h := hleft u hu w huw
    change -13*(n:ℤ) < w.val.1 ∧ w.val.1 < 3*(n:ℤ) ∧ -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ) at h
    change w.val ∈ latticeBox (-5*(n:ℤ),0) (8*n)
    rw [mem_latticeBox]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    omega
  · intro u hu w huw
    have h := hright u hu w huw
    change -3*(n:ℤ) < w.val.1 ∧ w.val.1 < 13*(n:ℤ) ∧ -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ) at h
    change w.val ∈ latticeBox (5*(n:ℤ),0) (8*n)
    rw [mem_latticeBox]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    omega

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
