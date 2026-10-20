module

public import PottsContinuity.FKC.Curves.RectanglePathIntersection

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- Two signs with opposite boundary conditions have a common nonpositive
vertex and positive witnesses in the same unit grid cell. The explicit
coordinate bounds permit diagonal neighbours and retain their full displacement. -/
theorem grid_two_signs_balanced_cell (p : ℕ)
    (X Y : (Fin 2 → Fin (p+1)) → Prop)
    (hX0 : ∀ v, v 0 = 0 → ¬X v) (hXp : ∀ v, (v 0).val = p → X v)
    (hY0 : ∀ v, v 1 = 0 → ¬Y v) (hYp : ∀ v, (v 1).val = p → Y v) :
    ∃ v, ¬X v ∧ ¬Y v ∧
      ∃ x, X x ∧ (∀ i : Fin 2, (x i).val ≤ (v i).val+1 ∧ (v i).val ≤ (x i).val+1) ∧
      ∃ y, Y y ∧ (∀ i : Fin 2, (y i).val ≤ (v i).val+1 ∧ (v i).val ≤ (y i).val+1) := by
  classical
  let SC : SpernerCube := {
    n := 2
    p := p
    RL := fun v => if X v then 0 else if Y v then 1 else 2
    rl_proper := by
      intro v
      constructor
      · split_ifs <;> omega
      · intro i
        fin_cases i
        · constructor
          · intro hv
            have hx := hX0 v hv
            simp only [hx,ite_false]
            split_ifs <;> omega
          · intro hv
            have hx := hXp v hv
            simp [hx]
        · constructor
          · intro hv
            have hy := hY0 v hv
            simp only [hy,ite_false]
            split_ifs <;> omega
          · intro hv
            have hy := hYp v hv
            simp only [hy,ite_true]
            split_ifs <;> omega }
  obtain ⟨I,hI⟩ := weaker_cubical_sperner SC
  have hc := (complete_simplex_iff 2 I hI.1).mp hI
  obtain ⟨i0,hi0⟩ := hc 0 (by omega)
  obtain ⟨i1,hi1⟩ := hc 1 (by omega)
  obtain ⟨i2,hi2⟩ := hc 2 (by omega)
  have hlabel (v : Fin 2 → Fin (p+1)) :
      (SC.RL v = 0 ↔ X v) ∧ (SC.RL v = 1 ↔ ¬X v ∧ Y v) ∧
        (SC.RL v = 2 ↔ ¬X v ∧ ¬Y v) := by
    dsimp [SC]
    by_cases hx : X v <;> by_cases hy : Y v <;> simp [hx,hy]
  have hclose (a b : Fin 3) (j : Fin 2) : (I a j).val ≤ (I b j).val+1 := by
    have ha := monotone_1_of_simplex SC I hI.1 a (Fin.last 2) (Fin.le_last a) j
    have hb := monotone_1_of_simplex SC I hI.1 0 b (Fin.zero_le b) j
    have hl := last_of_simplex SC I hI.1 j
    change (I (Fin.last 2) j).val ≤ (I 0 j).val+1 at hl
    change (I a j).val ≤ (I (Fin.last 2) j).val at ha
    change (I 0 j).val ≤ (I b j).val at hb
    omega
  exact ⟨I i2,((hlabel _).2.2.mp hi2).1,((hlabel _).2.2.mp hi2).2,
    I i0,(hlabel _).1.mp hi0,(fun j => ⟨hclose i0 i2 j,hclose i2 i0 j⟩),
    I i1,((hlabel _).2.1.mp hi1).2,(fun j => ⟨hclose i1 i2 j,hclose i2 i1 j⟩)⟩

end
end PottsContinuity.PlanarTopology
