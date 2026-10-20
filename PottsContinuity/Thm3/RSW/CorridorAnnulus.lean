module

public import PottsContinuity.Thm3.RSW.BoxCorridors
public import PottsContinuity.Thm3.RSW.AnnulusCircuit
public import PottsContinuity.Thm3.RSW.Prop3Conditional

/-!
# A power-112 annulus bound conditional only on circuit extraction

Every probabilistic and translated-domain step is proved. The sole premise
is the q-independent extraction of a genuine surrounding simple circuit from
four actual corridor crossings.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Four actual corridors imply the power-112 bound after finite FKG. The
only conditional input is deterministic circuit extraction, with all paths
and the actual Jordan-polygon target visible. -/
theorem squarePair_pow_oneHundredTwelve_le_annulus_of_fourCorridorCircuit
    (θ : Parameters) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmn : m < n) (hnm : n ≤ 7*m) (i j : Fin (m+1))
    (hfourCorridorCircuit : ∀ ω,
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ)) ω →
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1) ω →
      finiteVerticalCrossing (box (8*n)) (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1)
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      finiteVerticalCrossing (box (8*n)) ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ))
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      ω ∈ annulusCircuitEvent (box (8*n)) (0,0) n) :
    (squarePairProbability θ m i j)^112 ≤ annulusProbability θ 8 n := by
  let V := box (8*n)
  let ξ := frozenBoundaryCondition V 0
  let T := horizontalCrossing V (-2*(n:ℤ)) (2*(n:ℤ)) ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ))
  let B := horizontalCrossing V (-2*(n:ℤ)) (2*(n:ℤ)) (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1)
  let L := finiteVerticalCrossing V (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1) (-2*(n:ℤ)) (2*(n:ℤ))
  let R := finiteVerticalCrossing V ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ)) (-2*(n:ℤ)) (2*(n:ℤ))
  let p := squarePairProbability θ m i j
  have hnR : (1:ℤ) ≤ n := by exact_mod_cast hn
  have hmR : (m:ℤ) < n := by exact_mod_cast hmn
  have hT : p^28 ≤ finiteBoundaryEventProbability V θ ξ T :=
    squarePair_pow_twentyEight_le_box_corridor θ n m hn hm hmn hnm i j ((n:ℤ)+1)
      (by omega) (by omega)
  have hB : p^28 ≤ finiteBoundaryEventProbability V θ ξ B := by
    have h := squarePair_pow_twentyEight_le_box_corridor θ n m hn hm hmn hnm i j
      (-(n:ℤ)-1-(m:ℤ)) (by omega) (by omega)
    have hend : -(n:ℤ)-1-(m:ℤ)+(m:ℤ) = -(n:ℤ)-1 := by omega
    rw [hend] at h
    exact h
  have hL : p^28 ≤ finiteBoundaryEventProbability V θ ξ L := by
    have h := squarePair_pow_twentyEight_le_box_vertical_corridor θ n m hn hm hmn hnm i j
      (-(n:ℤ)-1-(m:ℤ)) (by omega) (by omega)
    have hend : -(n:ℤ)-1-(m:ℤ)+(m:ℤ) = -(n:ℤ)-1 := by omega
    rw [hend] at h
    exact h
  have hR : p^28 ≤ finiteBoundaryEventProbability V θ ξ R :=
    squarePair_pow_twentyEight_le_box_vertical_corridor θ n m hn hm hmn hnm i j ((n:ℤ)+1)
      (by omega) (by omega)
  have hTu : IsUpperSet {ω | T ω} := horizontalCrossing_isUpperSet _ _ _ _ _
  have hBu : IsUpperSet {ω | B ω} := horizontalCrossing_isUpperSet _ _ _ _ _
  have hLu : IsUpperSet {ω | L ω} := finiteVerticalCrossing_isUpperSet _ _ _ _ _
  have hRu : IsUpperSet {ω | R ω} := finiteVerticalCrossing_isUpperSet _ _ _ _ _
  have hTB : p^56 ≤ finiteBoundaryEventProbability V θ ξ (fun ω => T ω ∧ B ω) := by
    calc
      p^56 = p^28*p^28 := by ring
      _ ≤ finiteBoundaryEventProbability V θ ξ T * finiteBoundaryEventProbability V θ ξ B :=
        mul_le_mul hT hB (pow_nonneg (squarePairProbability_nonneg θ m i j) _) ENNReal.toReal_nonneg
      _ ≤ _ := finiteBoundaryEventProbability_fkg V θ ξ T B hTu hBu
  have hLR : p^56 ≤ finiteBoundaryEventProbability V θ ξ (fun ω => L ω ∧ R ω) := by
    calc
      p^56 = p^28*p^28 := by ring
      _ ≤ finiteBoundaryEventProbability V θ ξ L * finiteBoundaryEventProbability V θ ξ R :=
        mul_le_mul hL hR (pow_nonneg (squarePairProbability_nonneg θ m i j) _) ENNReal.toReal_nonneg
      _ ≤ _ := finiteBoundaryEventProbability_fkg V θ ξ L R hLu hRu
  calc
    p^112 = p^56*p^56 := by ring
    _ ≤ finiteBoundaryEventProbability V θ ξ (fun ω => T ω ∧ B ω) *
        finiteBoundaryEventProbability V θ ξ (fun ω => L ω ∧ R ω) :=
      mul_le_mul hTB hLR (pow_nonneg (squarePairProbability_nonneg θ m i j) _) ENNReal.toReal_nonneg
    _ ≤ finiteBoundaryEventProbability V θ ξ (fun ω => (T ω ∧ B ω) ∧ (L ω ∧ R ω)) :=
      finiteBoundaryEventProbability_fkg V θ ξ _ _
        (fun _ _ h hω => ⟨hTu h hω.1,hBu h hω.2⟩)
        (fun _ _ h hω => ⟨hLu h hω.1,hRu h hω.2⟩)
    _ ≤ annulusProbability θ 8 n := measureReal_mono
      (fun _ h => hfourCorridorCircuit _ h.1.1 h.1.2 h.2.1 h.2.2)

/-- The same bound for the genuine nonempty finite maximum over all source
endpoint pairs, again conditional only on deterministic circuit extraction. -/
theorem maxSquarePair_pow_oneHundredTwelve_le_annulus_of_fourCorridorCircuit
    (θ : Parameters) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmn : m < n) (hnm : n ≤ 7*m)
    (hfourCorridorCircuit : ∀ ω,
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ)) ω →
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1) ω →
      finiteVerticalCrossing (box (8*n)) (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1)
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      finiteVerticalCrossing (box (8*n)) ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ))
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      ω ∈ annulusCircuitEvent (box (8*n)) (0,0) n) :
    (maxSquarePairProbability θ m)^112 ≤ annulusProbability θ 8 n := by
  classical
  obtain ⟨ij,_,heq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin (m+1) × Fin (m+1)))) Finset.univ_nonempty
    (fun ij => squarePairProbability θ m ij.1 ij.2)
  unfold maxSquarePairProbability
  rw [heq]
  exact squarePair_pow_oneHundredTwelve_le_annulus_of_fourCorridorCircuit
    θ n m hn hm hmn hnm ij.1 ij.2 hfourCorridorCircuit

end
end PottsContinuity.RSW
