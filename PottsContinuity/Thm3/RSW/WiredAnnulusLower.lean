module

public import PottsContinuity.Thm3.RSW.WiredCorridorLower
public import PottsContinuity.Thm3.RSW.FourCorridorCentered

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

private theorem rectangle_in_centered_box (a z : LatticeVertex) (w h R : ℕ)
    (hx₀ : z.1-R ≤ a.1) (hx₁ : a.1+w ≤ z.1+R)
    (hy₀ : z.2-R ≤ a.2) (hy₁ : a.2+h ≤ z.2+R) :
    PD.FK.latticeRectangle a w h ⊆ latticeBox z R := by
  intro v hv
  have hv' := (mem_latticeRectangle a v w h).mp hv
  apply (mem_latticeBox z v R).mpr
  exact ⟨⟨hx₀.trans hv'.1.1,hv'.1.2.trans hx₁⟩,
    ⟨hy₀.trans hv'.2.1,hv'.2.2.trans hy₁⟩⟩

/-- Uniform wired probability of the genuine strict annulus circuit, at every
scale at least two and every translated center whose outer box is sampled. -/
theorem selfDual_finite_wired_annulus_lower_from_two (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n N : ℕ) (z : LatticeVertex), 2 ≤ n →
      latticeBox z (2*n) ⊆ latticeBox (0,0) N →
      c ≤ finiteBoundaryEventProbability (box N) (selfDualParameters q)
        (frozenBoundaryCondition (box N) 1)
        (fun ω => ω ∈ annulusCircuitEvent (box N) z n) := by
  obtain ⟨p,hp,hH,hV⟩ := selfDual_finite_wired_corridor_lower q 9 (by norm_num)
  refine ⟨p^4,pow_pos hp _,?_⟩
  intro n N z hn houter
  let m := n-1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmn : m < n := by dsimp [m]; omega
  have hnm : n = m+1 := by dsimp [m]; omega
  have hnmZ : (n:ℤ) = (m:ℤ)+1 := by exact_mod_cast hnm
  have hnmR : (n:ℝ) = (m:ℝ)+1 := by exact_mod_cast hnm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have haspect : (4*n:ℕ) < (9:ℝ)*m := by push_cast; linarith
  let θ := selfDualParameters q
  let ξ := frozenBoundaryCondition (box N) 1
  let T := horizontalCrossing (box N) (z.1-2*n) (z.1+2*n) (z.2+n+1) (z.2+n+1+m)
  let B := horizontalCrossing (box N) (z.1-2*n) (z.1+2*n) (z.2-n-1-m) (z.2-n-1)
  let L := finiteVerticalCrossing (box N) (z.1-n-1-m) (z.1-n-1) (z.2-2*n) (z.2+2*n)
  let R := finiteVerticalCrossing (box N) (z.1+n+1) (z.1+n+1+m) (z.2-2*n) (z.2+2*n)
  have hfitT : PD.FK.latticeRectangle (z.1-2*n,z.2+n+1) (4*n) m ⊆ latticeBox (0,0) N := by
    apply (rectangle_in_centered_box _ z (4*n) m (2*n) ?_ ?_ ?_ ?_).trans houter
    all_goals simp only [Nat.cast_mul,Nat.cast_ofNat]; omega
  have hfitB : PD.FK.latticeRectangle (z.1-2*n,z.2-n-1-m) (4*n) m ⊆ latticeBox (0,0) N := by
    apply (rectangle_in_centered_box _ z (4*n) m (2*n) ?_ ?_ ?_ ?_).trans houter
    all_goals simp only [Nat.cast_mul,Nat.cast_ofNat]; omega
  have hfitL : PD.FK.latticeRectangle (z.1-n-1-m,z.2-2*n) m (4*n) ⊆ latticeBox (0,0) N := by
    apply (rectangle_in_centered_box _ z m (4*n) (2*n) ?_ ?_ ?_ ?_).trans houter
    all_goals simp only [Nat.cast_mul,Nat.cast_ofNat]; omega
  have hfitR : PD.FK.latticeRectangle (z.1+n+1,z.2-2*n) m (4*n) ⊆ latticeBox (0,0) N := by
    apply (rectangle_in_centered_box _ z m (4*n) (2*n) ?_ ?_ ?_ ?_).trans houter
    all_goals simp only [Nat.cast_mul,Nat.cast_ofNat]; omega
  have hx : z.1-2*(n:ℤ)+(4*n:ℕ) = z.1+2*n := by push_cast; ring
  have hy : z.2-2*(n:ℤ)+(4*n:ℕ) = z.2+2*n := by push_cast; ring
  have hb : z.2-(n:ℤ)-1-m+(m:ℕ) = z.2-n-1 := by omega
  have hl : z.1-(n:ℤ)-1-m+(m:ℕ) = z.1-n-1 := by omega
  have hT : p ≤ finiteBoundaryEventProbability (box N) θ ξ T := by
    have h := hH (z.1-2*n,z.2+n+1) (4*n) m N (by omega) haspect hfitT
    simpa only [Prod.fst,Prod.snd,hx] using h
  have hB : p ≤ finiteBoundaryEventProbability (box N) θ ξ B := by
    have h := hH (z.1-2*n,z.2-n-1-m) (4*n) m N (by omega) haspect hfitB
    simpa only [Prod.fst,Prod.snd,hx,hb] using h
  have hL : p ≤ finiteBoundaryEventProbability (box N) θ ξ L := by
    have h := hV (z.1-n-1-m,z.2-2*n) m (4*n) N (by omega) haspect hfitL
    simpa only [Prod.fst,Prod.snd,hy,hl] using h
  have hR : p ≤ finiteBoundaryEventProbability (box N) θ ξ R := by
    have h := hV (z.1+n+1,z.2-2*n) m (4*n) N (by omega) haspect hfitR
    simpa only [Prod.fst,Prod.snd,hy] using h
  have hTu : IsUpperSet {ω | T ω} := horizontalCrossing_isUpperSet _ _ _ _ _
  have hBu : IsUpperSet {ω | B ω} := horizontalCrossing_isUpperSet _ _ _ _ _
  have hLu : IsUpperSet {ω | L ω} := finiteVerticalCrossing_isUpperSet _ _ _ _ _
  have hRu : IsUpperSet {ω | R ω} := finiteVerticalCrossing_isUpperSet _ _ _ _ _
  have hTB : p^2 ≤ finiteBoundaryEventProbability (box N) θ ξ (fun ω => T ω ∧ B ω) := by
    calc
      p^2 = p*p := by ring
      _ ≤ finiteBoundaryEventProbability (box N) θ ξ T * finiteBoundaryEventProbability (box N) θ ξ B :=
        mul_le_mul hT hB hp.le ENNReal.toReal_nonneg
      _ ≤ _ := finiteBoundaryEventProbability_fkg _ θ ξ T B hTu hBu
  have hLR : p^2 ≤ finiteBoundaryEventProbability (box N) θ ξ (fun ω => L ω ∧ R ω) := by
    calc
      p^2 = p*p := by ring
      _ ≤ finiteBoundaryEventProbability (box N) θ ξ L * finiteBoundaryEventProbability (box N) θ ξ R :=
        mul_le_mul hL hR hp.le ENNReal.toReal_nonneg
      _ ≤ _ := finiteBoundaryEventProbability_fkg _ θ ξ L R hLu hRu
  calc
    p^4 = p^2*p^2 := by ring
    _ ≤ finiteBoundaryEventProbability (box N) θ ξ (fun ω => T ω ∧ B ω) *
        finiteBoundaryEventProbability (box N) θ ξ (fun ω => L ω ∧ R ω) :=
      mul_le_mul hTB hLR (sq_nonneg p) ENNReal.toReal_nonneg
    _ ≤ finiteBoundaryEventProbability (box N) θ ξ (fun ω => (T ω ∧ B ω) ∧ (L ω ∧ R ω)) :=
      finiteBoundaryEventProbability_fkg _ θ ξ _ _
        (fun _ _ h hω => ⟨hTu h hω.1,hBu h hω.2⟩)
        (fun _ _ h hω => ⟨hLu h hω.1,hRu h hω.2⟩)
    _ ≤ _ := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro A hA
      exact fourCorridor_annulusCircuitEvent_centered (box N) z n m (by omega) hm hmn
        ((boolConfigurationEquiv _).symm A) hA.1.1 hA.1.2 hA.2.1 hA.2.2

end
end PottsContinuity.RSW
