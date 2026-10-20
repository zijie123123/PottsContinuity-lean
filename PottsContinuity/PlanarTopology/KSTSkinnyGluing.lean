module

public import PottsContinuity.PlanarTopology.KSTRectangleFactors
public import PottsContinuity.PlanarTopology.BandCrossingChain
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Horizontal rectangles and transposed overlaps for a skinny source rectangle. -/
def kstSkinnyFactor (stages n a : ℕ) (j : Fin (2*stages-1)) :
    PD.squareLattice ≃g PD.squareLattice :=
  if j.val < stages then
    kstHorizontalFactorIso (-((n+stages*a : ℕ) : ℤ)+(n : ℤ)+(a : ℤ)+2*(j.val : ℤ)*(a : ℤ))
  else
    kstVerticalFactorIso (-((n+stages*a : ℕ) : ℤ)+(n : ℤ)+2*((j.val-stages : ℕ)+1 : ℕ)*(a : ℤ))

/-- Gluing skinny rectangles increases their horizontal excess by one copy
per stage, with exactly two stages minus one isometric factors. -/
theorem kst_skinny_rectangle_gluing (stages n a : ℕ) (hs : 1 ≤ stages) :
    ∃ e : Fin (2*stages-1) → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹'
        horizontalRectangle (-((n+a : ℕ) : ℤ),-(n : ℤ)) (2*(n+a)) (2*n)) ⊆
        horizontalRectangle (-((n+stages*a : ℕ) : ℤ),-(n : ℤ))
          (2*(n+stages*a)) (2*n) := by
  refine ⟨kstSkinnyFactor stages n a,?_,?_⟩
  · intro j c v r
    unfold kstSkinnyFactor
    split
    · exact kstHorizontalFactorIso_box _ c v r
    · exact kstVerticalFactorIso_box _ c v r
  · intro ω hω
    have hH : ∀ i : ℕ, i < stages → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
        kstPathOpen ω p ∧ u.1 = -((n+stages*a : ℕ) : ℤ)+(i : ℤ)*(2*(a : ℤ)) ∧
        v.1 = -((n+stages*a : ℕ) : ℤ)+(i : ℤ)*(2*(a : ℤ))+2*((n+a : ℕ) : ℤ) ∧
        ∀ z ∈ p.support, -(n : ℤ) ≤ z.2 ∧ z.2 ≤ (n : ℤ) := by
      intro i hi
      let j : Fin (2*stages-1) := ⟨i,by omega⟩
      have hj := Set.mem_iInter.mp hω j
      change ω ∈ latticeConfigurationIsoHomeomorph (kstSkinnyFactor stages n a j) ⁻¹' _ at hj
      simp only [kstSkinnyFactor,show j.val < stages from hi,ite_eq_left] at hj
      obtain ⟨u,v,p,hp,hu,hv,hband⟩ := kst_horizontal_rectangle_factor_witness (n+a) n _ ω hj
      refine ⟨u,v,p,hp,?_,?_,hband⟩
      · dsimp [j] at hu
        push_cast at hu ⊢
        nlinarith [hu]
      · dsimp [j] at hv
        push_cast at hv ⊢
        nlinarith [hv]
    have hV : ∀ i : ℕ, i+1 < stages → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
        kstPathOpen ω p ∧ u.2 = -(n : ℤ) ∧ v.2 = (n : ℤ) ∧
        kstPathIn p (-((n+stages*a : ℕ) : ℤ)+((i : ℤ)+1)*(2*(a : ℤ)))
          (-((n+stages*a : ℕ) : ℤ)+(i : ℤ)*(2*(a : ℤ))+2*((n+a : ℕ) : ℤ))
          (-(n : ℤ)) (n : ℤ) := by
      intro i hi
      let j : Fin (2*stages-1) := ⟨stages+i,by omega⟩
      have hj := Set.mem_iInter.mp hω j
      change ω ∈ latticeConfigurationIsoHomeomorph (kstSkinnyFactor stages n a j) ⁻¹' _ at hj
      have hjrho : ¬j.val < stages := by dsimp [j]; omega
      simp only [kstSkinnyFactor,hjrho] at hj
      obtain ⟨u,v,p,hp,hu,hv,hbox⟩ := kst_vertical_rectangle_factor_witness (n+a) n (by omega) _ ω hj
      refine ⟨u,v,p,hp,hu,hv,?_⟩
      intro z hz
      have hh := hbox z hz
      have hji : j.val-stages = i := by dsimp [j]; omega
      rw [hji] at hh
      push_cast at hh ⊢
      exact ⟨by nlinarith [hh.1],by nlinarith [hh.2.1],hh.2.2⟩
    obtain ⟨u,v,p,hp,hu,hv,hband⟩ := kst_band_horizontal_chain_width stages hs
      (-((n+stages*a : ℕ) : ℤ)) (2*(a : ℤ)) (2*((n+a : ℕ) : ℤ)) (-(n : ℤ)) (n : ℤ)
      (by omega) (by push_cast; omega) (by omega) ω hH hV
    have hv' : ((n+stages*a : ℕ) : ℤ) ≤ v.1 := by
      push_cast at hv ⊢
      nlinarith [hv]
    have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
      intro x y h
      change |x.1-y.1|+|x.2-y.2| = 1 at h
      have := abs_nonneg (x.2-y.2)
      omega
    obtain ⟨x,y,Q,hQ,hx,hy,hQB⟩ := walk_subwalk_between_levels
      (fun z : LatticeVertex => z.1) hstep p
      (a := -((n+stages*a : ℕ) : ℤ)) (b := ((n+stages*a : ℕ) : ℤ))
      (by omega) (by omega) hv'
    apply horizontalRectangle_of_kst_open_walk _ _ _ ω Q
      (kstPathOpen_of_subwalk hQ hp) hx
    · change y.1 = -((n+stages*a : ℕ) : ℤ)+(2*(n+stages*a) : ℕ)
      push_cast at hy ⊢
      nlinarith [hy]
    · intro z hz
      have hh := hQB z hz
      have hbnd := hband z (hQ.support_subset hz)
      change -((n+stages*a : ℕ) : ℤ) ≤ z.1 ∧
        z.1 ≤ -((n+stages*a : ℕ) : ℤ)+(2*(n+stages*a) : ℕ) ∧
        -(n : ℤ) ≤ z.2 ∧ z.2 ≤ -(n : ℤ)+(2*n : ℕ)
      push_cast at hh ⊢
      exact ⟨hh.1,by nlinarith [hh.2],hbnd.1,by omega⟩

end
end PottsContinuity.PlanarTopology
