module

public import PottsContinuity.PlanarTopology.AlphaCoreRectangleFactors
public import PottsContinuity.PlanarTopology.BandCrossingChain
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- 449 horizontal rectangles and their 448 transposed overlap crossings. -/
def alphaCoreRectangleFactor (k : ℕ) (j : Fin 897) : PD.squareLattice ≃g PD.squareLattice :=
  if j.val < 449 then
    kstHorizontalFactorIso (-512*(k : ℤ)-1+2*(j.val : ℤ)*(k : ℤ)+65*(k : ℤ))
  else
    kstVerticalFactorIso (-512*(k : ℤ)-1+2*((j.val-449 : ℕ)+1 : ℕ)*(k : ℤ)+64*(k : ℤ))

/-- The odd source rectangle forces a long crossing with fewer than 2000 factors. -/
theorem alpha_core_rectangle_long_gluing (k : ℕ) (hk : 1 ≤ k) :
    ∃ e : Fin 897 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' alphaCoreRectangle k) ⊆
        horizontalRectangle (-512*(k : ℤ)-1,-64*(k : ℤ)) (1024*k+1) (128*k-1) := by
  refine ⟨alphaCoreRectangleFactor k,?_,?_⟩
  · intro j c v r
    unfold alphaCoreRectangleFactor
    split
    · exact kstHorizontalFactorIso_box _ c v r
    · exact kstVerticalFactorIso_box _ c v r
  · intro ω hω
    have hH : ∀ i : ℕ, i < 449 → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
        kstPathOpen ω p ∧ u.1 = -512*(k : ℤ)-1+(i : ℤ)*(2*(k : ℤ)) ∧
        v.1 = -512*(k : ℤ)-1+(i : ℤ)*(2*(k : ℤ))+(130*(k : ℤ)-1) ∧
        ∀ z ∈ p.support, -64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℤ)-1 := by
      intro i hi
      let j : Fin 897 := ⟨i,by omega⟩
      have hj := Set.mem_iInter.mp hω j
      change ω ∈ latticeConfigurationIsoHomeomorph (alphaCoreRectangleFactor k j) ⁻¹' _ at hj
      simp only [alphaCoreRectangleFactor,show j.val < 449 from hi,ite_eq_left] at hj
      obtain ⟨u,v,p,hp,hu,hv,hband⟩ := alpha_core_horizontal_factor_witness k hk _ ω hj
      refine ⟨u,v,p,hp,?_,?_,hband⟩
      · dsimp [j] at hu
        nlinarith [hu]
      · dsimp [j] at hv
        nlinarith [hv]
    have hV : ∀ i : ℕ, i+1 < 449 → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
        kstPathOpen ω p ∧ u.2 = -64*(k : ℤ) ∧ v.2 = 64*(k : ℤ)-1 ∧
        kstPathIn p (-512*(k : ℤ)-1+((i : ℤ)+1)*(2*(k : ℤ)))
          (-512*(k : ℤ)-1+(i : ℤ)*(2*(k : ℤ))+(130*(k : ℤ)-1))
          (-64*(k : ℤ)) (64*(k : ℤ)-1) := by
      intro i hi
      let j : Fin 897 := ⟨449+i,by omega⟩
      have hj := Set.mem_iInter.mp hω j
      change ω ∈ latticeConfigurationIsoHomeomorph (alphaCoreRectangleFactor k j) ⁻¹' _ at hj
      have hjrho : ¬j.val < 449 := by dsimp [j]; omega
      simp only [alphaCoreRectangleFactor,hjrho] at hj
      obtain ⟨u,v,p,hp,hu,hv,hbox⟩ := alpha_core_vertical_factor_witness k hk _ ω hj
      refine ⟨u,v,p,hp,hu,hv,?_⟩
      intro z hz
      have hh := hbox z hz
      have hji : j.val-449 = i := by dsimp [j]; omega
      rw [hji] at hh
      push_cast at hh
      exact ⟨by nlinarith [hh.1],by nlinarith [hh.2.1],hh.2.2⟩
    obtain ⟨u,v,p,hp,hu,hv,hband⟩ := kst_band_horizontal_chain_width 449 (by omega)
      (-512*(k : ℤ)-1) (2*(k : ℤ)) (130*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1)
      (by omega) (by omega) (by omega) ω hH hV
    have hv' : 512*(k : ℤ) ≤ v.1 := by omega
    have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
      intro x y h
      change |x.1-y.1|+|x.2-y.2| = 1 at h
      have := abs_nonneg (x.2-y.2)
      omega
    obtain ⟨x,y,Q,hQ,hx,hy,hQB⟩ := walk_subwalk_between_levels
      (fun z : LatticeVertex => z.1) hstep p
      (a := -512*(k : ℤ)-1) (b := 512*(k : ℤ)) (by omega) (by omega) hv'
    apply horizontalRectangle_of_kst_open_walk _ _ _ ω Q
      (kstPathOpen_of_subwalk hQ hp) hx
    · change y.1 = -512*(k : ℤ)-1+(1024*k+1 : ℕ)
      omega
    · intro z hz
      have hh := hQB z hz
      have hbnd := hband z (hQ.support_subset hz)
      change -512*(k : ℤ)-1 ≤ z.1 ∧ z.1 ≤ -512*(k : ℤ)-1+(1024*k+1 : ℕ) ∧
        -64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ -64*(k : ℤ)+(128*k-1 : ℕ)
      exact ⟨hh.1,by omega,hbnd.1,by omega⟩

end
end PottsContinuity.PlanarTopology
