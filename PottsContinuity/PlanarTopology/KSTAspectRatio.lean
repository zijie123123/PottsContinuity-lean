module

public import PottsContinuity.PlanarTopology.KSTAspectFactors
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The rho horizontal factors followed by the rho-1 vertical overlaps. -/
def kstAspectFactor (rho n : ℕ) (j : Fin (2*rho-1)) :
    PD.squareLattice ≃g PD.squareLattice :=
  if j.val < rho then
    kstHorizontalFactorIso (-((rho*n : ℕ) : ℤ)+((j.val : ℤ)+1)*2*(n : ℤ))
  else
    kstVerticalFactorIso (-((rho*n : ℕ) : ℤ)+(2*((j.val-rho : ℕ) : ℤ)+3)*(n : ℤ))

/-- Exact deterministic aspect-ratio extension used in KST's first relation.
All factors preserve lattice boxes and all connections use original open bonds. -/
theorem kst_aspect_ratio_gluing (rho n : ℕ) (hrho : 1 ≤ rho) (_hn : 1 ≤ n) :
    ∃ e : Fin (2*rho-1) → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹'
        horizontalRectangle (-2*(n : ℤ),-(n : ℤ)) (4*n) (2*n)) ⊆
        horizontalRectangle (-((rho*n : ℕ) : ℤ),-(n : ℤ)) (2*rho*n) (2*n) := by
  refine ⟨kstAspectFactor rho n,?_,?_⟩
  · intro j c v r
    unfold kstAspectFactor
    split
    · exact kstHorizontalFactorIso_box _ c v r
    · exact kstVerticalFactorIso_box _ c v r
  · intro ω hω
    have hH : ∀ i : ℕ, i < rho → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
        kstPathOpen ω p ∧ u.1 = -((rho*n : ℕ) : ℤ)+(i : ℤ)*(2*(n : ℤ)) ∧
        v.1 = -((rho*n : ℕ) : ℤ)+((i : ℤ)+2)*(2*(n : ℤ)) ∧
        ∀ z ∈ p.support, -(n : ℤ) ≤ z.2 ∧ z.2 ≤ (n : ℤ) := by
      intro i hi
      let j : Fin (2*rho-1) := ⟨i,by omega⟩
      have hj := Set.mem_iInter.mp hω j
      change ω ∈ latticeConfigurationIsoHomeomorph (kstAspectFactor rho n j) ⁻¹' _ at hj
      simp only [kstAspectFactor, show j.val < rho from hi, ite_eq_left] at hj
      obtain ⟨u,v,p,hp,hu,hv,hband⟩ := kst_horizontal_factor_witness n _ ω hj
      refine ⟨u,v,p,hp,?_,?_,hband⟩
      · dsimp [j] at hu
        push_cast
        nlinarith [hu]
      · dsimp [j] at hv
        push_cast
        nlinarith [hv]
    have hV : ∀ i : ℕ, i+1 < rho → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
        kstPathOpen ω p ∧ u.2 = -(n : ℤ) ∧ v.2 = (n : ℤ) ∧
        kstPathIn p (-((rho*n : ℕ) : ℤ)+((i : ℤ)+1)*(2*(n : ℤ)))
          (-((rho*n : ℕ) : ℤ)+((i : ℤ)+2)*(2*(n : ℤ))) (-(n : ℤ)) (n : ℤ) := by
      intro i hi
      let j : Fin (2*rho-1) := ⟨rho+i,by omega⟩
      have hj := Set.mem_iInter.mp hω j
      change ω ∈ latticeConfigurationIsoHomeomorph (kstAspectFactor rho n j) ⁻¹' _ at hj
      have hjrho : ¬j.val < rho := by dsimp [j]; omega
      simp only [kstAspectFactor,hjrho] at hj
      obtain ⟨u,v,p,hp,hu,hv,hbox⟩ := kst_vertical_factor_witness n _ ω hj
      refine ⟨u,v,p,hp,hu,hv,?_⟩
      intro z hz
      have hh := hbox z hz
      have hji : j.val-rho = i := by dsimp [j]; omega
      rw [hji] at hh
      exact ⟨by nlinarith [hh.1],by nlinarith [hh.2.1],hh.2.2⟩
    obtain ⟨u,v,p,hp,hu,hv,hband⟩ := kst_band_horizontal_chain rho hrho
      (-((rho*n : ℕ) : ℤ)) (2*(n : ℤ)) (-(n : ℤ)) (n : ℤ)
      (by omega) (by omega) ω hH hV
    have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
      intro x y h
      change |x.1-y.1|+|x.2-y.2| = 1 at h
      have := abs_nonneg (x.2-y.2)
      omega
    obtain ⟨a,b,Q,hQ,ha,hb,hQB⟩ := walk_subwalk_between_levels
      (fun z : LatticeVertex => z.1) hstep p
      (a := -((rho*n : ℕ) : ℤ)) (b := ((rho*n : ℕ) : ℤ))
      (by omega) (by omega) (by push_cast at hv ⊢; nlinarith)
    apply horizontalRectangle_of_kst_open_walk _ _ _ ω Q
      (kstPathOpen_of_subwalk hQ hp) ha
    · change b.1 = -((rho*n : ℕ) : ℤ)+(2*rho*n : ℕ)
      push_cast at hb ⊢
      nlinarith
    · intro z hz
      have hh := hQB z hz
      have hbnd := hband z (hQ.support_subset hz)
      change -((rho*n : ℕ) : ℤ) ≤ z.1 ∧
        z.1 ≤ -((rho*n : ℕ) : ℤ)+(2*rho*n : ℕ) ∧
        -(n : ℤ) ≤ z.2 ∧ z.2 ≤ -(n : ℤ)+(2*n : ℕ)
      push_cast at hh ⊢
      exact ⟨hh.1,by nlinarith [hh.2],hbnd.1,by omega⟩

end
end PottsContinuity.PlanarTopology
