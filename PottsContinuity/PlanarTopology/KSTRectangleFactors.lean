module

public import PottsContinuity.PlanarTopology.KSTAspectFactors
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- A general rectangular translated factor supplies an original band crossing. -/
theorem kst_horizontal_rectangle_factor_witness (w h : ℕ) (c : ℤ) (ω : LatticeConfiguration)
    (hω : ω ∈ latticeConfigurationIsoHomeomorph (kstHorizontalFactorIso c) ⁻¹'
      horizontalRectangle (-(w : ℤ),-(h : ℤ)) (2*w) (2*h)) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = c-(w : ℤ) ∧ v.1 = c+(w : ℤ) ∧
      ∀ z ∈ p.support, -(h : ℤ) ≤ z.2 ∧ z.2 ≤ (h : ℤ) := by
  obtain ⟨u,v,p,_,hp,hu,hv,hbox⟩ := kst_horizontal_crossing_witness _ _ _ _ hω
  refine ⟨_,_,p.map (kstHorizontalFactorIso c).symm.toHom,
    kstPathOpen_map_iso_inverse _ ω p hp,?_,?_,?_⟩
  · change u.1- -c = c-(w : ℤ)
    change u.1 = -(w : ℤ) at hu
    omega
  · change v.1- -c = c+(w : ℤ)
    change v.1 = -(w : ℤ)+(2*w : ℕ) at hv
    push_cast at hv
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    have hh := hbox w hw
    change -(h : ℤ) ≤ w.2-0 ∧ w.2-0 ≤ (h : ℤ)
    have hhY := hh.2.2
    change -↑h ≤ w.2 ∧ w.2 ≤ -↑h+(2*h : ℕ) at hhY
    push_cast at hhY
    omega

/-- A rotated factor supplies an original vertical crossing of the overlap. -/
theorem kst_vertical_rectangle_factor_witness (w h : ℕ) (hhw : h ≤ w) (c : ℤ) (ω : LatticeConfiguration)
    (hω : ω ∈ latticeConfigurationIsoHomeomorph (kstVerticalFactorIso c) ⁻¹'
      horizontalRectangle (-(w : ℤ),-(h : ℤ)) (2*w) (2*h)) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = -(h : ℤ) ∧ v.2 = (h : ℤ) ∧
      kstPathIn p (c-(h : ℤ)) (c+(h : ℤ)) (-(h : ℤ)) (h : ℤ) := by
  obtain ⟨u,v,p,_,hp,hu,hv,hbox⟩ := kst_horizontal_crossing_witness _ _ _ _ hω
  let P := p.map (kstVerticalFactorIso c).symm.toHom
  have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.2-y.2| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.1-y.1)
    omega
  have hv' : (h : ℤ) ≤ ((kstVerticalFactorIso c).symm v).2 := by
    change (h : ℤ) ≤ v.1-0
    change v.1 = -(w : ℤ)+(2*w : ℕ) at hv
    push_cast at hv
    omega
  obtain ⟨a,b,Q,hQ,ha,hb,hQB⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.2) hstep P (a := -(h : ℤ)) (b := (h : ℤ)) (by omega)
    (by change u.1-0 ≤ -(h : ℤ); change u.1 = -(w : ℤ) at hu; omega) hv'
  refine ⟨a,b,Q,kstPathOpen_of_subwalk hQ
    (kstPathOpen_map_iso_inverse _ ω p hp),ha,hb,?_⟩
  intro z hz
  have hzP := hQ.support_subset hz
  rw [SimpleGraph.Walk.support_map] at hzP
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hzP
  have hh := hbox w hw
  have he1 : z.1 = w.2- -c := by rw [← he]; rfl
  have hhY := hh.2.2
  change -(h : ℤ) ≤ w.2 ∧ w.2 ≤ -(h : ℤ)+(2*h : ℕ) at hhY
  push_cast at hhY
  exact ⟨by omega,by omega,hQB z hz⟩


end
end PottsContinuity.PlanarTopology
