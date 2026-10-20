module

public import PottsContinuity.PlanarTopology.BandCrossingGluing
public import PottsContinuity.PlanarTopology.KSTCorridorTranspose
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Move a horizontal factor with centre `c` to the source rectangle. -/
abbrev kstHorizontalFactorIso (c : ℤ) : PD.squareLattice ≃g PD.squareLattice :=
  latticeTranslationIso (-c,0)

/-- Move a vertical overlap factor to the source horizontal rectangle. -/
abbrev kstVerticalFactorIso (c : ℤ) : PD.squareLattice ≃g PD.squareLattice :=
  (latticeTranslationIso (-c,0)).trans latticeTransposeIso

 theorem kstHorizontalFactorIso_box (c : ℤ) (a v : LatticeVertex) (r : ℕ) :
    kstHorizontalFactorIso c v ∈ latticeBox (kstHorizontalFactorIso c a) r ↔
      v ∈ latticeBox a r := mem_latticeBox_translate_iff (-c,0) a v r

 theorem kstVerticalFactorIso_box (c : ℤ) (a v : LatticeVertex) (r : ℕ) :
    kstVerticalFactorIso c v ∈ latticeBox (kstVerticalFactorIso c a) r ↔
      v ∈ latticeBox a r := by
  simp only [mem_latticeBox]
  change (((a.2+0)-(r : ℤ) ≤ v.2+0 ∧ v.2+0 ≤ (a.2+0)+r) ∧
    (a.1+ -c-r ≤ v.1+ -c ∧ v.1+ -c ≤ a.1+ -c+r)) ↔ _
  omega

/-- A translated factor supplies an original horizontal band crossing. -/
theorem kst_horizontal_factor_witness (n : ℕ) (c : ℤ) (ω : LatticeConfiguration)
    (hω : ω ∈ latticeConfigurationIsoHomeomorph (kstHorizontalFactorIso c) ⁻¹'
      horizontalRectangle (-2*(n : ℤ),-(n : ℤ)) (4*n) (2*n)) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = c-2*(n : ℤ) ∧ v.1 = c+2*(n : ℤ) ∧
      ∀ z ∈ p.support, -(n : ℤ) ≤ z.2 ∧ z.2 ≤ (n : ℤ) := by
  obtain ⟨u,v,p,_,hp,hu,hv,hbox⟩ := kst_horizontal_crossing_witness _ _ _ _ hω
  refine ⟨_,_,p.map (kstHorizontalFactorIso c).symm.toHom,
    kstPathOpen_map_iso_inverse _ ω p hp,?_,?_,?_⟩
  · change u.1- -c = c-2*(n : ℤ)
    change u.1 = -2*(n : ℤ) at hu
    omega
  · change v.1- -c = c+2*(n : ℤ)
    change v.1 = -2*(n : ℤ)+(4*n : ℕ) at hv
    push_cast at hv
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    have hh := hbox w hw
    change -(n : ℤ) ≤ w.2-0 ∧ w.2-0 ≤ (n : ℤ)
    have hhY := hh.2.2
    change -↑n ≤ w.2 ∧ w.2 ≤ -↑n+(2*n : ℕ) at hhY
    push_cast at hhY
    omega

/-- A rotated factor supplies an original vertical crossing of the overlap. -/
theorem kst_vertical_factor_witness (n : ℕ) (c : ℤ) (ω : LatticeConfiguration)
    (hω : ω ∈ latticeConfigurationIsoHomeomorph (kstVerticalFactorIso c) ⁻¹'
      horizontalRectangle (-2*(n : ℤ),-(n : ℤ)) (4*n) (2*n)) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = -(n : ℤ) ∧ v.2 = (n : ℤ) ∧
      kstPathIn p (c-(n : ℤ)) (c+(n : ℤ)) (-(n : ℤ)) (n : ℤ) := by
  obtain ⟨u,v,p,_,hp,hu,hv,hbox⟩ := kst_horizontal_crossing_witness _ _ _ _ hω
  let P := p.map (kstVerticalFactorIso c).symm.toHom
  have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.2-y.2| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.1-y.1)
    omega
  have hv' : (n : ℤ) ≤ ((kstVerticalFactorIso c).symm v).2 := by
    change (n : ℤ) ≤ v.1-0
    change v.1 = -2*(n : ℤ)+(4*n : ℕ) at hv
    push_cast at hv
    omega
  obtain ⟨a,b,Q,hQ,ha,hb,hQB⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.2) hstep P (a := -(n : ℤ)) (b := (n : ℤ)) (by omega)
    (by change u.1-0 ≤ -(n : ℤ); change u.1 = -2*(n : ℤ) at hu; omega) hv'
  refine ⟨a,b,Q,kstPathOpen_of_subwalk hQ
    (kstPathOpen_map_iso_inverse _ ω p hp),ha,hb,?_⟩
  intro z hz
  have hzP := hQ.support_subset hz
  rw [SimpleGraph.Walk.support_map] at hzP
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hzP
  have hh := hbox w hw
  have he1 : z.1 = w.2- -c := by rw [← he]; rfl
  have hhY := hh.2.2
  change -(n : ℤ) ≤ w.2 ∧ w.2 ≤ -(n : ℤ)+(2*n : ℕ) at hhY
  push_cast at hhY
  exact ⟨by omega,by omega,hQB z hz⟩

end
end PottsContinuity.PlanarTopology
