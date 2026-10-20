module

public import PottsContinuity.PlanarTopology.KSTRectangleFactors
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Full horizontal crossing of the exact odd-sided alpha core box. -/
def alphaCoreRectangle (k : ℕ) : Set LatticeConfiguration :=
  horizontalRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k-1) (128*k-1)

theorem alpha_core_horizontal_factor_witness (k : ℕ) (hk : 1 ≤ k) (c : ℤ)
    (ω : LatticeConfiguration)
    (hω : ω ∈ latticeConfigurationIsoHomeomorph (kstHorizontalFactorIso c) ⁻¹' alphaCoreRectangle k) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = c-65*(k : ℤ) ∧ v.1 = c+65*(k : ℤ)-1 ∧
      ∀ z ∈ p.support, -64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℤ)-1 := by
  obtain ⟨u,v,p,_,hp,hu,hv,hbox⟩ := kst_horizontal_crossing_witness _ _ _ _ hω
  refine ⟨_,_,p.map (kstHorizontalFactorIso c).symm.toHom,
    kstPathOpen_map_iso_inverse _ ω p hp,?_,?_,?_⟩
  · change u.1- -c = _
    change u.1 = -65*(k : ℤ) at hu
    omega
  · change v.1- -c = _
    change v.1 = -65*(k : ℤ)+(130*k-1 : ℕ) at hv
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    have hh := (hbox w hw).2.2
    change -64*(k : ℤ) ≤ w.2 ∧ w.2 ≤ -64*(k : ℤ)+(128*k-1 : ℕ) at hh
    change -64*(k : ℤ) ≤ w.2-0 ∧ w.2-0 ≤ 64*(k : ℤ)-1
    omega

/-- Rotated odd-box crossings clip to the exact overlap band. -/
theorem alpha_core_vertical_factor_witness (k : ℕ) (hk : 1 ≤ k) (c : ℤ)
    (ω : LatticeConfiguration)
    (hω : ω ∈ latticeConfigurationIsoHomeomorph (kstVerticalFactorIso c) ⁻¹' alphaCoreRectangle k) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = -64*(k : ℤ) ∧ v.2 = 64*(k : ℤ)-1 ∧
      kstPathIn p (c-64*(k : ℤ)) (c+64*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1) := by
  obtain ⟨u,v,p,_,hp,hu,hv,hbox⟩ := kst_horizontal_crossing_witness _ _ _ _ hω
  let P := p.map (kstVerticalFactorIso c).symm.toHom
  have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.2-y.2| ≤ 1 := by
    intro x y h
    change |x.1-y.1|+|x.2-y.2| = 1 at h
    have := abs_nonneg (x.1-y.1)
    omega
  have hv' : 64*(k : ℤ)-1 ≤ ((kstVerticalFactorIso c).symm v).2 := by
    change 64*(k : ℤ)-1 ≤ v.1-0
    change v.1 = -65*(k : ℤ)+(130*k-1 : ℕ) at hv
    omega
  obtain ⟨a,b,Q,hQ,ha,hb,hQB⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.2) hstep P (a := -64*(k : ℤ)) (b := 64*(k : ℤ)-1) (by omega)
    (by change u.1-0 ≤ _; change u.1 = -65*(k : ℤ) at hu; omega) hv'
  refine ⟨a,b,Q,kstPathOpen_of_subwalk hQ
    (kstPathOpen_map_iso_inverse _ ω p hp),ha,hb,?_⟩
  intro z hz
  have hzP := hQ.support_subset hz
  rw [SimpleGraph.Walk.support_map] at hzP
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hzP
  have he1 : z.1 = w.2- -c := by rw [← he]; rfl
  have hh := (hbox w hw).2.2
  change -64*(k : ℤ) ≤ w.2 ∧ w.2 ≤ -64*(k : ℤ)+(128*k-1 : ℕ) at hh
  exact ⟨by omega,by omega,hQB z hz⟩

end
end PottsContinuity.PlanarTopology
