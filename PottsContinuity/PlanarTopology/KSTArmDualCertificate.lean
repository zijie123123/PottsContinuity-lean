module

public import PottsContinuity.PlanarTopology.AlphaCoreFiniteCover
public import PottsContinuity.PlanarTopology.WholePlaneRectangleExclusion

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves BD12
noncomputable section

/-- Long ordinary rectangle obtained by the exact odd-core dual gluing. -/
def alphaCoreLongRectangle (k : ℕ) : Set LatticeConfiguration :=
  horizontalRectangle (-512*(k : ℤ)-1,-64*(k : ℤ)) (1024*k+1) (128*k-1)

/-- A short primal crossing excludes the transposed complementary dual long
crossing, including the exact exterior half-cell rows. -/
theorem alpha_core_dual_long_crossing_excludes_short (k : ℕ) (hk : 1 ≤ k) :
    horizontalRectangle (-64*(k : ℤ),-512*(k : ℤ)) (128*k) (1024*k) ⊆
      (wholePlaneDualConfigurationHomeomorph ⁻¹'
        (latticeConfigurationIsoHomeomorph latticeTransposeIso ⁻¹' alphaCoreLongRectangle k))ᶜ := by
  intro ω hshort hlong
  obtain ⟨u,v,p,_,hp,hu,hv,hpB⟩ := kst_horizontal_crossing_witness _ _ _ _ hshort
  obtain ⟨x,y,r,_,hr,hx,hy,hrB⟩ := kst_horizontal_crossing_witness _ _ _ _ hlong
  let q := r.map latticeTransposeIso.symm.toHom
  have hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q :=
    kstPathOpen_map_iso_inverse latticeTransposeIso _ r hr
  apply wholePlane_rectangle_crossings_exclusive
    (-64*(k : ℤ),-512*(k : ℤ)) (128*k) (1024*k) (by omega) ω p q hp hq hpB
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    have hh := hrB b hb
    change -512*(k : ℤ)-1 ≤ b.1 ∧ b.1 ≤ -512*(k : ℤ)-1+(1024*k+1 : ℕ) ∧
      -64*(k : ℤ) ≤ b.2 ∧ b.2 ≤ -64*(k : ℤ)+(128*k-1 : ℕ) at hh
    change -64*(k : ℤ) ≤ b.2 ∧ b.2 ≤ -64*(k : ℤ)+(128*k : ℕ)-1 ∧
      -512*(k : ℤ)-1 ≤ b.1 ∧ b.1 ≤ -512*(k : ℤ)+(1024*k : ℕ)
    exact ⟨hh.2.2.1,by omega,hh.1,by omega⟩
  · exact hu
  · exact hv
  · change x.1 = -512*(k : ℤ)-1
    exact hx
  · change y.1 = -512*(k : ℤ)+(1024*k : ℕ)
    change y.1 = -512*(k : ℤ)-1+(1024*k+1 : ℕ) at hy
    omega

/-- Complete geometric arm certificate for the KST dual argument: increasing
finite candidates cover arm absence in the actual dual state; their isometric
intersections force a long crossing excluded by the short primal crossing. -/
theorem kst_arm_dual_cover_certificate (k : ℕ) (hk : 1 ≤ k) :
    ∃ S : Fin 2000 → Set LatticeConfiguration,
      (∀ i, PD.RCInfinite.IsCylinder (S i) ∧ IsUpperSet (S i)) ∧
      ((kstArm (64*k))ᶜ ⊆ wholePlaneDualConfigurationHomeomorph ⁻¹' (⋃ i, S i)) ∧
      (∀ i, ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
        (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
        (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) ⊆ alphaCoreLongRectangle k) ∧
      (horizontalRectangle (-64*(k : ℤ),-512*(k : ℤ)) (128*k) (1024*k) ⊆
        (wholePlaneDualConfigurationHomeomorph ⁻¹'
          (latticeConfigurationIsoHomeomorph latticeTransposeIso ⁻¹' alphaCoreLongRectangle k))ᶜ) := by
  obtain ⟨S,hS,hcover,hglue⟩ := kst_arm_complement_dual_finite_cover k hk
  exact ⟨S,hS,hcover,hglue,alpha_core_dual_long_crossing_excludes_short k hk⟩

end
end PottsContinuity.PlanarTopology
