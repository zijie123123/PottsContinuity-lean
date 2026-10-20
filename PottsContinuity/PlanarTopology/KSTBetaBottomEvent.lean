module

public import PottsContinuity.PlanarTopology.KSTBetaBottomChain
public import PottsContinuity.PlanarTopology.ConfinedWalkCylinders
public import PottsContinuity.PlanarTopology.KSTAspectFactors
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The beta-target variant of KST Section 3's event F: a connection from the bottom-left beta target
to the bottom-right beta target in the beta-wide rectangle. Integer
inequalities give the intended targets on the whole natural scale carrier. -/
def kstBetaBottomArc (m : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u v, ∃ p : PD.squareLattice.Walk u v,
    kstPathOpen ω p ∧ u.2 = -(m : ℤ) ∧ v.2 = -(m : ℤ) ∧
    12*u.1 ≤ -(m : ℤ) ∧ (m : ℤ) ≤ 12*v.1 ∧
    ∀ z ∈ p.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)}

/-- The 96 horizontal translates appearing in the source bottom-arc gluing. -/
def kstBetaBottomArcFactor (a : ℕ) (j : Fin 96) : PD.squareLattice ≃g PD.squareLattice :=
  kstHorizontalFactorIso ((2*(j.val : ℤ)-95)*(a : ℤ))

/-- Literal event form of the source's bottom-arc gluing at integral beta
scales. The factors preserve every lattice box. -/
theorem kst_beta_bottom_arc_long_gluing (a : ℕ) (ha : 1 ≤ a) :
    ∃ e : Fin 96 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' kstBetaBottomArc (12*a)) ⊆
        horizontalRectangle (-96*(a : ℤ),-12*(a : ℤ)) (192*a) (24*a) := by
  refine ⟨kstBetaBottomArcFactor a,fun j => kstHorizontalFactorIso_box _,?_⟩
  intro ω hω
  apply kst_96_beta_bottom_connections_glue a ha ω
  intro i
  obtain ⟨u,v,p,hp,hu,hv,hux,hvx,hbox⟩ := Set.mem_iInter.mp hω i
  let e := kstBetaBottomArcFactor a i
  let c := (2*(i.val : ℤ)-95)*(a : ℤ)
  refine ⟨e.symm u,e.symm v,p.map e.symm.toHom,
    kstPathOpen_map_iso_inverse e ω p hp,?_,?_,?_,?_,?_⟩
  · change u.2-0 = -12*(a : ℤ)
    push_cast at hu
    omega
  · change v.2-0 = -12*(a : ℤ)
    push_cast at hv
    omega
  · change u.1- -c ≤ (2*(i.val : ℤ)-96)*(a : ℤ)
    push_cast at hux
    dsimp [c]
    nlinarith [hux]
  · change (2*(i.val : ℤ)-94)*(a : ℤ) ≤ v.1- -c
    push_cast at hvx
    dsimp [c]
    nlinarith [hvx]
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    have hh := hbox b hb
    push_cast at hh
    have hbx : |b.1| ≤ 13*(a : ℤ) := by omega
    have hby : |b.2| ≤ 12*(a : ℤ) := hh.2
    have hbi := abs_le.mp hbx
    have hbj := abs_le.mp hby
    have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ 95 := by omega
    have hcl : -95*(a : ℤ) ≤ c := by
      dsimp [c]
      nlinarith [mul_nonneg hi.1 (Int.natCast_nonneg a)]
    have hcr : c ≤ 95*(a : ℤ) := by
      dsimp [c]
      nlinarith [mul_nonneg (show 0 ≤ 95-(i.val : ℤ) by omega) (Int.natCast_nonneg a)]
    change -108*(a : ℤ) ≤ b.1- -c ∧ b.1- -c ≤ 108*(a : ℤ) ∧
      -12*(a : ℤ) ≤ b.2-0 ∧ b.2-0 ≤ 12*(a : ℤ)
    omega

end
end PottsContinuity.PlanarTopology
