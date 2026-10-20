module

public import PottsContinuity.PlanarTopology.AlphaCoreBottomChain
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

/-- Bottom-to-bottom connection across the exact contracted alpha gap. -/
def alphaCoreBottomArc (k : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u v, ∃ p : PD.squareLattice.Walk u v,
    kstPathOpen ω p ∧ u.2 = -64*(k : ℤ) ∧ v.2 = -64*(k : ℤ) ∧
    u.1 ≤ -(k : ℤ)-1 ∧ (k : ℤ) ≤ v.1 ∧
    kstPathIn p (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1)}

/-- The translation spacing equals the exact odd target gap. -/
def alphaCoreBottomFactor (k : ℕ) (j : Fin 512) : PD.squareLattice ≃g PD.squareLattice :=
  kstHorizontalFactorIso (-511*(k : ℤ)+(j.val : ℤ)*(2*(k : ℤ)+1))

/-- Gluing retains the odd width and height of the contracted face box. -/
theorem alpha_core_bottom_arc_long_gluing (k : ℕ) (hk : 1 ≤ k) :
    ∃ e : Fin 512 → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' alphaCoreBottomArc k) ⊆
        horizontalRectangle (-512*(k : ℤ)-1,-64*(k : ℤ)) (1024*k+1) (128*k-1) := by
  refine ⟨alphaCoreBottomFactor k,fun j => kstHorizontalFactorIso_box _,?_⟩
  intro ω hω
  apply alpha_core_512_bottom_connections_glue k hk ω
  intro i
  obtain ⟨u,v,p,hp,hu,hv,hux,hvx,hbox⟩ := Set.mem_iInter.mp hω i
  let e := alphaCoreBottomFactor k i
  let c := -511*(k : ℤ)+(i.val : ℤ)*(2*(k : ℤ)+1)
  refine ⟨e.symm u,e.symm v,p.map e.symm.toHom,
    kstPathOpen_map_iso_inverse e ω p hp,?_,?_,?_,?_,?_⟩
  · change u.2-0 = -64*(k : ℤ)
    omega
  · change v.2-0 = -64*(k : ℤ)
    omega
  · change u.1- -c ≤ _
    dsimp [c]
    nlinarith
  · change _ ≤ v.1- -c
    dsimp [c]
    nlinarith
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    have hh := hbox b hb
    have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ 511 := by omega
    have hcl : -511*(k : ℤ) ≤ c := by
      dsimp [c]
      nlinarith [mul_nonneg hi.1 (show 0 ≤ 2*(k : ℤ)+1 by omega)]
    have hcr : c ≤ 511*(k : ℤ)+511 := by
      dsimp [c]
      nlinarith [mul_nonneg (show 0 ≤ 511-(i.val : ℤ) by omega) (show 0 ≤ 2*(k : ℤ)+1 by omega)]
    change -576*(k : ℤ) ≤ b.1- -c ∧ b.1- -c ≤ 576*(k : ℤ)+511 ∧
      -64*(k : ℤ) ≤ b.2-0 ∧ b.2-0 ≤ 64*(k : ℤ)-1
    omega

end
end PottsContinuity.PlanarTopology
