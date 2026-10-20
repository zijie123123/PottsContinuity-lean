module

public import PottsContinuity.PD.RCInfinite.BoxConnector
public import PottsContinuity.PD.FK.BoxTranslation
public import PottsContinuity.PD.Duality.RayIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Constancy of the dual ray index throughout a primal box -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality

/-- Translation transports connectivity of the origin box to any lattice box. -/
theorem translated_boxGraph_connected (c : LatticeVertex) (r : ℕ) :
    (boxGraph c r).Connected := by
  let e : boxGraph (0,0) r ≃g boxGraph c r := by
    have hc : latticeTranslate c (0,0) = c := by ext <;> simp [latticeTranslate]
    exact hc ▸ boxVertexTranslationIso c (0,0) r
  let BoxRayIndex_nonempty : Nonempty (BoxVertex c r) :=
    ⟨⟨c, center_mem_latticeBox c r⟩⟩
  refine ⟨?_⟩
  intro u v
  have h := (PD.RCInfinite.boxGraph_connected r).preconnected (e.symm u) (e.symm v)
  have hmap := h.map e.toHom
  change (boxGraph c r).Reachable (e (e.symm u)) (e (e.symm v)) at hmap
  exact (e.toEquiv.apply_symm_apply u) ▸ (e.toEquiv.apply_symm_apply v) ▸ hmap

/-- If the dual walk crosses no internal primal edge of a box, its ray index
is the same at all vertices of that box, including its boundary. -/
theorem closedWalk_rayIndex_eq_on_box
    (c : LatticeVertex) (r : ℕ) {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z)
    (havoid : ∀ b : LatticeBond, b.source ∈ latticeBox c r →
      b.target ∈ latticeBox c r → (dualBondOfPrimal b).toSym2 ∉ p.edges)
    (u v : LatticeVertex) (hu : u ∈ latticeBox c r) (hv : v ∈ latticeBox c r) :
    rayIndex u p = rayIndex v p := by
  let φ : boxGraph c r →g circuitAvoidanceGraph p :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        refine ⟨hab, ?_⟩
        intro d hd
        have hs : d.source ∈ latticeBox c r := by
          have hh : d.source ∈ s(a.val,b.val) := hd ▸ (by simp [LatticeBond.toSym2])
          rcases Sym2.mem_iff.mp hh with h | h
          · exact h ▸ a.property
          · exact h ▸ b.property
        have ht : d.target ∈ latticeBox c r := by
          have hh : d.target ∈ s(a.val,b.val) := hd ▸ (by simp [LatticeBond.toSym2])
          rcases Sym2.mem_iff.mp hh with h | h
          · exact h ▸ a.property
          · exact h ▸ b.property
        exact havoid d hs ht }
  exact rayIndex_eq_of_avoidance_reachable p
    (((translated_boxGraph_connected c r).preconnected ⟨u,hu⟩ ⟨v,hv⟩).map φ)

end PottsContinuity.RSW
