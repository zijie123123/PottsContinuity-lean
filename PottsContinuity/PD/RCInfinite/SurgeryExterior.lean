-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/SurgeryExterior.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.TreeSurgery
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

theorem exteriorReachable_distinct_endpoints_outside {n : ℕ}
    (ω : LatticeConfiguration) {x y : LatticeVertex}
    (hxy : (exteriorOpenGraph ω n).Reachable x y) (hne : x ≠ y) :
    x ∉ latticeBox (0, 0) n ∧ y ∉ latticeBox (0, 0) n := by
  obtain ⟨p, hp⟩ := hxy.exists_isPath
  obtain ⟨z, hxz, _, rfl⟩ := p.exists_eq_cons_of_ne hne
  have hxout : x ∉ latticeBox (0, 0) n :=
    (exteriorOpenGraph_adj ω n x z).mp hxz |>.2.1
  have hyout : y ∉ latticeBox (0, 0) n := by
    obtain ⟨q, hq⟩ := hxy.symm.exists_isPath
    obtain ⟨z, hyz, _, rfl⟩ := q.exists_eq_cons_of_ne hne.symm
    exact (exteriorOpenGraph_adj ω n y z).mp hyz |>.2.1
  exact ⟨hxout, hyout⟩

theorem exteriorOpenGraph_le_tree_surgery {n : ℕ}
    (exits : Fin 3 → BoxExit n)
    (hdistinct : Function.Injective (fun j => boxExitOutside (exits j)))
    (U : Finset (BoxExitCarrier n)) (H : SimpleGraph (U : Set (BoxExitCarrier n)))
    (ω : LatticeConfiguration) :
    exteriorOpenGraph ω n ≤
      rcInfiniteOpenGraph
        (setEdges (boxIncidentEdges n)
          (boxTreeEdgeState H (boxExitSubembedding exits hdistinct U)) ω) := by
  classical
  let f := boxExitSubembedding exits hdistinct U
  let ξ := boxTreeEdgeState H f
  intro x y hxy
  obtain ⟨hOpen, hxout, hyout⟩ := (exteriorOpenGraph_adj ω n x y).mp hxy
  obtain ⟨he, hstate⟩ := (rcInfiniteOpenGraph_adj ω x y).mp hOpen
  let e : Edge := ⟨s(x, y), he⟩
  have hnotF : e ∉ boxIncidentEdges n := by
    intro heF
    obtain ⟨_, ⟨z, hz, hze⟩⟩ := (mem_boxIncidentEdges n e).mp heF
    have hze' : z = x ∨ z = y := by
      change z ∈ s(x, y) at hze
      exact (Sym2.mem_iff).mp hze
    rcases hze' with hzx | hzy
    · exact hxout (hzx ▸ hz)
    · exact hyout (hzy ▸ hz)
  have hprescribed : setEdges (boxIncidentEdges n) ξ ω e = true := by
    simpa [setEdges, hnotF] using hstate
  exact (rcInfiniteOpenGraph_adj (setEdges (boxIncidentEdges n) ξ ω) x y).mpr
    ⟨he, hprescribed⟩

theorem exteriorOpenGraph_deleted_le_tree_surgery_deleted {n : ℕ}
    (exits : Fin 3 → BoxExit n)
    (hdistinct : Function.Injective (fun j => boxExitOutside (exits j)))
    (U : Finset (BoxExitCarrier n)) (H : SimpleGraph (U : Set (BoxExitCarrier n)))
    (ω : LatticeConfiguration) (v : LatticeVertex) :
    (exteriorOpenGraph ω n).deleteIncidenceSet v ≤
      (rcInfiniteOpenGraph
        (setEdges (boxIncidentEdges n)
          (boxTreeEdgeState H (boxExitSubembedding exits hdistinct U)) ω)).deleteIncidenceSet v := by
  intro x y hxy
  obtain ⟨hOpen, hxv, hyv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hxy
  exact SimpleGraph.deleteIncidenceSet_adj.mpr
    ⟨exteriorOpenGraph_le_tree_surgery exits hdistinct U H ω hOpen, hxv, hyv⟩

end
end PottsContinuity.PD.RCInfinite
