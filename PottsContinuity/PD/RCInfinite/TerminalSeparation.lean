-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/TerminalSeparation.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

open Set Finset

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

theorem walk_reachable_deleteIncidenceSet {V : Type*} {G : SimpleGraph V}
    {x y v : V} (w : G.Walk x y) (hv : v ∉ w.support) :
    (G.deleteIncidenceSet v).Reachable x y := by
  induction w with
  | nil => exact .refl _
  | @cons x y z h w ih =>
    have hx : x ≠ v := by
      intro heq
      exact hv (by simp [heq])
    have hy : y ≠ v := by
      intro heq
      exact hv (List.mem_cons_of_mem _ (heq ▸ w.start_mem_support))
    exact (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h, hx, hy⟩).reachable.trans
      (ih (fun hh => hv (List.mem_cons_of_mem _ hh)))

theorem degree_ge_three_of_separated_targets
    {V W : Type*} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hH : H.Connected) (f : H →g G) (hf : Function.Injective f)
    (v : W) (ys : Fin 3 → W) (hne : ∀ j, ys j ≠ v)
    (hsep : ∀ j k, j ≠ k →
      ¬(G.deleteIncidenceSet (f v)).Reachable (f (ys j)) (f (ys k))) :
    3 ≤ H.degree v := by
  have hfirst (j : Fin 3) : ∃ u, H.Adj v u ∧
      (G.deleteIncidenceSet (f v)).Reachable (f u) (f (ys j)) := by
    obtain ⟨p, hp⟩ := hH.exists_isPath v (ys j)
    obtain ⟨u, h, w, rfl⟩ := p.exists_eq_cons_of_ne (hne j).symm
    have hv : v ∉ w.support := (SimpleGraph.Walk.cons_isPath_iff h w).mp hp |>.2
    have havoid : f v ∉ (w.map f).support := by
      intro hmem
      have hmem' : f v ∈ w.support.map f := by
        simpa only [SimpleGraph.Walk.support_map] using hmem
      obtain ⟨z, hz, heq⟩ := List.mem_map.mp hmem'
      exact hv (hf heq ▸ hz)
    exact ⟨u, h, walk_reachable_deleteIncidenceSet (w.map f) havoid⟩
  choose u hu hreach using hfirst
  let g : Fin 3 → H.neighborSet v := fun j => ⟨u j, hu j⟩
  have hg : Function.Injective g := by
    intro j k hjk
    by_contra hne
    have heq : u j = u k := congrArg Subtype.val hjk
    exact hsep j k hne ((hreach j).symm.trans (heq ▸ hreach k))
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hc

/-- A vertex separating three distinct terminal components after its deletion.
The terminal witnesses themselves are different from the removed vertex. -/
def SeparatesThreeTerminals {V : Type*} (G : SimpleGraph V) (T : Set V) (v : V) : Prop :=
  ∃ ys : Fin 3 → V, (∀ j, G.Reachable v (ys j) ∧ ys j ∈ T ∧ ys j ≠ v) ∧
    ∀ j k, j ≠ k → ¬(G.deleteIncidenceSet v).Reachable (ys j) (ys k)

theorem separator_mem_connected_carrier {V : Type*} {G : SimpleGraph V}
    {T U : Set V} (hTU : T ⊆ U) (H : SimpleGraph U)
    (hHG : H ≤ G.induce U) (hH : H.Connected)
    {v : V} (hv : SeparatesThreeTerminals G T v) : v ∈ U := by
  by_contra hvU
  obtain ⟨ys, hys, hsep⟩ := hv
  let f : H →g G.deleteIncidenceSet v :=
    { toFun := Subtype.val
      map_rel' := fun {x y} h => SimpleGraph.deleteIncidenceSet_adj.mpr
        ⟨hHG h, fun heq => hvU (heq ▸ x.property),
          fun heq => hvU (heq ▸ y.property)⟩ }
  exact hsep 0 1 (by decide) ((hH ⟨ys 0, hTU (hys 0).2.1⟩
    ⟨ys 1, hTU (hys 1).2.1⟩).map f)

theorem separator_degree_ge_three {V : Type*} {G : SimpleGraph V}
    {T U : Set V} [Fintype U] (hTU : T ⊆ U) (H : SimpleGraph U)
    (hHG : H ≤ G.induce U) (hH : H.Connected)
    {v : V} (hv : SeparatesThreeTerminals G T v) (hvU : v ∈ U) :
    3 ≤ H.degree ⟨v, hvU⟩ := by
  obtain ⟨ys, hys, hsep⟩ := hv
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => hHG h }
  exact degree_ge_three_of_separated_targets hH f Subtype.val_injective ⟨v, hvU⟩
    (fun j => ⟨ys j, hTU (hys j).2.1⟩)
    (fun j hj => (hys j).2.2 (congrArg Subtype.val hj)) hsep

end
end PottsContinuity.PD.RCInfinite
