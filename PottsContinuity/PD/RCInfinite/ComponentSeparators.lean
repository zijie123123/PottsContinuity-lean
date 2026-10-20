-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ComponentSeparators.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ComponentCounting
public import PottsContinuity.PD.RCInfinite.TerminalCounting

@[expose] public section

open Finset

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

/-- Separators in each connected component are controlled by the terminals
from that component. -/
theorem component_separator_part_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.ConnectedComponent] (T : Finset V)
    (c : G.ConnectedComponent) :
    (componentPart G (separatingTerminals G (T : Set V)) c).card ≤
      (componentPart G T c).card := by
  classical
  let E := componentPart G (separatingTerminals G (T : Set V)) c
  let Q := componentPart G T c
  let TC := componentPartSubtype G T c
  let LC := separatingTerminals c.toSimpleGraph (TC : Set c)
  by_cases hE : E.Nonempty
  · obtain ⟨v, hv⟩ := hE
    have hglobal : SeparatesThreeTerminals G (T : Set V) v := by
      simpa only [E, componentPart, separatingTerminals, Finset.mem_filter,
        Finset.mem_univ, true_and] using (Finset.mem_filter.mp hv).1
    have hvc : G.connectedComponentMk v = c := (Finset.mem_filter.mp hv).2
    obtain ⟨ys, hys, hsep⟩ := hglobal
    have hycc (j : Fin 3) : G.connectedComponentMk (ys j) = c :=
      (SimpleGraph.ConnectedComponent.sound (hys j).1).symm.trans hvc
    let y : Fin 3 → c := fun j => ⟨ys j, hycc j⟩
    have hyT (j : Fin 3) : y j ∈ TC := by
      change y j ∈ componentPartSubtype G T c
      simp only [componentPartSubtype, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hys j).2.1
    let hmap :
        (c.toSimpleGraph.deleteIncidenceSet ⟨v, hvc⟩) →g G.deleteIncidenceSet v := by
      refine { toFun := fun z => z.val, map_rel' := ?_ }
      intro x z hxz
      rw [SimpleGraph.deleteIncidenceSet_adj] at hxz ⊢
      exact ⟨(SimpleGraph.ConnectedComponent.toSimpleGraph_hom c).map_rel hxz.1,
        fun heq => hxz.2.1 (Subtype.ext heq),
        fun heq => hxz.2.2 (Subtype.ext heq)⟩
    have hsepLocal (j k : Fin 3) (hjk : j ≠ k) :
        ¬(c.toSimpleGraph.deleteIncidenceSet ⟨v, hvc⟩).Reachable (y j) (y k) := by
      intro hreach
      have hmapped := hreach.map hmap
      have hmapped' : (G.deleteIncidenceSet v).Reachable (ys j) (ys k) := by
        simpa [hmap, y] using hmapped
      exact hsep j k hjk hmapped'
    have hdistinct (j k : Fin 3) (hjk : j ≠ k) : y j ≠ y k := by
      intro heq
      have hEq : ys j = ys k := congrArg Subtype.val heq
      have hreach : (G.deleteIncidenceSet v).Reachable (ys j) (ys k) := by
        simpa only [hEq] using (SimpleGraph.Reachable.refl (ys j) :
          (G.deleteIncidenceSet v).Reachable (ys j) (ys j))
      exact hsep j k hjk hreach
    have hTC_two : 2 ≤ TC.card := by
      let f : Fin 3 → TC := fun j => ⟨y j, hyT j⟩
      have hf : Function.Injective f := by
        intro j k heq
        by_contra hjk
        exact hdistinct j k hjk (congrArg (fun z : TC => z.val) heq)
      have hc := Fintype.card_le_of_injective f hf
      have hc' : 3 ≤ TC.card := by simpa only [Fintype.card_fin, Fintype.card_coe] using hc
      omega
    have hlocal : LC.card + 2 ≤ TC.card := by
      have := terminal_separator_card_add_two_le c.toSimpleGraph
        (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c) TC hTC_two
      simpa only [LC, separatingTerminals] using this
    let f : E → LC := fun x => by
      have hxc : G.connectedComponentMk x.val = c := (Finset.mem_filter.mp x.property).2
      have hxglobal : SeparatesThreeTerminals G (T : Set V) x.val := by
        simpa only [E, componentPart, separatingTerminals, Finset.mem_filter,
          Finset.mem_univ, true_and] using (Finset.mem_filter.mp x.property).1
      refine ⟨⟨x.val, hxc⟩, ?_⟩
      obtain ⟨zs, hzs, hzsSep⟩ := hxglobal
      have hzcc (j : Fin 3) : G.connectedComponentMk (zs j) = c :=
        (SimpleGraph.ConnectedComponent.sound (hzs j).1).symm.trans hxc
      let z : Fin 3 → c := fun j => ⟨zs j, hzcc j⟩
      have hzT (j : Fin 3) : z j ∈ TC := by
        change z j ∈ componentPartSubtype G T c
        simp only [componentPartSubtype, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hzs j).2.1
      let hmapx :
          (c.toSimpleGraph.deleteIncidenceSet ⟨x.val, hxc⟩) →g G.deleteIncidenceSet x.val := by
        refine { toFun := fun w => w.val, map_rel' := ?_ }
        intro a b hab
        rw [SimpleGraph.deleteIncidenceSet_adj] at hab ⊢
        exact ⟨(SimpleGraph.ConnectedComponent.toSimpleGraph_hom c).map_rel hab.1,
          fun heq => hab.2.1 (Subtype.ext heq),
          fun heq => hab.2.2 (Subtype.ext heq)⟩
      have hsepX (j k : Fin 3) (hjk : j ≠ k) :
          ¬(c.toSimpleGraph.deleteIncidenceSet ⟨x.val, hxc⟩).Reachable (z j) (z k) := by
        intro hreach
        have hmapped := hreach.map hmapx
        have hmapped' : (G.deleteIncidenceSet x.val).Reachable (zs j) (zs k) := by
          simpa [hmapx, z] using hmapped
        exact hzsSep j k hjk hmapped'
      have hloc : SeparatesThreeTerminals c.toSimpleGraph (TC : Set c) ⟨x.val, hxc⟩ := by
        refine ⟨z, ?_, hsepX⟩
        intro j
        refine ⟨SimpleGraph.ConnectedComponent.reachable_toSimpleGraph c hxc (hzcc j),
          hzT j, ?_⟩
        intro heq
        exact (hzs j).2.2 (congrArg Subtype.val heq)
      simpa only [LC, separatingTerminals, Finset.mem_filter,
        Finset.mem_univ, true_and] using hloc
    have hf : Function.Injective f := by
      intro x z h
      apply Subtype.ext
      simpa only [f] using congrArg (fun w : LC => w.val.val) h
    have hc := Fintype.card_le_of_injective f hf
    have hc' : E.card ≤ LC.card := by simpa only [Fintype.card_coe] using hc
    have hcard : TC.card = Q.card := by simpa only [TC, Q] using componentPartSubtype_card G T c
    calc
      E.card ≤ LC.card := hc'
      _ ≤ TC.card := by omega
      _ = Q.card := hcard
  · have hzero : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    simp [E, hzero]

theorem finite_graph_terminal_separator_card_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.ConnectedComponent] (T : Finset V) :
    (separatingTerminals G (T : Set V)).card ≤ T.card := by
  calc
    (separatingTerminals G (T : Set V)).card =
        ∑ c : G.ConnectedComponent,
          (componentPart G (separatingTerminals G (T : Set V)) c).card :=
      (sum_componentPart_card G _).symm
    _ ≤ ∑ c : G.ConnectedComponent, (componentPart G T c).card := by
      apply Finset.sum_le_sum
      intro c hc
      exact component_separator_part_le G T c
    _ = T.card := sum_componentPart_card G T

end
end PottsContinuity.PD.RCInfinite
