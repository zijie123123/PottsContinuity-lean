-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/TreeCounting.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

open Finset

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

/-- A finite nontrivial tree has at least two more leaves than vertices of
degree at least three. This is the deterministic degree count in the
encounter-point argument. -/
theorem tree_branch_card_add_two_le_leaf_card {V : Type*} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.IsTree) :
    (univ.filter fun v => 3 ≤ G.degree v).card + 2 ≤
      (univ.filter fun v => G.degree v = 1).card := by
  have hpos (v : V) : 0 < G.degree v :=
    lt_of_lt_of_le hG.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree v)
  have hpoint (v : V) :
      2 + (if 3 ≤ G.degree v then 1 else 0) ≤
        G.degree v + (if G.degree v = 1 then 1 else 0) := by
    have := hpos v
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul,
    sum_boole, Nat.cast_id] at hsum
  have hdegrees := G.sum_degrees_eq_twice_card_edges
  have hcard := hG.card_edgeFinset
  omega

/-- If all leaves are terminals, the number of branching vertices is bounded
by the number of terminals. -/
theorem tree_branch_card_le_terminals {V : Type*} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.IsTree) (T : Finset V)
    (hleaf : ∀ v, G.degree v = 1 → v ∈ T) :
    (univ.filter fun v => 3 ≤ G.degree v).card + 2 ≤ T.card := by
  have hsub : (univ.filter fun v => G.degree v = 1) ⊆ T := by
    intro v hv
    exact hleaf v (mem_filter.mp hv).2
  exact (tree_branch_card_add_two_le_leaf_card G hG).trans (card_le_card hsub)

/-- A connected finite graph has a tree connecting any prescribed terminals,
with no extraneous leaves. The vertex set may shrink. -/
theorem exists_terminal_tree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (T : Finset V) :
    ∃ U : Finset V, T ⊆ U ∧ ∃ H : SimpleGraph (U : Set V),
      H ≤ G.induce (U : Set V) ∧ H.IsTree ∧
        ∀ v : (U : Set V), H.degree v = 1 → v.val ∈ T := by
  have hex : ∃ n : ℕ, ∃ U : Finset V,
      T ⊆ U ∧ (G.induce (U : Set V)).Connected ∧ U.card = n := by
    refine ⟨univ.card, univ, subset_univ _, ?_, rfl⟩
    let f : G →g G.induce ((univ : Finset V) : Set V) :=
      { toFun := fun v => ⟨v, mem_univ v⟩
        map_rel' := fun h => h }
    exact hG.map f (fun z => ⟨z.val, Subtype.ext rfl⟩)
  obtain ⟨U, hTU, hU, hcard⟩ := Nat.find_spec hex
  obtain ⟨H, hHG, hH⟩ := hU.exists_isTree_le
  refine ⟨U, hTU, H, hHG, hH, ?_⟩
  intro v hv
  by_contra hvT
  have hsmallconn : (G.induce ((U.erase v.val : Finset V) : Set V)).Connected := by
    let f : H.induce {v}ᶜ →g G.induce ((U.erase v.val : Finset V) : Set V) :=
      { toFun := fun z => ⟨z.val.val, Finset.mem_erase.mpr ⟨by
          intro heq
          exact z.property (Subtype.ext heq), z.val.property⟩⟩
        map_rel' := fun h => hHG h }
    have hf : Function.Surjective f := by
      intro z
      have hz := Finset.mem_erase.mp z.property
      refine ⟨⟨⟨z.val, hz.2⟩, ?_⟩, rfl⟩
      intro heq
      exact hz.1 (congrArg Subtype.val heq)
    exact (hH.connected.induce_compl_singleton_of_degree_eq_one hv).map f hf
  have hTsmall : T ⊆ U.erase v.val := by
    intro x hx
    exact mem_erase.mpr ⟨fun heq => hvT (heq ▸ hx), hTU hx⟩
  have hmin := Nat.find_min' hex
    (show ∃ W : Finset V, T ⊆ W ∧ (G.induce (W : Set V)).Connected ∧
      W.card = (U.erase v.val).card from ⟨_, hTsmall, hsmallconn, rfl⟩)
  have hlt : (U.erase v.val).card < U.card := card_erase_lt_of_mem v.property
  omega

end
end PottsContinuity.PD.RCInfinite
