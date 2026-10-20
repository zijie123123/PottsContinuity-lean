module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card

/-! # Nontrivial induced components of a connected four-port graph -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- In a connected graph with at most four vertices, every two edges of
an induced subgraph belong to the same component. Isolated ports are allowed. -/
theorem induced_four_port_edges_connected {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Preconnected) (hcard : Fintype.card V ≤ 4)
    (U : Set V) (a b c d : U)
    (hab : (G.induce U).Adj a b) (hcd : (G.induce U).Adj c d) :
    (G.induce U).Reachable a c := by
  classical
  by_contra hn
  have habN : a ≠ b := hab.ne
  have hcdN : c ≠ d := hcd.ne
  have hacN : a ≠ c := fun h => hn (h ▸ SimpleGraph.Reachable.refl a)
  have hadN : a ≠ d := by
    intro h
    subst d
    exact hn hcd.symm.reachable
  have hbcN : b ≠ c := by
    intro h
    subst c
    exact hn hab.reachable
  have hbdN : b ≠ d := by
    intro h
    subst d
    exact hn (hab.reachable.trans hcd.symm.reachable)
  have habV : a.val ≠ b.val := fun h => habN (Subtype.ext h)
  have hacV : a.val ≠ c.val := fun h => hacN (Subtype.ext h)
  have hadV : a.val ≠ d.val := fun h => hadN (Subtype.ext h)
  have hbcV : b.val ≠ c.val := fun h => hbcN (Subtype.ext h)
  have hbdV : b.val ≠ d.val := fun h => hbdN (Subtype.ext h)
  have hcdV : c.val ≠ d.val := fun h => hcdN (Subtype.ext h)
  have hfour : ({a.val,b.val,c.val,d.val} : Finset V).card = 4 := by
    simp [habV,hacV,hadV,hbcV,hbdV,hcdV,
      ]
  have hall : ({a.val,b.val,c.val,d.val} : Finset V) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [hfour,Finset.card_univ] using hcard
  have hU (x : V) : x ∈ U := by
    have hx : x ∈ ({a.val,b.val,c.val,d.val} : Finset V) := hall.symm ▸ Finset.mem_univ x
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact a.property
    · exact b.property
    · exact c.property
    · exact d.property
  obtain ⟨p⟩ := hG a.val c.val
  exact hn ⟨p.induce U (fun x _ => hU x)⟩

end
end PottsContinuity.Thm3.Prop4
