-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/UnionReachability.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
noncomputable section

/-- If the exterior graph cannot connect two different points of the finite
graph's support, adding it creates no new reachability between support points. -/
theorem reachable_of_sup_of_external_components
    {V : Type*} (G E : SimpleGraph V) (S : Set V)
    (hG : ∀ ⦃x y⦄, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hE : ∀ ⦃x y⦄, x ∈ S → y ∈ S → E.Reachable x y → x = y)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : (G ⊔ E).Reachable x y) : G.Reachable x y := by
  obtain ⟨w⟩ := hxy
  have normalize {a b : V} (p : (G ⊔ E).Walk a b) :
      (a ∈ S → b ∈ S → G.Reachable a b) ∧
      (a ∉ S → b ∈ S → ∃ t, t ∈ S ∧ E.Reachable t a ∧ G.Reachable t b) := by
    induction p with
    | nil =>
        constructor
        · intro ha hb
          exact .refl _
        · intro ha hb
          exact (ha hb).elim
    | @cons a z b haz p ih =>
        constructor
        · intro ha hb
          rcases (SimpleGraph.sup_adj G E a z).mp haz with hGadj | hEadj
          · have hz := (hG hGadj).2
            exact hGadj.reachable.trans (ih.1 hz hb)
          · by_cases hz : z ∈ S
            · have hab : a = z := hE ha hz hEadj.reachable
              subst z
              exact ih.1 ha hb
            · obtain ⟨t, ht, htz, htb⟩ := ih.2 hz hb
              have hat : E.Reachable a t := hEadj.reachable.trans htz.symm
              have hatEq : a = t := hE ha ht hat
              exact hatEq ▸ htb
        · intro ha hb
          rcases (SimpleGraph.sup_adj G E a z).mp haz with hGadj | hEadj
          · exact (ha (hG hGadj).1).elim
          · by_cases hz : z ∈ S
            · exact ⟨z, hz, hEadj.reachable.symm, ih.1 hz hb⟩
            · obtain ⟨t, ht, htz, htb⟩ := ih.2 hz hb
              exact ⟨t, ht, htz.trans hEadj.reachable.symm, htb⟩
  exact (normalize w).1 hx hy

end
end PottsContinuity.PD.RCInfinite
