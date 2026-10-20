module

public import PottsContinuity.Thm3.OuterCircuit.FiniteSourceSelector

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.FKC

noncomputable section

theorem outerCircuitPolygon_vertex_mem_host_of_radius {n m : ℕ}
    (P : FKC.LatticePolygon m)
    (hrad : ∀ i : ZMod (m + 3),
      max |(P.vertex i).1| |(P.vertex i).2| ≤ (14*n : ℤ)) :
    ∀ i : ZMod (m + 3), P.vertex i ∈ PottsContinuity.PD.box (56*n) := by
  intro i
  have hx := le_trans (le_max_left |(P.vertex i).1| |(P.vertex i).2|) (hrad i)
  have hy := le_trans (le_max_right |(P.vertex i).1| |(P.vertex i).2|) (hrad i)
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  simp only [PottsContinuity.PD.box, Finset.mem_product,
    Finset.mem_Icc]
  constructor <;> constructor <;> omega

theorem outerCircuitPolygon_index_lt_host_card {n m : ℕ}
    (P : FKC.LatticePolygon m)
    (hvertices : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.PD.box (56*n)) :
    m < Fintype.card (OuterCircuitHostVertex n) + 1 := by
  let f : ZMod (m + 3) → OuterCircuitHostVertex n := fun i =>
    ⟨P.vertex i, hvertices i⟩
  have hfinj : Function.Injective f := by
    intro i j h
    apply P.vertex_injective
    exact congrArg Subtype.val h
  have hcard : Fintype.card (ZMod (m + 3)) ≤
      Fintype.card (OuterCircuitHostVertex n) := Fintype.card_le_of_injective f hfinj
  have hverticesCount : m + 3 ≤ Fintype.card (OuterCircuitHostVertex n) := by
    simpa using hcard
  omega

noncomputable def outerCircuitPolygonCodeOfHostPolygon {n m : ℕ}
    (P : FKC.LatticePolygon m)
    (hvertices : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.PD.box (56*n)) :
    OuterCircuitPolygonCode n := by
  let mFin : Fin (Fintype.card (OuterCircuitHostVertex n) + 1) :=
    ⟨m, outerCircuitPolygon_index_lt_host_card P hvertices⟩
  exact ⟨mFin, ⟨P, hvertices⟩⟩

theorem outerCircuitCodePolygon_of_hostPolygon_eq {n m : ℕ}
    (P : FKC.LatticePolygon m)
    (hvertices : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.PD.box (56*n)) :
    outerCircuitCodePolygon (outerCircuitPolygonCodeOfHostPolygon P hvertices) = P := rfl

end
end PottsContinuity.OuterCircuit
