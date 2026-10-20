module

public import PottsContinuity.Thm3.OuterCircuit.PolygonWalkBridge

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.FKC

noncomputable section

/-- The source box carrier used for finite indexing of candidate polygons. -/
abbrev OuterCircuitHostVertex (n : ℕ) :=
  {z : PD.FK.LatticeVertex // z ∈
    (PottsContinuity.box (56*n) : Set PD.FK.LatticeVertex)}

private theorem outerCircuitSourceBox_mem_latticeBox (n : ℕ)
    (z : PD.FK.LatticeVertex) :
    z ∈ box (56*n) ↔ z ∈ PD.FK.latticeBox (0, 0) (56*n) := by
  simp [PottsContinuity.box, PD.FK.latticeBox,
    Finset.mem_product, Finset.mem_Icc, zero_sub, zero_add]

 theorem outerCircuitHost_mem_latticeBox (n : ℕ)
    (z : PD.FK.LatticeVertex) :
    z ∈ (PottsContinuity.box (56*n) : Set PD.FK.LatticeVertex) ↔
      z ∈ PD.FK.latticeBox (0, 0) (56*n) := by
  constructor
  · intro hz
    exact (outerCircuitSourceBox_mem_latticeBox n z).mp
      (Finset.mem_coe.mp hz)
  · intro hz
    exact Finset.mem_coe.mpr
      ((outerCircuitSourceBox_mem_latticeBox n z).mpr hz)

def outerCircuitHostVertexEquiv (n : ℕ) :
    OuterCircuitHostVertex n ≃ PD.FK.BoxVertex (0, 0) (56*n) where
  toFun x := ⟨x.val, (outerCircuitHost_mem_latticeBox n x.val).mp x.property⟩
  invFun x := ⟨x.val, (outerCircuitHost_mem_latticeBox n x.val).mpr x.property⟩
  left_inv _x := Subtype.ext rfl
  right_inv _x := Subtype.ext rfl

noncomputable instance outerCircuitHostVertexFintype (n : ℕ) :
    Fintype (OuterCircuitHostVertex n) :=
  Fintype.ofEquiv (PD.FK.BoxVertex (0, 0) (56*n))
    (outerCircuitHostVertexEquiv n).symm

/-- A polygon whose ordered vertices all lie in the source host box. -/
abbrev OuterCircuitBoundedPolygon (n m : ℕ) :=
  {P : FKC.LatticePolygon m // ∀ i : ZMod (m + 3), P.vertex i ∈ box (56*n)}

private theorem outerCircuitPolygon_eq_of_vertex_eq {m : ℕ}
    {P Q : FKC.LatticePolygon m} (h : P.vertex = Q.vertex) : P = Q := by
  cases P with
  | mk vertex₁ injective₁ adjacent₁ =>
    cases Q with
    | mk vertex₂ injective₂ adjacent₂ =>
      change vertex₁ = vertex₂ at h
      cases h
      rfl

 theorem outerCircuitBoundedPolygon_finite (n m : ℕ) :
    Finite (OuterCircuitBoundedPolygon n m) := by
  classical
  let f : OuterCircuitBoundedPolygon n m →
      (ZMod (m + 3) → OuterCircuitHostVertex n) := fun P i =>
    ⟨P.1.vertex i, Finset.mem_coe.mpr (P.2 i)⟩
  apply Finite.of_injective f
  intro P Q h
  apply Subtype.ext
  apply outerCircuitPolygon_eq_of_vertex_eq
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- A finite code family of every source-box polygon, with enough indices for
its full simple vertex list. -/
abbrev OuterCircuitPolygonCode (n : ℕ) :=
  Σ m : Fin (Fintype.card (OuterCircuitHostVertex n) + 1),
    OuterCircuitBoundedPolygon n m.val

noncomputable instance outerCircuitPolygonCodeFintype (n : ℕ) :
    Fintype (OuterCircuitPolygonCode n) := by
  classical
  letI : ∀ m : Fin (Fintype.card (OuterCircuitHostVertex n) + 1),
      Finite (OuterCircuitBoundedPolygon n m.val) := fun m =>
    outerCircuitBoundedPolygon_finite n m.val
  exact Fintype.ofFinite _

/-- The polygon carried by one finite source-box code. -/
def outerCircuitCodePolygon {n : ℕ} (i : OuterCircuitPolygonCode n) :
    FKC.LatticePolygon i.1.val := i.2.1

/-- Every vertex of a decoded code lies in the source host box. -/
theorem outerCircuitCodePolygon_vertex_mem {n : ℕ}
    (i : OuterCircuitPolygonCode n) (j : ZMod (i.1.val + 3)) :
    (outerCircuitCodePolygon i).vertex j ∈ box (56*n) := i.2.2 j

end
end PottsContinuity.OuterCircuit
