module

public import PottsContinuity.BD12.FiniteDomainOneArm
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! A one-arm event is determined inside any induced subdomain containing
the entire target-radius ball, independently of the exterior configuration. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- Exact event restriction in arbitrary nested finite induced lattice domains. -/
theorem finiteDomainOneArmEvent_restriction_iff {S T : Finset LatticeVertex}
    (hST : S ⊆ T) (c : LatticeVertex) (n : ℕ) (hball : latticeBox c n ⊆ S)
    (o : (S : Set LatticeVertex)) (ho : o.val = c)
    (A : Configuration (finiteLatticeGraph T)) :
    A ∈ finiteDomainOneArmEvent T c (finiteLatticeVertexEmbedding hST o) n ↔
      embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
        (finiteLatticeVertexEmbedding hST) (finiteLatticeGraph_map_le hST) A ∈
          finiteDomainOneArmEvent S c o n := by
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph T
  let f := finiteLatticeVertexEmbedding hST
  let hGH := finiteLatticeGraph_map_le hST
  constructor
  · rintro ⟨b, hb, hconn⟩
    have hstart : latticeRadius c (f o).val ≤ n := by
      change latticeRadius c o.val ≤ n
      rw [ho, latticeRadius_self]
      exact Nat.zero_le n
    obtain ⟨z, hz, hzconn⟩ := reachable_radius_inside_induced_ball
      (fun v : (T : Set LatticeVertex) => latticeRadius c v.val)
      (fun h => latticeRadius_step c ((FKC.FiniteFK.openGraph_le H A) h)) hconn n hstart hb.ge
    let hom : (FKC.FiniteFK.openGraph H A).induce {v | latticeRadius c v.val ≤ n} →g
        FKC.FiniteFK.openGraph G (embeddedConfigurationRestriction G H f hGH A) := {
      toFun := fun v => ⟨v.val.val, hball ((latticeRadius_le_iff_mem_box c v.val.val n).mp v.property)⟩
      map_rel' := by
        intro x y hxy
        have hinner : G.Adj
            ⟨x.val.val, hball ((latticeRadius_le_iff_mem_box c x.val.val n).mp x.property)⟩
            ⟨y.val.val, hball ((latticeRadius_le_iff_mem_box c y.val.val n).mp y.property)⟩ :=
          (FKC.FiniteFK.openGraph_le H A) hxy
        exact (embeddedOpenRestriction_adj G H f hGH A _ _ hinner).mpr hxy }
    exact ⟨hom z, hz, hzconn.map hom⟩
  · rintro ⟨b, hb, hconn⟩
    exact ⟨f b, hb, embeddedOpenRestriction_connected_map G H f hGH A hconn⟩

/-- Equality of the literal event preimage, with no probability-law premise. -/
theorem finiteDomainOneArmEvent_preimage {S T : Finset LatticeVertex}
    (hST : S ⊆ T) (c : LatticeVertex) (n : ℕ) (hball : latticeBox c n ⊆ S)
    (o : (S : Set LatticeVertex)) (ho : o.val = c) :
    (fun A => embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
      (finiteLatticeVertexEmbedding hST) (finiteLatticeGraph_map_le hST) A) ⁻¹'
        finiteDomainOneArmEvent S c o n =
      finiteDomainOneArmEvent T c (finiteLatticeVertexEmbedding hST o) n := by
  ext A
  exact (finiteDomainOneArmEvent_restriction_iff hST c n hball o ho A).symm

end
end PottsContinuity.BD12
