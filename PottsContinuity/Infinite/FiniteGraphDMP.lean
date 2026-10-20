module

public import PottsContinuity.Infinite.FiniteGraphComparison
public import PottsContinuity.PD.RCInfinite.FiniteConditioning
public import PottsContinuity.PD.RCInfinite.ExteriorClusters

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance finiteGraphDMPEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance finiteGraphDMPEdgeDecidableEq {V : Type*} [Finite V]
    (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- The boundary condition induced inside a finite induced lattice subgraph by
freezing all other edges in a larger graph is dominated by its wired vertex
boundary, provided the outer wired boundary is disjoint from the inner vertex
set. -/
theorem finite_induced_pullback_boundary_le_wired
    (S U : Finset LatticeVertex) (hSU : S ⊆ U)
    (houter : Disjoint (S : Set LatticeVertex)
      (PottsContinuity.PD.vertexBoundary U))
    (K : RemovedConfiguration (finiteLatticeGraph U)
      (subgraphRemovedEdges
        ((finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hSU))
        (finiteLatticeGraph U))) :
    (isolatedExtensionPullbackBoundary (finiteLatticeVertexEmbedding hSU)
      (frozenBoundary (frozenBoundaryCondition U 1) K.val)).partition ≤
      (frozenBoundaryCondition S 1).partition := by
  classical
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph U
  let f := finiteLatticeVertexEmbedding hSU
  let R := subgraphRemovedEdges (G.map f) H
  let external : Set (U : Set LatticeVertex) :=
    {x | x.val ∈ PottsContinuity.PD.vertexBoundary S ∨
      x.val ∉ (S : Set LatticeVertex)}
  let rel : Setoid (U : Set LatticeVertex) := {
    r := fun x y => x = y ∨ (x ∈ external ∧ y ∈ external)
    iseqv := {
      refl := fun x => Or.inl rfl
      symm := by
        intro x y h
        rcases h with h | ⟨hx, hy⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨hy, hx⟩
      trans := by
        intro x y z hxy hyz
        rcases hxy with rfl | ⟨hx, hy⟩
        · exact hyz
        · rcases hyz with rfl | ⟨_, hz⟩
          · exact Or.inr ⟨hx, hy⟩
          · exact Or.inr ⟨hx, hz⟩
    }
  }
  have hboundaryOuter : (frozenBoundaryCondition U 1).partition ≤ rel := by
    intro x y hxy
    have hwire : (BoundaryCondition.wired (frozenVertexBoundary U)).partition x y := by
      exact hxy
    have hxy' := (BoundaryCondition.wired_rel (frozenVertexBoundary U) x y).mp hwire
    rcases hxy' with hxy' | ⟨hx, hy⟩
    · exact Or.inl hxy'
    · right
      constructor
      · right
        intro hxS
        exact Set.disjoint_left.mp houter hxS
          (by simpa [frozenVertexBoundary] using hx)
      · right
        intro hyS
        exact Set.disjoint_left.mp houter hyS
          (by simpa [frozenVertexBoundary] using hy)
  have hopen : ∀ {x y : (U : Set LatticeVertex)},
      ActualConnected H K.val x y → rel.r x y := by
    intro x y hxy
    have hreach : (openGraph H K.val).reachableSetoid ≤ rel := by
      apply reachableSetoid_le_of_adj
      intro a b hab
      have hadj : H.Adj a b := openGraph_le H K.val hab
      have hopen' := (openGraph_adj H K.val a b).mp hab
      obtain ⟨e, heK, heval⟩ := hopen'
      have heR : e ∈ R := K.property heK
      have heOutside : e.val ∉ (G.map f).edgeSet :=
        (mem_subgraphRemovedEdges e).mp heR
      have hAdjLattice : squareLattice.Adj a.val b.val := by
        change H.Adj a b at hadj
        exact hadj
      have haExt : a ∈ external := by
        by_cases haS : a.val ∈ S
        · by_cases haB : a.val ∈ PottsContinuity.PD.vertexBoundary S
          · exact Or.inl haB
          · exfalso
            have hbS : b.val ∈ S := by
              by_contra hbS
              apply haB
              exact ⟨haS, b.val, hAdjLattice, hbS⟩
            let x : (S : Set LatticeVertex) := ⟨a.val, haS⟩
            let y : (S : Set LatticeVertex) := ⟨b.val, hbS⟩
            have hfx : f x = a := by
              apply Subtype.ext
              rfl
            have hfy : f y = b := by
              apply Subtype.ext
              rfl
            have hGxy : G.Adj x y := by
              change squareLattice.Adj x.val y.val
              exact hAdjLattice
            have hy : (G.map f).Adj a b := by
              have hmap : (G.map f).Adj (f x) (f y) :=
                (SimpleGraph.map_adj f G (f x) (f y)).mpr
                  ⟨x, y, hGxy, rfl, rfl⟩
              simpa only [hfx, hfy] using hmap
            apply heOutside
            rw [heval]
            exact (G.map f).mem_edgeSet.mpr hy
        · exact Or.inr haS
      have hbExt : b ∈ external := by
        by_cases hbS : b.val ∈ S
        · by_cases hbB : b.val ∈ PottsContinuity.PD.vertexBoundary S
          · exact Or.inl hbB
          · exfalso
            have haS : a.val ∈ S := by
              by_contra haS
              apply hbB
              exact ⟨hbS, a.val, hAdjLattice.symm, haS⟩
            let x : (S : Set LatticeVertex) := ⟨a.val, haS⟩
            let y : (S : Set LatticeVertex) := ⟨b.val, hbS⟩
            have hfx : f x = a := by
              apply Subtype.ext
              rfl
            have hfy : f y = b := by
              apply Subtype.ext
              rfl
            have hGxy : G.Adj x y := by
              change squareLattice.Adj x.val y.val
              exact hAdjLattice
            have hy : (G.map f).Adj a b := by
              have hmap : (G.map f).Adj (f x) (f y) :=
                (SimpleGraph.map_adj f G (f x) (f y)).mpr
                  ⟨x, y, hGxy, rfl, rfl⟩
              simpa only [hfx, hfy] using hmap
            apply heOutside
            rw [heval]
            exact (G.map f).mem_edgeSet.mpr hy
        · exact Or.inr hbS
      exact Or.inr ⟨haExt, hbExt⟩
    exact hreach hxy
  have hboundary : (frozenBoundary (frozenBoundaryCondition U 1) K.val).partition ≤ rel := by
    change componentSetoid H (frozenBoundaryCondition U 1) K.val ≤ rel
    exact componentSetoid_le H (frozenBoundaryCondition U 1) K.val rel hopen hboundaryOuter
  intro x y hxy
  have hxy' : rel.r (f x) (f y) := by
    exact hboundary ((Setoid.comap_rel f
      (frozenBoundary (frozenBoundaryCondition U 1) K.val).partition x y).mp hxy)
  rcases hxy' with hxy' | ⟨hx, hy⟩
  · exact Or.inl (f.injective hxy')
  · have hxB : x.val ∈ PottsContinuity.PD.vertexBoundary S := by
      rcases hx with hx | hx
      · exact hx
      · exact (hx x.property).elim
    have hyB : y.val ∈ PottsContinuity.PD.vertexBoundary S := by
      rcases hy with hy | hy
      · exact hy
      · exact (hy y.property).elim
    have hxB' : x ∈ frozenVertexBoundary S := by
      simpa [frozenVertexBoundary] using hxB
    have hyB' : y ∈ frozenVertexBoundary S := by
      simpa [frozenVertexBoundary] using hyB
    exact (BoundaryCondition.wired_rel (frozenVertexBoundary S) x y).mpr
      (Or.inr ⟨hxB', hyB'⟩)

/-- Exterior-state projection for a general finite graph embedding. -/
def embeddedOutsideState {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (_hGH : G.map f ≤ H) (C : Configuration H) :
    RemovedConfiguration H (subgraphRemovedEdges (G.map f) H) :=
  (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2

/-- Finite joint DMP directly from a boundary-partition comparison, for any
finite graph embedding. -/
theorem embedded_joint_le_boundary_order {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (hGH : G.map f ≤ H)
    (θ : PottsContinuity.PD.FK.Parameters)
    (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (A : Set (Configuration G)) (hA : IsUpperSet A)
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
        η.partition)
    (T : Set (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))) :
    (measure H θ ξ
      ((embeddedConfigurationRestriction G H f hGH ⁻¹' A) ∩
        (embeddedOutsideState G H f hGH ⁻¹' T))).toReal ≤
      (measure G θ η A).toReal *
        (measure H θ ξ (embeddedOutsideState G H f hGH ⁻¹' T)).toReal := by
  exact PottsContinuity.PD.RCInfinite.embedded_joint_le
    G H f hGH θ ξ η A hA hpart T

end
end PottsContinuity.Infinite
