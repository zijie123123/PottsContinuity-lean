module

public import PottsContinuity.Thm3.Prop4.RadiusTubeSurgery
public import PottsContinuity.Thm3.RSW.ErasureGraph

/-!
# Revealing every original edge of the literal Euclidean tube

The revealed set contains exactly the original edges with both endpoints
in the tube. Its restricted connection has actual tube-confined witnesses.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance tubeRevealEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance tubeRevealEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _

/-- Erasing to an induced region is intersection with its all-open edge set. -/
theorem induced_erasure_eq_inter_all_open {V : Type*} [Finite V] (G : SimpleGraph V)
    (S : Set V) (A : Configuration G) :
    RSW.inducedConfigurationErasure S A =
      A ∩ RSW.inducedConfigurationErasure S (Finset.univ : Configuration G) := by
  classical
  ext e
  simp only [RSW.mem_inducedConfigurationErasure,Finset.mem_inter,Finset.mem_univ,true_and]

/-- At a retained root, restriction to an induced region is exactly existence
of an original open walk confined to that region, including the length-zero case. -/
theorem actualConnected_erasure_iff_confined_walk {V : Type*} [Finite V] (G : SimpleGraph V)
    (S : Set V) (A : Configuration G) (a b : V) (ha : a ∈ S) :
    ActualConnected G (RSW.inducedConfigurationErasure S A) a b ↔
      ∃ p : (openGraph G A).Walk a b, ∀ z ∈ p.support, z ∈ S := by
  classical
  constructor
  · rintro ⟨p⟩
    have hsupport : ∀ z ∈ p.support, z ∈ S := by
      intro z hz
      by_contra hzout
      obtain ⟨d,_,_,hdout⟩ := (p.takeUntil z hz).exists_boundary_dart S ha hzout
      exact hdout ((RSW.openGraph_inducedConfigurationErasure_adj S A _ _).mp d.adj).2.2
    refine ⟨p.mapLe (openGraph_mono (RSW.inducedConfigurationErasure_subset S A)),?_⟩
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hsupport
  · rintro ⟨p,hp⟩
    let f : (openGraph G A).induce S →g openGraph G (RSW.inducedConfigurationErasure S A) :=
      ⟨Subtype.val,fun {x y} hxy =>
        (RSW.openGraph_inducedConfigurationErasure_adj S A x.val y.val).mpr
          ⟨hxy,x.property,y.property⟩⟩
    exact ⟨(p.induce S hp).map f⟩

/-- Exactly all original box bonds whose endpoints lie in the actual tube. -/
def radiusTubeRevealedEdges (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    Configuration (squareLattice.induce (box n : Set LatticeVertex)) :=
  RSW.inducedConfigurationErasure {z | z.val ∈ radiusTube n r u v} Finset.univ

/-- Membership in the full tube reveal means that both original endpoints
belong to the literal tube, on the entire original box edge carrier. -/
theorem mem_radiusTubeRevealedEdges (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (e : (squareLattice.induce (box n : Set LatticeVertex)).edgeSet) :
    e ∈ radiusTubeRevealedEdges n r u v ↔ ∀ z ∈ e.val, z.val ∈ radiusTube n r u v := by
  simp only [radiusTubeRevealedEdges,RSW.mem_inducedConfigurationErasure,Finset.mem_univ,
    true_and,Set.mem_ofPred_eq]

/-- The source event in the fixed-tube averaging theorem is the actual
original tube-confined connection, with its true original sampled edges. -/
theorem radiusTube_revealed_connection_iff_walk (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (A : Configuration (squareLattice.induce (box n : Set LatticeVertex)))
    (a b : (box n : Set LatticeVertex)) (ha : a.val ∈ radiusTube n r u v) :
    ActualConnected _ (A ∩ radiusTubeRevealedEdges n r u v) a b ↔
      ∃ p : (openGraph _ A).Walk a b, ∀ z ∈ p.support, z.val ∈ radiusTube n r u v := by
  unfold radiusTubeRevealedEdges
  rw [← induced_erasure_eq_inter_all_open _ {z | z.val ∈ radiusTube n r u v} A]
  exact actualConnected_erasure_iff_confined_walk _ _ A a b ha

end
end PottsContinuity.Thm3.Prop4
