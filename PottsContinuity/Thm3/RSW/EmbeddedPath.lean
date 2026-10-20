module

public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.Thm3.RSW.EmbeddedFreeConnection
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Embedded restriction preserves actual paths and their vertex constraints

The confined corridor events in the corrected Proposition-3 construction
require paths in the image of the small rectangle, not only connectivity in
the larger graph. The graph homomorphism here retains precisely that image.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)

/-- Map the actual open graph of the restricted configuration into the full
actual open graph, using the given vertex embedding. -/
def embeddedRestrictionOpenHom (A : Configuration H) :
    openGraph G (embeddedConfigurationRestriction G H f hGH A) →g openGraph H A where
  toFun := f
  map_rel' := by
    intro a b hab
    let C := embeddedConfigurationRestriction G H f hGH A
    have hsub := embeddedConfigurationEmbedding_restriction_subset G H f hGH A
    rcases (openGraph_adj G C a b).mp hab with ⟨e, he, heval⟩
    have hGadj : G.Adj a b := G.mem_edgeSet.mp (heval ▸ e.property)
    have hHadj : H.Adj (f a) (f b) := hGH
      ((SimpleGraph.map_adj f G (f a) (f b)).mpr ⟨a,b,hGadj,rfl,rfl⟩)
    let eH : H.edgeSet := ⟨s(f a,f b), H.mem_edgeSet.mpr hHadj⟩
    have heI : embeddedEdgeEmbedding G H f hGH e ∈
        embeddedConfigurationEmbedding G H f hGH C := by
      rw [embeddedConfigurationEmbedding_eq_map]
      exact Finset.mem_map.mpr ⟨e,he,rfl⟩
    have heA := hsub heI
    rw [openGraph_adj]
    refine ⟨eH, ?_, rfl⟩
    have hev : (embeddedEdgeEmbedding G H f hGH e).val = s(f a,f b) := by
      rw [embeddedEdgeEmbedding_coe, heval]
      simp
    have heq : embeddedEdgeEmbedding G H f hGH e = eH := Subtype.ext hev
    simpa [heq] using heA

omit [Finite V] [Finite W] in
/-- A connected restriction gives a full-graph path confined to the image of
its vertex set. There is no assumption on exterior open states. -/
theorem embedded_restriction_confined_path (A : Configuration H) (x y : V)
    (hconn : ActualConnected G (embeddedConfigurationRestriction G H f hGH A) x y) :
    ∃ w : (openGraph H A).Walk (f x) (f y),
      ∀ z ∈ w.support, z ∈ Set.range f := by
  obtain ⟨p⟩ := hconn
  let hom := embeddedRestrictionOpenHom G H f hGH A
  have hs : ∀ z ∈ (p.map hom).support, z ∈ Set.range f := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact ⟨v,rfl⟩
  exact ⟨p.map hom, hs⟩

/-- Increasing event probabilities compare with the actual restriction of the
larger free law. This retains confinement data in the event itself. -/
theorem embedded_free_probability_le (θ : Parameters)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G θ (BoundaryCondition.free ∅) S).toReal ≤
      (measure H θ (BoundaryCondition.free ∅)
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  have h := embedded_boundary_probability_le G H f hGH θ (BoundaryCondition.free ∅) S hS
  have hpart : (isolatedExtensionPullbackBoundary f (BoundaryCondition.free ∅)).partition =
      (BoundaryCondition.free (∅ : Set V)).partition := by
    apply Setoid.ext
    intro a b
    change f a = f b ↔ a = b
    exact f.injective.eq_iff
  have hlaw := law_eq_of_boundary_partition_eq (G := G) θ
    (isolatedExtensionPullbackBoundary f (BoundaryCondition.free ∅))
    (BoundaryCondition.free ∅) hpart
  unfold PD.FK.measure at h ⊢
  rw [hlaw] at h
  exact h

end
end PottsContinuity.RSW
