module

public import PottsContinuity.Thm3.RSW.AnnulusEmbedding
public import PottsContinuity.Thm3.RSW.FiniteIso

/-! # Literal local-carrier identification for the shielded annulus bound -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- A local finite lattice set, viewed as a vertex region of the ambient set. -/
def finiteVertexRegion (U V : Finset (ℤ × ℤ)) : Set (V : Set (ℤ × ℤ)) :=
  {v | v.val ∈ U}

/-- The nested induced carrier is exactly the original smaller lattice graph.
The coordinates of each vertex are unchanged. -/
def finiteInducedRegionIso (U V : Finset (ℤ × ℤ)) (hUV : U ⊆ V) :
    (squareLattice.induce (U : Set (ℤ × ℤ))) ≃g
      (squareLattice.induce (V : Set (ℤ × ℤ))).induce (finiteVertexRegion U V) where
  toFun u := ⟨⟨u.val,hUV u.property⟩,u.property⟩
  invFun v := ⟨v.val.val,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem openGraph_embedded_extension {X Y : Type*}
    (G : SimpleGraph X) (H : SimpleGraph Y) (f : X ↪ Y) (hGH : G.map f ≤ H)
    (A : Configuration G) :
    openGraph H (embeddedConfigurationEmbedding G H f hGH A) = (openGraph G A).map f := by
  change openGraph H (subgraphConfigurationEmbedding hGH
    (isolatedExtensionConfigurationEquiv G f A)) = _
  rw [openGraph_subgraphConfigurationEmbedding,openGraph_isolatedExtension]

/-- The induced-region probability in the ambient notation is exactly the
literal free probability on U. Isolated exterior vertices do not alter this
law and no planar or parameter hypothesis is required. -/
theorem inducedAnnulusProbability_eq_local (U V : Finset (ℤ × ℤ)) (hUV : U ⊆ V)
    (θ : Parameters) (z : ℤ × ℤ) (n : ℕ) :
    inducedAnnulusProbability V (finiteVertexRegion U V) θ z n =
      finiteBoundaryEventProbability U θ (frozenBoundaryCondition U 0)
        (fun ω => ω ∈ annulusCircuitEvent U z n) := by
  let G := squareLattice.induce (V : Set (ℤ × ℤ))
  let W := finiteVertexRegion U V
  let e := finiteInducedRegionIso U V hUV
  let f : (U : Set (ℤ × ℤ)) ↪ (V : Set (ℤ × ℤ)) :=
    ⟨fun u => ⟨u.val,hUV u.property⟩,
      fun u v h => Subtype.ext (congrArg (fun z : (V : Set (ℤ × ℤ)) => z.val) h)⟩
  let S : Set (Configuration (G.induce W)) :=
    {B | inducedConfigurationExtension W B ∈
      finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n)}
  have hevent : {A | configurationIso e A ∈ S} =
      finiteBoolEvent U (fun ω => ω ∈ annulusCircuitEvent U z n) := by
    ext A
    have hmap : openGraph G (inducedConfigurationExtension W (configurationIso e A)) =
        (openGraph (squareLattice.induce (U : Set (ℤ × ℤ))) A).map f := by
      change openGraph G (embeddedConfigurationEmbedding _ _ _ _ _) = _
      rw [openGraph_embedded_extension]
      ext x y
      constructor
      · intro hxy
        obtain ⟨u,v,huv,hu,hv⟩ := (SimpleGraph.map_adj (inducedVertexEmbedding W) _ x y).mp hxy
        exact (SimpleGraph.map_adj f _ x y).mpr
          ⟨e.symm u,e.symm v,(openGraphIso e A).symm.map_rel_iff.mpr huv,hu,hv⟩
      · intro hxy
        obtain ⟨u,v,huv,hu,hv⟩ := (SimpleGraph.map_adj f _ x y).mp hxy
        exact (SimpleGraph.map_adj (inducedVertexEmbedding W) _ x y).mpr
          ⟨e u,e v,(openGraphIso e A).map_rel_iff.mpr huv,hu,hv⟩
    exact annulus_event_iff_of_openGraph_map U V f (fun _ => rfl) A _ hmap z n
  have hprob := free_probability_iso θ e S
  rw [hevent] at hprob
  have hfree : law (squareLattice.induce (U : Set (ℤ × ℤ))) θ
      (frozenBoundaryCondition U 0) = law _ θ (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq θ _ _
      (by simp [frozenBoundaryCondition,BoundaryCondition.free])
  unfold inducedAnnulusProbability finiteBoundaryEventProbability PD.FK.measure
  rw [hfree]
  exact hprob

end
end PottsContinuity.RSW
