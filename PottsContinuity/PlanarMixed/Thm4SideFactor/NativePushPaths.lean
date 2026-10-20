module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushReducedDefinitions
public import PottsContinuity.Thm3.RSW.EmbeddedPath

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open RSW PD.FK PD.Duality BD12
noncomputable section

theorem nativeSideReducedCrossingEvent_confined_walk
    (m : ℕ) (C : Configuration (nativeSideReducedGraph m))
    (hC : C ∈ nativeSideReducedCrossingEvent m) :
    ∃ u v : NativeSideVertex m,
      u.val.1 = -16*(m:ℤ)-1 ∧ v.val.1 = 16*(m:ℤ) ∧
      ∃ p : (openGraph (nativeSideReducedGraph m) C).Walk u v,
        ∀ z ∈ p.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ ((4*m-1:ℕ):ℤ) := by
  let f := Push.rectangleBandEmbedding (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)
  let hGH := Push.rectangleBandEmbedding_map_le (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)
  let D := (edgeRestrictionConfigurationEquiv (nativeSideFullGraph m) (nativeSideWiredEdges m) C).val
  obtain ⟨u,hu,v,hv,⟨p⟩⟩ := hC
  have heq : openGraph (nativeSideReducedGraph m) C = openGraph (nativeSideFullGraph m) D :=
    openGraph_edgeRestriction (nativeSideFullGraph m) (nativeSideWiredEdges m) C
  let g : openGraph (rectangleGraph (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1))
      (embeddedConfigurationRestriction _ _ f hGH D) →g
      openGraph (nativeSideReducedGraph m) C :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        have hh := (embeddedRestrictionOpenHom _ _ f hGH D).map_rel hxy
        rw [heq]
        exact hh }
  refine ⟨f u,f v,hu,?_,p.map g,?_⟩
  · change v.val.1 = 16*(m:ℤ)
    have he : -16*(m:ℤ)-1 + ((32*m+1:ℕ):ℤ) = 16*(m:ℤ) := by omega
    simpa only [he,Set.mem_ofPred_eq] using hv
  · intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    have h := (mem_latticeRectangle (-16*(m:ℤ)-1,0) w.val (32*m+1) (4*m-1)).mp w.property
    change 0 ≤ w.val.2 ∧ w.val.2 ≤ ((4*m-1:ℕ):ℤ)
    simpa only [Prod.snd,zero_add] using h.2

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
