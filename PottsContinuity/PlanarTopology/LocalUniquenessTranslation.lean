module

public import PottsContinuity.PlanarTopology.LocalUniquenessEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite
noncomputable section

/-- Translation preserves the actual finite local-uniqueness property,
including the global outside-witness condition and the induced connecting graph. -/
theorem finiteLocalUniquenessEvent_translate (a : LatticeVertex)
    (S T : Finset LatticeVertex) (ω : LatticeConfiguration)
    (hω : ω ∈ finiteLocalUniquenessEvent S T) :
    edgeTranslate a ω ∈ finiteLocalUniquenessEvent
      (S.image (latticeTranslate a)) (T.image (latticeTranslate a)) := by
  classical
  obtain ⟨hST,hT⟩ := hω
  let e := openGraphTranslationIso a ω
  have hBij : Set.BijOn e (T : Set LatticeVertex)
      ((T.image (latticeTranslate a)) : Set LatticeVertex) := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro z hz
      exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
    · intro z hz
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
      exact ⟨x,hx,hxz⟩
  let f := e.induce hBij
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨u,hST hu,rfl⟩
  · intro u' v' hu' hv' hex hey
    obtain ⟨u,hu,heu⟩ := Finset.mem_image.mp hu'
    obtain ⟨v,hv,hev⟩ := Finset.mem_image.mp hv'
    let uT : {z // z ∈ T} := ⟨u,hST hu⟩
    let vT : {z // z ∈ T} := ⟨v,hST hv⟩
    have outside (b : LatticeVertex) (b' : {z // z ∈ T.image (latticeTranslate a)})
        (hb : e b = b'.val)
        (hext : ∃ z, z ∉ T.image (latticeTranslate a) ∧
          (PD.rcInfiniteOpenGraph (edgeTranslate a ω)).Reachable b'.val z) :
        ∃ z, z ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable b z := by
      obtain ⟨z,hz,hreach⟩ := hext
      refine ⟨e.symm z,?_,?_⟩
      · intro hzT
        apply hz
        apply Finset.mem_image.mpr
        exact ⟨e.symm z,hzT,e.apply_symm_apply z⟩
      · apply e.reachable_iff.mp
        simpa only [e.apply_symm_apply,hb] using hreach
    have hconn := hT uT vT hu hv (outside u u' heu hex) (outside v v' hev hey)
    have hfu : f uT = u' := Subtype.ext heu
    have hfv : f vT = v' := Subtype.ext hev
    have hh := hconn.map f.toHom
    change ((PD.rcInfiniteOpenGraph (edgeTranslate a ω)).induce
      ((T.image (latticeTranslate a)) : Set LatticeVertex)).Reachable (f uT) (f vT) at hh
    rwa [hfu,hfv] at hh

end
end PottsContinuity.PlanarTopology
