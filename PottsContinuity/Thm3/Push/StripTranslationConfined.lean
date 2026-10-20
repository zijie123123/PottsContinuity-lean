module

public import PottsContinuity.Thm3.Push.StripTranslationPaths
public import PottsContinuity.Thm3.Push.StripTranslationProbability

@[expose] public section

namespace PottsContinuity.Push
open MeasureTheory PD.FK Topology
noncomputable section

/-- Translation transports the exact confined open-walk event and both
original endpoint sets. No virtual boundary connections enter this identity. -/
theorem stripConfinedConnection_translation (n : ℕ) (a : ℤ)
    (S : Finset (RSW.stripVertices n)) (A B : Set (RSW.stripVertices n)) :
    (stripTranslation n a) ⁻¹' (RSW.stripConfinedConnection n S A B) =
      RSW.stripConfinedConnection n
        (S.map (stripTranslationIso n a).toEquiv.toEmbedding)
        ((stripTranslationIso n a) '' A) ((stripTranslationIso n a) '' B) := by
  ext ω
  let e := stripTranslationOpenIso n a ω
  constructor
  · rintro ⟨a,b,p,ha,hb,hp⟩
    refine ⟨e a,e b,p.map e.toHom,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    exact Finset.mem_map.mpr ⟨v,hp v hv,rfl⟩
  · rintro ⟨a,b,p,ha,hb,hp⟩
    refine ⟨e.symm a,e.symm b,p.map e.symm.toHom,?_,?_,?_⟩
    · obtain ⟨a',ha',haa'⟩ := ha
      change e a' = a at haa'
      rw [← haa',e.symm_apply_apply]
      exact ha'
    · obtain ⟨b',hb',hbb'⟩ := hb
      change e b' = b at hbb'
      rw [← hbb',e.symm_apply_apply]
      exact hb'
    · intro w hw
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hw
      obtain ⟨v,hv,rfl⟩ := hw
      obtain ⟨v',hv',hvv'⟩ := Finset.mem_map.mp (hp v hv)
      change e v' = v at hvv'
      change e.symm v ∈ S
      rw [← hvv',e.symm_apply_apply]
      exact hv'

/-- Actual confined connection probabilities in the genuine top-only strip
law are exactly preserved by translating the carrier and both original arcs. -/
theorem strip_limit_confined_translation (θ : Parameters) (n : ℕ) (a : ℤ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (S : Finset (RSW.stripVertices n)) (A B : Set (RSW.stripVertices n)) :
    μ.real (RSW.stripConfinedConnection n S A B) =
      μ.real (RSW.stripConfinedConnection n
        (S.map (stripTranslationIso n a).toEquiv.toEmbedding)
        ((stripTranslationIso n a) '' A) ((stripTranslationIso n a) '' B)) := by
  rw [← stripConfinedConnection_translation]
  exact strip_limit_clopen_translation θ n μ hμ a _
    (RSW.stripConfinedConnection_isClopen n S A B)
    (RSW.stripConfinedConnection_isUpperSet n S A B)

end
end PottsContinuity.Push
