module

public import PottsContinuity.Thm3.Push.StripReflectionPaths
public import PottsContinuity.Thm3.Push.StripReflectionProbability

@[expose] public section

namespace PottsContinuity.Push
open MeasureTheory PD.FK Topology
noncomputable section

/-- Reflection transports the exact confined open-walk event and both
original endpoint sets. No virtual boundary connections enter this identity. -/
theorem stripConfinedConnection_reflection (n : ℕ)
    (S : Finset (RSW.stripVertices n)) (A B : Set (RSW.stripVertices n)) :
    (stripHorizontalReflection n) ⁻¹' (RSW.stripConfinedConnection n S A B) =
      RSW.stripConfinedConnection n
        (S.map (stripHorizontalReflectionIso n).toEquiv.toEmbedding)
        ((stripHorizontalReflectionIso n) '' A) ((stripHorizontalReflectionIso n) '' B) := by
  ext ω
  let e := stripReflectionOpenIso n ω
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
law are exactly preserved by reflecting the carrier and both original arcs. -/
theorem strip_limit_confined_reflection (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (S : Finset (RSW.stripVertices n)) (A B : Set (RSW.stripVertices n)) :
    μ.real (RSW.stripConfinedConnection n S A B) =
      μ.real (RSW.stripConfinedConnection n
        (S.map (stripHorizontalReflectionIso n).toEquiv.toEmbedding)
        ((stripHorizontalReflectionIso n) '' A) ((stripHorizontalReflectionIso n) '' B)) := by
  rw [← stripConfinedConnection_reflection]
  exact strip_limit_clopen_reflection θ n μ hμ _
    (RSW.stripConfinedConnection_isClopen n S A B)

end
end PottsContinuity.Push
