-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateReflection.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.SlitBoxHorizontalReflection
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

def slitBoxReflectVertex (n : ℕ) : SlitBoxVertex n → SlitBoxVertex n :=
  slitBoxGraphHorizontalReflectionIso n

@[simp] theorem slitBoxReflectVertex_apply_val (n : ℕ) (v : SlitBoxVertex n) :
    (slitBoxReflectVertex n v).val = (-v.val.1, v.val.2) :=
  slitBoxHorizontalReflectionVertexEquiv_val n v

theorem slitBoxReflectVertex_involutive (n : ℕ) :
    Function.Involutive (slitBoxReflectVertex n) := by
  intro v
  exact (slitBoxGraphHorizontalReflectionIso n).apply_symm_apply v

 theorem slitBoxReflect_mem_wiredArc_iff (n : ℕ) (v : SlitBoxVertex n) :
    slitBoxReflectVertex n v ∈ slitBoxWiredArc n ↔ v ∈ slitBoxWiredArc n := by
  rw [mem_slitBoxWiredArc_iff, mem_slitBoxWiredArc_iff]
  change (-v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n) ↔
    (v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n)
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨by omega, h₂, h₃⟩

/-- Reflection of an actual first-hit candidate, retaining its ordered path. -/
noncomputable def slitBoxReflectCandidate (n : ℕ) (u : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    SlitBoxFirstHitBaseCandidates n (slitBoxReflectVertex n u) := by
  classical
  let σ := slitBoxGraphHorizontalReflectionIso n
  let qpath := p.val.2.map σ.toHom σ.injective
  refine ⟨⟨σ p.val.1, qpath⟩, ?_, ?_⟩
  · exact (slitBoxReflect_mem_wiredArc_iff n p.val.1).2 p.property.1
  · intro x hx hxArc
    have hx' : σ.symm x ∈ finiteSimplePathSupport p.val := by
      change x ∈ ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map σ.toHom).support at hx
      rw [SimpleGraph.Walk.support_map] at hx
      rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
      have : σ y = x := hxy
      simpa [finiteSimplePathSupport, ← this] using hy
    have hxArc' : σ.symm x ∈ slitBoxWiredArc n := by
      have h : σ (σ.symm x) ∈ slitBoxWiredArc n ↔
          σ.symm x ∈ slitBoxWiredArc n := by
        simpa [slitBoxReflectVertex, σ] using
          slitBoxReflect_mem_wiredArc_iff n (σ.symm x)
      rw [σ.apply_symm_apply] at h
      exact h.mp hxArc
    have hfirst := p.property.2 (σ.symm x) hx' hxArc'
    have := congrArg σ hfirst
    simpa [σ] using this

@[simp] theorem slitBoxReflectCandidate_endpoint (n : ℕ) (u : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    (slitBoxReflectCandidate n u p).val.1 = slitBoxReflectVertex n p.val.1 := rfl

theorem slitBoxReflectCandidate_orderedSupport (n : ℕ) (u : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    finiteSimplePathSupport (slitBoxReflectCandidate n u p).val =
      (finiteSimplePathSupport p.val).map (slitBoxReflectVertex n) := by
  change ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map
      (slitBoxGraphHorizontalReflectionIso n).toHom).support = _
  rw [SimpleGraph.Walk.support_map]
  rfl

@[simp] theorem configurationIso_slitBoxReflection_involutive (n : ℕ)
    (A : Configuration (slitBoxGraph n)) :
    configurationIso (slitBoxGraphHorizontalReflectionIso n)
      (configurationIso (slitBoxGraphHorizontalReflectionIso n) A) = A := by
  let f := configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)
  have hσ : (slitBoxGraphHorizontalReflectionIso n).symm.toEquiv =
      (slitBoxGraphHorizontalReflectionIso n).toEquiv := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    simp [slitBoxGraphHorizontalReflectionIso,
      slitBoxHorizontalReflectionVertexEquiv]
  have hfSymm : f.symm = f := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    simp [f, configurationIsoEdgeEquiv, SimpleGraph.Iso.mapEdgeSet, hσ]
  have hf : Function.Involutive f := by
    intro e
    have he : f.symm e = f e := congrArg (fun g : _ ≃ _ => g e) hfSymm
    simpa [he] using f.apply_symm_apply e
  change Finset.map f.toEmbedding (Finset.map f.toEmbedding A) = A
  ext e
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨b, ⟨a, ha, hab⟩, hbe⟩
    subst b
    have he : f (f a) = e := hbe
    rw [hf a] at he
    simpa [he] using ha
  · intro he
    exact ⟨f e, ⟨e, he, rfl⟩, by simp [hf e]⟩

theorem slitBoxReflectCandidate_edgeSupport (n : ℕ) (u : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    configurationIso (slitBoxGraphHorizontalReflectionIso n)
        (slitBoxCandidateOriginalPathEdgeSupport n u p) =
      slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
        (slitBoxReflectCandidate n u p) := by
  classical
  ext e
  change e ∈ Finset.map
      (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding
        (slitBoxCandidateOriginalPathEdgeSupport n u p) ↔
    e ∈ slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
      (slitBoxReflectCandidate n u p)
  rw [Finset.mem_map]
  constructor
  · rintro ⟨e₀, he₀, hmap⟩
    have he₀' := (mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p e₀).mp he₀
    have hval : Sym2.map (slitBoxGraphHorizontalReflectionIso n) e₀.val = e.val := by
      simpa [configurationIsoEdgeEquiv, SimpleGraph.Iso.mapEdgeSet] using
        congrArg Subtype.val hmap
    rw [mem_slitBoxCandidateOriginalPathEdgeSupport_iff]
    change e.val ∈ ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map
      (slitBoxGraphHorizontalReflectionIso n).toHom).edges
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨e₀.val, he₀', hval⟩
  · intro he
    have he' := (mem_slitBoxCandidateOriginalPathEdgeSupport_iff
      n (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u p) e).mp he
    change e.val ∈ ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map
      (slitBoxGraphHorizontalReflectionIso n).toHom).edges at he'
    rw [SimpleGraph.Walk.edges_map] at he'
    rcases List.mem_map.mp he' with ⟨z, hz, hze⟩
    let e₀ : (slitBoxGraph n).edgeSet := ⟨z,
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges_subset_edgeSet hz⟩
    refine ⟨e₀, (mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p e₀).2 hz, ?_⟩
    apply Subtype.ext
    change Sym2.map (slitBoxGraphHorizontalReflectionIso n) e₀.val = e.val
    simpa [e₀] using hze

end
end PottsContinuity.FKC.FiniteFK
