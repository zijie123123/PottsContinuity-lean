-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredVertexQuotient.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Model
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem wiredQuotient_sourceAdj_to_target
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (A : Configuration G) {u v : V}
    (h : (openGraph G A).Adj u v) :
    (openGraph H (A.map E.toEmbedding)).Adj (f u) (f v) := by
  rw [openGraph_adj] at h ⊢
  rcases h with ⟨e, he, heuv⟩
  refine ⟨E e, Finset.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
  rw [hE, heuv]
  simp

private theorem wiredQuotient_targetAdj_to_sourceRel
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (A : Configuration G) {u v : V}
    (h : (openGraph H (A.map E.toEmbedding)).Adj (f u) (f v)) :
    (componentSetoid G ξ A).r u v := by
  rw [openGraph_adj] at h
  rcases h with ⟨e', he', heuv⟩
  obtain ⟨e, he, heEq⟩ := Finset.mem_map.mp he'
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
  have heab : e.val = s(a,b) := by simpa using hab.symm
  have hpair : s(f u, f v) = s(f a, f b) := by
    calc
      s(f u, f v) = e'.val := heuv.symm
      _ = (E e).val := by simpa using (congrArg Subtype.val heEq).symm
      _ = Sym2.map f e.val := hE e
      _ = Sym2.map f (s(a,b)) := by rw [heab]
      _ = s(f a, f b) := by simp
  rcases Sym2.eq_iff.mp hpair with ⟨hua, hvb⟩ | ⟨hub, hva⟩
  · have hua' : ξ.partition.r u a := by rw [hker]; exact hua
    have hvb' : ξ.partition.r b v := by rw [hker]; exact hvb.symm
    have hadj : (openGraph G A).Adj a b := by
      rw [openGraph_adj]
      exact ⟨e, he, heab⟩
    exact Setoid.trans' (componentSetoid G ξ A)
      (boundary_component G ξ A hua')
      (Setoid.trans' (componentSetoid G ξ A)
        (actualConnected_component G ξ A (actualConnected_of_adj G A hadj))
        (boundary_component G ξ A hvb'))
  · have hub' : ξ.partition.r u b := by rw [hker]; exact hub
    have hva' : ξ.partition.r a v := by rw [hker]; exact hva.symm
    have hadj : (openGraph G A).Adj a b := by
      rw [openGraph_adj]
      exact ⟨e, he, heab⟩
    exact Setoid.trans' (componentSetoid G ξ A)
      (boundary_component G ξ A hub')
      (Setoid.trans' (componentSetoid G ξ A)
        (Setoid.symm' (componentSetoid G ξ A)
          (actualConnected_component G ξ A (actualConnected_of_adj G A hadj)))
        (boundary_component G ξ A hva'))

private theorem wiredQuotient_walk_lift
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (A : Configuration G) {x y : W}
    (p : (openGraph H (A.map E.toEmbedding)).Walk x y)
    (u : V) (hxu : f u = x) :
    ∃ v : V, f v = y ∧ (componentSetoid G ξ A).r u v := by
  induction p generalizing u with
  | nil => exact ⟨u, hxu, (componentSetoid G ξ A).refl u⟩
  | @cons x y z hadj tail ih =>
      obtain ⟨a, hya⟩ := hsurj y
      have hstep : (componentSetoid G ξ A).r u a :=
        wiredQuotient_targetAdj_to_sourceRel f E hE ξ hker A
          (by simpa [hxu, hya] using hadj)
      obtain ⟨c, hzc, hrel⟩ := ih a hya
      exact ⟨c, hzc, Setoid.trans' (componentSetoid G ξ A) hstep hrel⟩

private theorem wiredQuotient_sourceConnected_to_target
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (A : Configuration G) {u v : V}
    (h : ActualConnected G A u v) :
    ActualConnected H (A.map E.toEmbedding) (f u) (f v) := by
  change (openGraph G A).Reachable u v at h
  change (openGraph H (A.map E.toEmbedding)).Reachable (f u) (f v)
  exact SimpleGraph.Reachable.map
    (show openGraph G A →g openGraph H (A.map E.toEmbedding) from
      { toFun := f
        map_rel' := by
          intro x y hxy
          exact wiredQuotient_sourceAdj_to_target f E hE A hxy }) h

/-- Actual connectivity after quotienting vertices is exactly connectivity after
wiring the fibers of the quotient map. -/
theorem wiredVertexQuotient_componentSetoid_rel_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (A : Configuration G) (u v : V) :
    (componentSetoid G ξ A).r u v ↔
      ActualConnected H (A.map E.toEmbedding) (f u) (f v) := by
  rw [componentSetoid_rel_iff]
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
        rcases hxy with hconn | hξ
        · exact wiredQuotient_sourceConnected_to_target f E hE A hconn
        · have hxy : f x = f y := by
            rw [hker] at hξ
            change f x = f y at hξ
            exact hξ
          rw [hxy]
          exact SimpleGraph.Reachable.refl _
    | refl x => exact SimpleGraph.Reachable.refl _
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    obtain ⟨p⟩ := (actualConnected_iff_walk H (A.map E.toEmbedding) (f u) (f v)).mp h
    obtain ⟨z, hz, hrel⟩ :=
      wiredQuotient_walk_lift f hsurj E hE ξ hker A p u rfl
    have hboundary : ξ.partition.r z v := by
      have hkerRel : (Setoid.ker f).r z v := by
        change f z = f v
        exact hz
      rw [hker]
      exact hkerRel
    exact (componentSetoid_rel_iff G ξ A u v).mp
      (Setoid.trans' (componentSetoid G ξ A) hrel
        (boundary_component G ξ A hboundary))

/-- The finite component count is preserved by the explicit quotient data,
including every quotient-carrier vertex not incident to an open edge. -/
theorem wiredVertexQuotient_componentCount
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (A : Configuration G) :
    componentCount G ξ A =
      componentCount H (BoundaryCondition.free (∅ : Set W)) (A.map E.toEmbedding) := by
  classical
  let t := (openGraph H (A.map E.toEmbedding)).reachableSetoid
  let F : V → Quotient t := fun x => Quotient.mk t (f x)
  have hrel : componentSetoid G ξ A = Setoid.ker F := by
    apply Setoid.ext
    intro u v
    change (componentSetoid G ξ A).r u v ↔ F u = F v
    rw [wiredVertexQuotient_componentSetoid_rel_iff f hsurj E hE ξ hker A u v]
    change (openGraph H (A.map E.toEmbedding)).Reachable (f u) (f v) ↔
      Quotient.mk t (f u) = Quotient.mk t (f v)
    constructor
    · intro hr
      apply Quotient.sound
      exact hr
    · intro hq
      exact Quotient.exact hq
  have hF : Function.Surjective F := by
    intro q
    obtain ⟨w, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨v, ?_⟩
    change Quotient.mk t (f v) = Quotient.mk t w
    rw [hv]
  let e : Quotient (componentSetoid G ξ A) ≃ Quotient t :=
    (Quotient.congrRight (fun x y => hrel ▸ Iff.rfl)).trans
      (Setoid.quotientKerEquivOfSurjective F hF)
  have hcard : Nat.card (Quotient (componentSetoid G ξ A)) = Nat.card (Quotient t) :=
    Nat.card_congr e
  simpa [componentCount, t, componentSetoid_free] using hcard

end
end PottsContinuity.FKC.FiniteFK
