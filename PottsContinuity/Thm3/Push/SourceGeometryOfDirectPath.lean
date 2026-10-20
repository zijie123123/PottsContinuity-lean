module

public import PottsContinuity.Thm3.Push.DirectPrefixSystem

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 RSW Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Every actual open first-contact prefix avoiding the selected tip
supplies the complete source geometry. No choice rule, code order,
far-boundary continuation, extremality or locality is used. -/
theorem caseTwoDirectPrefixSourcePaths_of_open_first_contact
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n)))
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (a : RectangleVertex (0,0) (2*n) (2*n))
    (ha : a ∈ intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
    (t : RectangleVertex (0,0) (2*n) (2*n))
    (htx : t.val.1 = 4*(s:ℤ)-1) (hty : b.2.val.2 ≤ t.val.2)
    (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a t)
    (hp : p.support = trace)
    (hfirst : firstContactTrace {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} trace = some trace)
    (havoid : ∀ z ∈ trace, z ∉ caseTwoTipOriginalTrace n s hfit b.1) :
    Nonempty (CaseTwoDirectPrefixSourcePaths n s hfit C b trace) := by
  obtain ⟨htip,hlast⟩ := (caseTwoTipEndpointSelector_eq_some_iff n s hfit C b.1 b.2).mp hb
  obtain ⟨j,u,q,hj,hjl,hjr,hux,hq,hqb,hqfirst⟩ :=
    caseTwoTipFirstHitSelector_original_path n s hfit C b.1 htip
  change q.val.support = caseTwoTipOriginalTrace n s hfit b.1 at hq
  have hend : q.val.support.getLast? = some u := by
    rw [List.getLast?_eq_some_getLast q.val.support_ne_nil,SimpleGraph.Walk.getLast_support]
  have hub : u = b.2 := Option.some.inj (hend.symm.trans ((congrArg List.getLast? hq).trans hlast))
  let P := p.mapLe (openGraph_le _ C)
  let Q := q.val.mapLe (openGraph_le _ C)
  have hsP : P.support = trace := (SimpleGraph.Walk.support_mapLe_eq_support _ _).trans hp
  have hsQ : Q.support = caseTwoTipOriginalTrace n s hfit b.1 :=
    (SimpleGraph.Walk.support_mapLe_eq_support _ _).trans hq
  have hcontact := (firstContactTrace_fixed_iff_firstContact_at_length p
    {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} ⟨htx,hty⟩).mp
      (by simpa only [hp] using hfirst)
  have hfirstP : ∀ i < P.length,
      ¬ ((P.getVert i).val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ (P.getVert i).val.2) := by
    intro i hi
    have hi' : i < p.length := by simpa only [P,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.length_map] using hi
    simpa only [P,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,SimpleGraph.Hom.ofLE_apply,Set.mem_ofPred_eq]
      using hcontact.2.2 i hi'
  have hdis : ∀ z ∈ P.support, z ∉ Q.support := by
    intro z hz hzq
    rw [hsP] at hz
    exact havoid z hz (hsQ ▸ hzq)
  let O : SourceWalkPair (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C) := {
    firstStart := a
    secondStart := j
    firstEnd := t
    secondEnd := u
    first := p
    second := q.val }
  refine ⟨⟨O,?_,ha,⟨hj,hjl,hjr⟩,hp,hq,hub⟩⟩
  change RetainedRectanglePathGeometry (2*n) (2*n) (4*(s:ℤ))
    {firstStart := a,secondStart := j,firstEnd := t,secondEnd := u,first := P,second := Q}
  refine ⟨by omega,by omega,ha.1,hj,htx,?_,hux,ha.2.1,?_,?_,hdis,?_⟩
  · change u.val.2 ≤ t.val.2
    rw [hub]
    exact hty
  · change a.val.1 < j.val.1
    have hax := ha.2.2
    omega
  · intro z hz
    exact (hqb z (by simpa only [Q,SimpleGraph.Walk.support_mapLe_eq_support] using hz)).1
  · simpa only [hub] using hfirstP


end
end PottsContinuity.Push
