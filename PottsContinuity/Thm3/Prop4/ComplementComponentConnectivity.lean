module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Removing one component outside a connected explored region -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- Original labels of one component of the graph outside the explored set. -/
def complementComponentLabels {V : Type*} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) : Set V := Subtype.val '' C.supp

/-- The component remains connected when expressed on original vertex labels. -/
theorem complementComponentLabels_preconnected {V : Type*} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    (G.induce (complementComponentLabels G S C)).Preconnected := by
  let f : C.toSimpleGraph →g G.induce (complementComponentLabels G S C) := {
    toFun := fun x => ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
    map_rel' := fun h => h }
  rintro ⟨x,⟨a,ha,rfl⟩⟩ ⟨y,⟨b,hb,rfl⟩⟩
  exact (C.reachable_toSimpleGraph ha hb).map f

/-- A neighbor of an unexplored component lying outside that component is
in the explored set; different unexplored components cannot be adjacent. -/
theorem complementComponentLabels_attachment {V : Type*} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) {x y : V}
    (hx : x ∉ complementComponentLabels G S C) (hy : y ∈ complementComponentLabels G S C)
    (hxy : G.Adj x y) : x ∈ S := by
  classical
  by_contra hxS
  obtain ⟨b,hb,rfl⟩ := hy
  have hstep : (G.induce Sᶜ).Adj ⟨x,hxS⟩ b := hxy
  exact hx ⟨⟨x,hxS⟩,(C.mem_supp_congr_adj hstep).mpr hb,rfl⟩

/-- If the ambient graph and the explored set are connected, the exterior
of each single unexplored component is connected. No planarity is required. -/
theorem complementComponentLabels_exterior_preconnected {V : Type*}
    (G : SimpleGraph V) (hG : G.Preconnected) (S : Set V)
    (hS : (G.induce S).Preconnected) (hne : S.Nonempty)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    (G.induce (complementComponentLabels G S C)ᶜ).Preconnected := by
  classical
  let D := complementComponentLabels G S C
  have disjoint (x : V) (hx : x ∈ S) : x ∉ D := by
    rintro ⟨a,ha,heq⟩
    exact a.property (heq ▸ hx)
  obtain ⟨r,hr⟩ := hne
  let f : G.induce S →g G.induce Dᶜ := {
    toFun := fun x => ⟨x.val,disjoint x.val x.property⟩
    map_rel' := fun h => h }
  have liftWalk {x : V} (p : G.Walk x r) : ∀ hx : x ∉ D,
      (G.induce Dᶜ).Reachable ⟨x,hx⟩ ⟨r,disjoint r hr⟩ := by
    induction p with
    | nil => exact fun hx => SimpleGraph.Reachable.refl _
    | @cons x y r hxy p ih =>
      intro hx
      by_cases hy : y ∈ D
      · have hxS := complementComponentLabels_attachment G S C hx hy hxy
        exact (hS ⟨x,hxS⟩ ⟨r,hr⟩).map f
      · exact (show (G.induce Dᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy).reachable.trans (ih hr hy)
  intro x y
  exact (liftWalk (hG x.val r).some x.property).trans
    (liftWalk (hG y.val r).some y.property).symm

end
end PottsContinuity.Thm3.Prop4
