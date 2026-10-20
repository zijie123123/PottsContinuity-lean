module

public import PottsContinuity.PD.FK.Graph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- In a connected original graph, if mixed attachments of either reveal
avoid every bond of the other, two proper reveal regions cannot overlap.
The argument concerns all bonds, independently of their sampled states. -/
theorem disjoint_reveals_of_opposite_attachment_avoidance
    {V : Type*} (G : SimpleGraph V) (hconn : G.Preconnected)
    (L R : Configuration G) (hproper : ∃ g : G.edgeSet, g ∉ L)
    (hLR : ∀ u, (∃ f ∈ L, ∃ g : G.edgeSet, g ∉ L ∧ u ∈ f.val ∧ u ∈ g.val) →
      ∀ f ∈ R, u ∉ f.val)
    (hRL : ∀ u, (∃ f ∈ R, ∃ g : G.edgeSet, g ∉ R ∧ u ∈ f.val ∧ u ∈ g.val) →
      ∀ f ∈ L, u ∉ f.val) :
    Disjoint L R := by
  have hexpand : ∀ u (e : G.edgeSet), e ∈ L → e ∈ R → u ∈ e.val →
      ∀ g : G.edgeSet, u ∈ g.val → g ∈ L ∧ g ∈ R := by
    intro u e heL heR hue g hug
    constructor
    · by_contra hg
      exact hLR u ⟨e,heL,g,hg,hue,hug⟩ e heR hue
    · by_contra hg
      exact hRL u ⟨e,heR,g,hg,hue,hug⟩ e heL hue
  let P := fun u => ∀ g : G.edgeSet, u ∈ g.val → g ∈ L ∧ g ∈ R
  have hstep : ∀ {u v}, G.Adj u v → P u → P v := by
    intro u v huv hu
    let e : G.edgeSet := ⟨s(u,v),G.mem_edgeSet.mpr huv⟩
    have he := hu e (Sym2.mem_mk_left _ _)
    exact hexpand v e he.1 he.2 (Sym2.mem_mk_right _ _)
  have hprop : ∀ {u v}, G.Reachable u v → P u → P v := by
    rintro u v ⟨p⟩
    induction p with
    | nil => exact id
    | cons huv p ih => exact fun hu => ih (hstep huv hu)
  have hout : ∀ e : G.edgeSet, e.val.out.1 ∈ e.val := by
    intro e
    have hpair : s(e.val.out.1,e.val.out.2)=e.val := Quot.out_eq _
    have hm := Sym2.mem_mk_left e.val.out.1 e.val.out.2
    rw [hpair] at hm
    exact hm
  apply Finset.disjoint_left.mpr
  intro e heL heR
  obtain ⟨g,hg⟩ := hproper
  have hp : P e.val.out.1 := hexpand _ e heL heR (hout e)
  have hpg := hprop (hconn e.val.out.1 g.val.out.1) hp
  exact hg (hpg g (hout g)).1

/-- The same hypotheses give disjoint incident VERTEX sets, so a removed-bond
walk cannot switch from one reveal to the other through a shared endpoint. -/
theorem disjoint_reveal_vertices_of_opposite_attachment_avoidance
    {V : Type*} (G : SimpleGraph V) (hconn : G.Preconnected)
    (L R : Configuration G) (hproper : ∃ g : G.edgeSet, g ∉ L)
    (hLR : ∀ u, (∃ f ∈ L, ∃ g : G.edgeSet, g ∉ L ∧ u ∈ f.val ∧ u ∈ g.val) →
      ∀ f ∈ R, u ∉ f.val)
    (hRL : ∀ u, (∃ f ∈ R, ∃ g : G.edgeSet, g ∉ R ∧ u ∈ f.val ∧ u ∈ g.val) →
      ∀ f ∈ L, u ∉ f.val) :
    Disjoint {u | ∃ f ∈ L, u ∈ f.val} {u | ∃ f ∈ R, u ∈ f.val} := by
  have hd := disjoint_reveals_of_opposite_attachment_avoidance G hconn L R hproper hLR hRL
  apply Set.disjoint_left.mpr
  rintro u ⟨f,hf,huf⟩ ⟨g,hg,hug⟩
  have hgn : g ∉ L := fun h => Finset.disjoint_left.mp hd h hg
  exact hLR u ⟨f,hf,g,hgn,huf,hug⟩ g hg hug

end PottsContinuity.Push
