module

public import PottsContinuity.Thm3.Push.SourceGeometryOfDirectPath

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 RSW Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Ordinary first-contact path data on the literal sampled confined graph.
There is no source-arm continuation or law assertion in this predicate. -/
def ConfinedPrefixFirstContact (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n))) : Prop :=
  ∃ a ∈ intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)),
    ∃ t : RectangleVertex (0,0) (2*n) (2*n),
      t.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ t.val.2 ∧
      ∃ p : (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
        (caseTwoConfinedPrefixConfiguration n s hfit b C)).Walk a t,
        p.support = trace ∧
        firstContactTrace {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} trace = some trace

/-- Physical confined first-contact data alone supplies all static geometry
required by the source bound. Tip avoidance follows from actual isolation. -/
theorem confinedPrefixFirstContact_sourcePaths
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n)))
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hpath : ConfinedPrefixFirstContact n s hfit C b trace) :
    Nonempty (CaseTwoDirectPrefixSourcePaths n s hfit C b trace) := by
  obtain ⟨a,ha,t,htx,hty,p,hp,hfirst⟩ := hpath
  have hne : a ≠ t := by
    intro h
    have ha' := ha.2.1
    rw [h] at ha'
    omega
  have havoid : ∀ z ∈ p.support, z ∉ caseTwoTipOriginalTrace n s hfit b.1 := by
    intro z hz htip
    have hiso : (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
        (caseTwoConfinedPrefixConfiguration n s hfit b C)).IsIsolated z := by
      intro v hv
      exact (openGraph_le _ _ hv).1.2.1 htip
    exact (SimpleGraph.Walk.not_nil_of_ne hne) (SimpleGraph.Walk.nil_of_isIsolated_of_mem_support hiso hz)
  let f : (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
      (caseTwoConfinedPrefixConfiguration n s hfit b C)) →g
      openGraph (rectangleGraph (0,0) (2*n) (2*n)) C := {
    toFun := id
    map_rel' := fun h => ((embeddedRestriction_openGraph_adj_iff _ _ (Function.Embedding.refl _)
      (caseTwoConfinedPrefixGraph_map_le n s hfit b) C _ _).mp h).2 }
  have hmap : (p.map f).support = trace := by
    rw [SimpleGraph.Walk.support_map]
    change p.support.map id = trace
    rw [List.map_id,hp]
  exact caseTwoDirectPrefixSourcePaths_of_open_first_contact n s hs hfit C b trace hb
    a ha t htx hty (p.map f) hmap hfirst (by simpa only [hp] using havoid)

end
end PottsContinuity.Push
