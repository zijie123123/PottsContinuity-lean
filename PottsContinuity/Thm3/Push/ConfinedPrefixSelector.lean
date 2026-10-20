module

public import PottsContinuity.Thm3.Push.SourceGeometryOfConfinedPath
public import Mathlib.Data.Prod.Lex

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance confinedPrefixSelectorEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance confinedPrefixSelectorVertexOrder (n : ℕ) :
    LinearOrder (RectangleVertex (0,0) (2*n) (2*n)) :=
  LinearOrder.lift' (fun v => toLex v.val) (fun _ _ he => Subtype.ext (toLex.injective he))

/-- A physical first-contact choice on the actual confined source graph.
Locality is deliberately a separate predicate. -/
structure ConfinedPrefixSelector (n s : ℕ) (hfit : 9*s ≤ 2*n) where
  selectPrefix : CaseTwoTipEndpointRecord n s →
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
    Option (List (RectangleVertex (0,0) (2*n) (2*n)))
  search : ∀ C b,
    caseTwoConfinedPrefixConfiguration n s hfit b C ∈
      arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
        (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
        {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} → (selectPrefix b C).isSome
  firstContact : ∀ C b trace, selectPrefix b C = some trace →
    ConfinedPrefixFirstContact n s hfit C b trace

/-- Exact selected-value locality on the retained augmented record. -/
def ConfinedPrefixSelector.IsLocal {n s : ℕ} {hfit : 9*s ≤ 2*n}
    (D : ConfinedPrefixSelector n s hfit) : Prop :=
  ∀ C C' b trace,
    caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
    D.selectPrefix b C = some trace →
    C' ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
      C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → D.selectPrefix b C' = some trace

/-- A local physical first-contact selector supplies every source-system
field. Source geometry is derived from its literal sampled walk data. -/
def ConfinedPrefixSelector.toDirectPrefixSystem {n s : ℕ} {hfit : 9*s ≤ 2*n}
    (D : ConfinedPrefixSelector n s hfit) (hs : 1 ≤ s) (hlocal : D.IsLocal) :
    CaseTwoDirectPrefixSystem n s hfit where
  selectPrefix := D.selectPrefix
  locality := hlocal
  search := D.search
  paths C b trace hb hpref := confinedPrefixFirstContact_sourcePaths n s hs hfit C b trace hb
    (D.firstContact C b trace hpref)

/-- The remaining finite geometric interface at the exact ceiling scale. -/
def RoundedLocalConfinedPrefixSelectorExists (n : ℕ) (hn : 13 ≤ n) : Prop :=
  ∃ D : ConfinedPrefixSelector n ((n+8)/9)
    ((rounded_source_both_rectangles_fit n (by omega) (by omega)).1), D.IsLocal

/-- Local confined choice discharges the entire rounded physical system. -/
theorem roundedDirectPrefixSystem_nonempty_of_localConfinedSelector
    (n : ℕ) (hn : 13 ≤ n) (hlocal : RoundedLocalConfinedPrefixSelectorExists n hn) :
    Nonempty (RoundedDirectPrefixSystem n hn) := by
  obtain ⟨D,hD⟩ := hlocal
  exact ⟨D.toDirectPrefixSystem (by omega) hD⟩

end
end PottsContinuity.Push
