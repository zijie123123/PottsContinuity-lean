module

public import PottsContinuity.Thm3.Push.AllHeightTipSourceSplit
public import PottsContinuity.Thm3.Push.ConfinedStoppedPrefixGraph
public import PottsContinuity.Thm3.Push.PositiveTipPrefixDMP

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance completePrefixEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance completePrefixEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Fintype.ofFinite _

/-- Literal sampled connection of the two original source intervals. -/
abbrev caseTwoSourceIntervalConnection (n s : ℕ) :=
  arcsConnectionEvent (rectangleGraph (0,0) (2*n) (2*n))
    (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
    (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ)))

/-- Direct prefix takes precedence. Only a failed search may use the already
connected branch; every such branch will expose the full source sample. -/
def caseTwoCompletePrefixSelector (n s : ℕ) (_hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Option (Sum (List (RectangleVertex (0,0) (2*n) (2*n))) Unit) := by
  classical
  exact if 0 < b.2.val.2 then
    match selectPrefix b C with
    | some trace => some (.inl trace)
    | none => if C ∈ caseTwoSourceIntervalConnection n s then some (.inr ()) else none
  else if C ∈ caseTwoSourceIntervalConnection n s then some (.inr ()) else none

/-- A direct-prefix value is chosen exactly when the positive search chooses it. -/
theorem caseTwoCompletePrefixSelector_eq_inl_iff
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (trace : List (RectangleVertex (0,0) (2*n) (2*n))) :
    caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inl trace) ↔
      0 < b.2.val.2 ∧ selectPrefix b C = some trace := by
  classical
  by_cases hy : 0 < b.2.val.2
  · cases hp : selectPrefix b C with
    | none =>
      by_cases hc : C ∈ caseTwoSourceIntervalConnection n s
      · simp [caseTwoCompletePrefixSelector,hy,hp,hc]
      · simp [caseTwoCompletePrefixSelector,hy,hp,hc]
    | some t => simp [caseTwoCompletePrefixSelector,hy,hp]
  · by_cases hc : C ∈ caseTwoSourceIntervalConnection n s
    · simp [caseTwoCompletePrefixSelector,hy,hc]
    · simp [caseTwoCompletePrefixSelector,hy,hc]

/-- The fully observed alternative is always a genuine source connection. -/
theorem caseTwoCompletePrefixSelector_inr_connects
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hsel : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inr ())) :
    C ∈ caseTwoSourceIntervalConnection n s := by
  classical
  by_contra hc
  by_cases hy : 0 < b.2.val.2
  · cases hp : selectPrefix b C with
    | none => simp [caseTwoCompletePrefixSelector,hy,hp,hc] at hsel
    | some trace => simp [caseTwoCompletePrefixSelector,hy,hp] at hsel
  · simp [caseTwoCompletePrefixSelector,hy,hc] at hsel

/-- A source connection gives success regardless of the direct search result. -/
theorem caseTwoCompletePrefixSelector_isSome_of_connection
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hc : C ∈ caseTwoSourceIntervalConnection n s) :
    (caseTwoCompletePrefixSelector n s hfit selectPrefix b C).isSome := by
  classical
  by_cases hy : 0 < b.2.val.2
  · cases hp : selectPrefix b C with
    | none => simp only [caseTwoCompletePrefixSelector,ite_eq_left hy,hp,ite_eq_left hc,Option.isSome_some]
    | some trace => simp only [caseTwoCompletePrefixSelector,ite_eq_left hy,hp,Option.isSome_some]
  · simp only [caseTwoCompletePrefixSelector,ite_eq_right hy,ite_eq_left hc,Option.isSome_some]

/-- The second source-arm event implies completed second-stage success.
The search specification refers only to physical connection in the stopped
precursor rectangle, with no farther-boundary completion characterization. -/
theorem caseTwoCompletePrefixSelector_isSome_of_source_arm
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hsearch : ∀ C b,
      caseTwoConfinedPrefixConfiguration n s hfit b C ∈
        arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
          (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
          {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} → (selectPrefix b C).isSome)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hE : C ∈ sourceCaseTwoFirstArm n s) :
    (caseTwoCompletePrefixSelector n s hfit selectPrefix b C).isSome := by
  classical
  rcases caseTwoTipEndpoint_source_connection_or_native n s hs hfit C b hb hE with hc | ⟨D,hcol,hright,hend,htrace,hy⟩
  · exact caseTwoCompletePrefixSelector_isSome_of_connection n s hfit selectPrefix b C hc
  · have hphys := native_confined_prefix_connection_on_augmented_fiber n s hfit C C
      _ _ b D hcol hright hend htrace rfl
    have hsuc := hsearch C b hphys
    cases hp : selectPrefix b C with
    | none => simp only [hp,Option.isSome_none,Bool.false_eq_true] at hsuc
    | some trace => simp only [caseTwoCompletePrefixSelector,ite_eq_left hy,hp,Option.isSome_some]

/-- Direct records reveal only the retained cuts; the connection alternative
reveals all source bonds, including its determining connection test. -/
def caseTwoCompletePrefixSecondReveal (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s)
    (rec : Sum (List (RectangleVertex (0,0) (2*n) (2*n))) Unit) :
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) :=
  match rec with
  | .inl trace => caseTwoStoppedPrefixReveal n s hfit b trace
  | .inr _ => Finset.univ

/-- No locality hypothesis is needed for the connection alternative. Only
selected-value locality of the successful direct search remains explicit. -/
theorem caseTwoCompletePrefixSelector_stable_of_prefixLocality
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hprefix : ∀ C D b trace,
      caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
      selectPrefix b C = some trace →
      D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
        C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace)
    (C D : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (rec : Sum (List (RectangleVertex (0,0) (2*n) (2*n))) Unit)
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hr : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some rec)
    (hstates : D ∩ caseTwoCompletePrefixSecondReveal n s hfit b rec =
      C ∩ caseTwoCompletePrefixSecondReveal n s hfit b rec) :
    caseTwoCompletePrefixSelector n s hfit selectPrefix b D = some rec := by
  cases rec with
  | inl trace =>
    obtain ⟨hy,htrace⟩ := (caseTwoCompletePrefixSelector_eq_inl_iff n s hfit selectPrefix b C trace).mp hr
    apply (caseTwoCompletePrefixSelector_eq_inl_iff n s hfit selectPrefix b D trace).mpr
    exact ⟨hy,hprefix C D b trace hb hy htrace hstates⟩
  | inr u =>
    have hDC : D = C := by simpa only [caseTwoCompletePrefixSecondReveal,Finset.inter_univ] using hstates
    exact hDC ▸ hr

end
end PottsContinuity.Push
