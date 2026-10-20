module

public import PottsContinuity.Thm3.Push.PositiveTipRecordSelector
public import PottsContinuity.Thm3.Push.CaseTwoTipFirstHitPath

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- All attained tip records, including tips on the source bottom side. -/
abbrev CaseTwoTipEndpointRecord (n s : ℕ) :=
  SideCollarFirstHitRecord (5*s) (2*n) × RectangleVertex (0,0) (2*n) (2*n)

/-- Preserve every successful source tip and its actual last vertex. -/
def caseTwoTipEndpointSelector (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Option (CaseTwoTipEndpointRecord n s) :=
  (caseTwoTipFirstHitSelector n s hfit C).bind fun tip =>
    (caseTwoTipOriginalTrace n s hfit tip).getLast?.map fun v => (tip,v)

/-- No positive-height restriction is imposed by the endpoint record. -/
theorem caseTwoTipEndpointSelector_eq_some_iff
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n)) :
    caseTwoTipEndpointSelector n s hfit C = some (tip,v) ↔
      caseTwoTipFirstHitSelector n s hfit C = some tip ∧
      (caseTwoTipOriginalTrace n s hfit tip).getLast? = some v := by
  constructor
  · intro h
    obtain ⟨r,hr,hmap⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w,hw,he⟩ := Option.map_eq_some_iff.mp hmap
    have hrEq : r = tip := congrArg Prod.fst he
    have hwEq : w = v := congrArg Prod.snd he
    subst r
    subst w
    exact ⟨hr,hw⟩
  · rintro ⟨htip,hlast⟩
    simp only [caseTwoTipEndpointSelector,htip,Option.bind_some,hlast,Option.map_some]

/-- The actual first selector has the exact full side-arm success event,
including the height-zero branch needed by the source product consumer. -/
theorem caseTwoTipEndpointSelector_isSome_iff
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    (caseTwoTipEndpointSelector n s hfit C).isSome ↔ C ∈ sourceCaseTwoSecondArm n s := by
  rw [← caseTwoTipFirstHitSelector_isSome_iff n s hfit C]
  cases htip : caseTwoTipFirstHitSelector n s hfit C with
  | none => simp only [caseTwoTipEndpointSelector,htip,Option.bind_none,Option.isSome_none]
  | some tip =>
    obtain ⟨a,b,p,ha,hal,har,hb,hp,hbounds,hfirst⟩ :=
      caseTwoTipFirstHitSelector_original_path n s hfit C tip htip
    have hsupport : p.val.support = caseTwoTipOriginalTrace n s hfit tip := hp
    have hlast : (caseTwoTipOriginalTrace n s hfit tip).getLast? = some b := by
      rw [← hsupport,List.getLast?_eq_some_getLast p.val.support_ne_nil,SimpleGraph.Walk.getLast_support]
    simp only [caseTwoTipEndpointSelector,htip,Option.bind_some,hlast,Option.map_some,Option.isSome_some]

local instance allHeightTipEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance allHeightTipEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Fintype.ofFinite _

/-- Positive tips use their right reveal; other endpoint records expose all
source bonds. This retains the full first-arm event without a locality gap. -/
def caseTwoTipEndpointReveal (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) : Configuration (rectangleGraph (0,0) (2*n) (2*n)) := by
  classical
  exact if 0 < b.2.val.2 then caseTwoTipRightReveal n s hfit b.1 b.2 else Finset.univ

/-- First-stage locality holds for every attained endpoint record. -/
theorem caseTwoTipEndpointSelector_oneSidedStable
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C D : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hstates : D ∩ caseTwoTipEndpointReveal n s hfit b =
      C ∩ caseTwoTipEndpointReveal n s hfit b) :
    caseTwoTipEndpointSelector n s hfit D = some b := by
  classical
  obtain ⟨htip,hlast⟩ := (caseTwoTipEndpointSelector_eq_some_iff n s hfit C b.1 b.2).mp hb
  by_cases hy : 0 < b.2.val.2
  · apply (caseTwoTipEndpointSelector_eq_some_iff n s hfit D b.1 b.2).mpr
    refine ⟨?_,hlast⟩
    apply caseTwoTipFirstHitSelector_stable_on_right_augmented_of_pos_height
      n s hs hfit C D b.1 b.2 htip hlast hy
    simpa only [caseTwoTipEndpointReveal,ite_eq_left hy,caseTwoTipRightReveal] using hstates
  · have hDC : D = C := by
      simpa only [caseTwoTipEndpointReveal,ite_eq_right hy,Finset.inter_univ] using hstates
    exact hDC ▸ hb

end
end PottsContinuity.Push
