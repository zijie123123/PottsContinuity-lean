module

public import PottsContinuity.Thm3.RSW.StripClosedCutRecordLaw
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutCylinderSupport
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinderRestriction
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinders
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open FKC.Medial FKC.FiniteFK
open PD.FK Exploration MeasureTheory Filter Topology
noncomputable section
attribute [local instance] PD.FK.configurationMeasurableSpace

local instance pdCutConditionalCylinderOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance pdCutConditionalCylinderOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance pdCutConditionalCylinderIntervalEdgeFintype (n : ℕ) (lo hi : ℤ) :
    Fintype (FKC.rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).edgeSet := Fintype.ofFinite _

/-- Under a successful two-sided closed-cut record, the original outer
cylinder has the same conditional probability as its literal restriction to
the selected interval. The queried edge set is required to lie in that
interval. -/
theorem stripClosedCutRecord_cylinder_probability_le_topOnly
    {N n K : ℕ} (hKN : K ≤ N) (q : Parameters)
    (ξ : PD.FK.BoundaryCondition (FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (A₀ : PD.FK.Configuration (horizontalStripCutRectangle N n))
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A₀).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A₀).2 = some j)
    (F : Finset FKC.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range
      (rectanglePrimalEdgeToSquareEdge
        (-(N : ℤ) + (i : ℤ) + 1, 0)
        ((N : ℤ) - 1 - (j : ℤ) - (-(N : ℤ) + (i : ℤ) + 1)).toNat
        (2 * n)))
 :
    (((PD.FK.law (horizontalStripCutRectangle N n) q ξ).filter
      (Exploration.revealRecordEvent
        (fun A => horizontalStripClosedCutReveal N n K A) A₀)
      (by
        have hstable : ∀ C C', C' ∩ horizontalStripClosedCutReveal N n K C =
            C ∩ horizontalStripClosedCutReveal N n K C →
            horizontalStripClosedCutReveal N n K C' = horizontalStripClosedCutReveal N n K C := by
          intro C C' hAgree
          exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (fun A => horizontalStripClosedCutReveal N n K A) hstable A₀]
        exact PD.FK.frozenStateEvent_support q ξ _ _)).toMeasure
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      (PD.FK.measure (horizontalStripCutRectangle N n) q
      (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n))
      (horizontalStripRectangleCylinderEvent N n F)).toReal := by
  classical
  let : DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
  let lo : ℤ := -(N : ℤ) + (i : ℤ) + 1
  let hi : ℤ := (N : ℤ) - 1 - (j : ℤ)
  let w : ℕ := (hi - lo).toNat
  let G := horizontalStripCutRectangle N n
  let H := FKC.rectangleGraph (lo, 0) w (2 * n)
  have hcenter := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
  have hsEnds := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
  have hw : (w : ℤ) = hi - lo := by
    dsimp [w]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
  have hleft : -(N : ℤ) < lo := by dsimp [lo]; exact hsEnds.1
  have hright : lo + (w : ℤ) < N := by
    have hsum : lo + (hi - lo) = hi := by dsimp [lo, hi]; omega
    rw [hw, hsum]
    exact hsEnds.2
  have hlo : -(N : ℤ) ≤ lo := le_of_lt hleft
  have hhi : hi ≤ N := le_of_lt hsEnds.2
  have hle : lo ≤ hi := by omega
  have hrightWeak : lo + (w : ℤ) ≤ N := le_of_lt hright
  let f : FKC.RectangleVertex (lo, 0) w (2 * n) ↪
      FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripIntervalEmbedding hlo hrightWeak
  have hGH : H.map f ≤ G := horizontalStripInterval_map_le hlo hrightWeak
  let reveal : PD.FK.Configuration G → PD.FK.Configuration G :=
    fun A => horizontalStripClosedCutReveal N n K A
  have hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C := by
    intro C C' hAgree
    exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
  have hsupp : ∃ C ∈ Exploration.revealRecordEvent reveal A₀, C ∈ (PD.FK.law G q ξ).support := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal hstable A₀]
    exact PD.FK.frozenStateEvent_support q ξ _ _
  let P := (PD.FK.law G q ξ).filter (Exploration.revealRecordEvent reveal A₀) hsupp
  have hLaw : P.map (PD.FK.embeddedConfigurationRestriction H G f hGH) =
      PD.FK.law H q (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n)) := by
    simpa [P, G, H, f, hGH, lo, hi, w] using
      stripClosedCutRecord_law_map_interval_topOnly
        N n K hKN q ξ hξ hTop A₀ hL hR
  let fcut : FKC.RectangleVertex (lo, 0) w (2 * n) ↪
      FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripCutWindowIntervalEmbedding hlo hhi hle
  have hf : f = fcut := by
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    exact Prod.ext rfl rfl
  let hGcut : H.map fcut ≤ G := horizontalStripCutWindowInterval_map_le hlo hhi hle
  have hrestriction : ∀ A : PD.FK.Configuration G,
      A ∈ horizontalStripRectangleCylinderEvent N n F ↔
        PD.FK.embeddedConfigurationRestriction H G f hGH A ∈
          horizontalStripIntervalCylinderEvent lo w n F := by
    intro A
    have hcut := horizontalStripCutWindowIntervalCylinder_restrict_iff
      hlo hhi hle F hF A
    have hread : FKC.FiniteFK.embeddedConfigurationRestriction H G fcut hGcut A =
        PD.FK.embeddedConfigurationRestriction H G fcut hGcut A := by
      ext e
      rw [FKC.FiniteFK.mem_embeddedConfigurationRestriction,PD.FK.mem_embeddedConfigurationRestriction]
      have he : FKC.FiniteFK.embeddedEdgeEmbedding H G fcut hGcut e =
          PD.FK.embeddedEdgeEmbedding H G fcut hGcut e := by
        apply Subtype.ext
        rfl
      rw [he]
    change (A ∈ horizontalStripRectangleCylinderEvent N n F ↔
      FKC.FiniteFK.embeddedConfigurationRestriction H G fcut hGcut A ∈
        horizontalStripIntervalCylinderEvent lo w n F) at hcut
    rw [hread] at hcut
    simpa [f, fcut, hGcut, hGH, hf, G, H, lo, hi, w] using hcut
  let Eout := horizontalStripRectangleCylinderEvent N n F
  let Ein := horizontalStripIntervalCylinderEvent lo w n F
  have hpre : (PD.FK.embeddedConfigurationRestriction H G f hGH) ⁻¹' Ein = Eout := by
    ext A
    exact (hrestriction A).symm
  have hmeas : Measurable (PD.FK.embeddedConfigurationRestriction H G f hGH) := measurable_from_top
  have hmapMeasure : P.toMeasure.map (PD.FK.embeddedConfigurationRestriction H G f hGH) =
      (P.map (PD.FK.embeddedConfigurationRestriction H G f hGH)).toMeasure :=
    PMF.toMeasure_map (PD.FK.embeddedConfigurationRestriction H G f hGH) P hmeas
  have hprob : P.toMeasure Eout = PD.FK.measure H q
      (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n)) Ein := by
    calc
      P.toMeasure Eout = P.toMeasure
          ((PD.FK.embeddedConfigurationRestriction H G f hGH) ⁻¹' Ein) := by
            congr 1
            exact hpre.symm
      _ = (P.toMeasure.map (PD.FK.embeddedConfigurationRestriction H G f hGH)) Ein := by
            rw [Measure.map_apply hmeas MeasurableSpace.measurableSet_top]
      _ = (P.map (PD.FK.embeddedConfigurationRestriction H G f hGH)).toMeasure Ein := by
            rw [hmapMeasure]
      _ = (PD.FK.law H q (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n))).toMeasure Ein := by
            rw [hLaw]
      _ = PD.FK.measure H q (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n)) Ein := rfl
  have hp : (PD.FK.isolatedExtensionPullbackBoundary f
      (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n))).partition =
      (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n)).partition := by
    apply Setoid.ext
    intro u v
    change (f u=f v ∨ u.val.2=(2*n:ℤ) ∧ v.val.2=(2*n:ℤ)) ↔
      (u=v ∨ u.val.2=(2*n:ℤ) ∧ v.val.2=(2*n:ℤ))
    exact or_congr ⟨fun h => f.injective h,fun h => congrArg f h⟩ Iff.rfl
  have hLawTop := PD.FK.law_eq_of_boundary_partition_eq (G:=H) q _ _ hp
  have hupper : IsUpperSet Ein := by
    intro A B hAB hA
    exact hA.trans (Finset.image_mono _ hAB)
  have hbound := embedded_boundary_probability_le H G f hGH q
    (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)) Ein hupper
  change ((PD.FK.law H q (PD.FK.isolatedExtensionPullbackBoundary f
    (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)))).toMeasure Ein).toReal ≤
    (PD.FK.measure G q (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n))
      ((PD.FK.embeddedConfigurationRestriction H G f hGH) ⁻¹' Ein)).toReal at hbound
  rw [hLawTop,hpre] at hbound
  change (P.toMeasure Eout).toReal ≤ _
  rw [hprob]
  exact hbound

end
end PottsContinuity.RSW
