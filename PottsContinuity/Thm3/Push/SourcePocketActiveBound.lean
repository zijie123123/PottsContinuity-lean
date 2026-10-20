module

public import PottsContinuity.Thm3.Push.SourcePocketActiveCarrier
public import PottsContinuity.Thm3.Push.SlitBandPocketEmbeddedBound
public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleSeparatePathBound
public import PottsContinuity.PlanarMixed.EmbeddedBoundaryLower
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutActive
public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceActiveCarrier
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceTip

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance sourcePocketActiveBoundEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Delete the slit and both pocket-augmented exteriors from the original
source graph, retaining its original vertex carrier. -/
def sourcePocketActiveGraph (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h)) :=
  edgeRestriction (rectangleGraph (0,0) w h)
    (pocketAugmentedSourceReveal w h x P.secondEnd.val.2
      (Subtype.val '' {z | z ∈ P.first.support})
      (Subtype.val '' {z | z ∈ P.second.support}))

/-- The canonical mixed crossing bound on the actual augmented source
carrier. Every geometric and carrier comparison is discharged. -/
theorem source_pocketAugmented_separate_wired_paths_lower_bound
    (w h : ℕ) (x : ℤ) (P : SourceWalkPair (rectangleGraph (0,0) w h))
    (hgeometry : RetainedRectanglePathGeometry w h x P) (q : Set.Ici (1:ℝ)) :
    1/(1+(q:ℝ)^2) ≤
      (measure (sourcePocketActiveGraph w h x P) (criticalParameters q)
        (sourceSeparatePathBoundary w h x P hgeometry)
        (arcsConnectionEvent (sourcePocketActiveGraph w h x P)
          {z | z ∈ P.first.support} {z | z ∈ P.second.support})).toReal := by
  have hgeometry₀ := hgeometry
  rcases hgeometry₀ with ⟨hx,hxw,ha,hb,hu,huy,hv,hxa,hab,hcol,hdis,hfirst⟩
  obtain ⟨hy,D,_,_,_,_,hPs,hQs,_,_⟩ :=
    sourceRectangle_crosscutData_of_leftContactPrefix w h x P.secondEnd.val.2 hx hxw
      P.first P.second ha hb hxa hab ⟨hu,huy⟩ (Prod.ext hv rfl) hcol hdis hfirst
  have hpD : ∀ r ∈ D.first.support,
      0 ≤ r.val.1 ∧ r.val.1 ≤ (w:ℤ) ∧ r.val.2 ≤ (h:ℤ) := by
    intro r hr
    rw [hPs] at hr
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
    have hz := (PD.FK.mem_latticeRectangle _ _ _ _).mp z.property
    change 0 ≤ z.val.1 ∧ z.val.1 ≤ (w:ℤ) ∧ z.val.2 ≤ (h:ℤ)
    dsimp at hz
    omega
  have hqD : ∀ r ∈ D.second.support,
      0 ≤ r.val.1 ∧ r.val.1 ≤ (w:ℤ) ∧ r.val.2 ≤ (h:ℤ) := by
    intro r hr
    rw [hQs] at hr
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
    have hz := (PD.FK.mem_latticeRectangle _ _ _ _).mp z.property
    change 0 ≤ z.val.1 ∧ z.val.1 ≤ (w:ℤ) ∧ z.val.2 ≤ (h:ℤ)
    dsimp at hz
    omega
  let i := D.sourceRectangleEmbedding (by omega) hy w h hx hxw hpD hqD
  have hI : ∀ u : rankedBandVertices (D.rank (by omega) hy),
      u.val ∈ D.first.support → i u ∈ {z | z ∈ P.first.support} := by
    intro u hu
    rw [hPs] at hu
    obtain ⟨z,hz,hzu⟩ := List.mem_map.mp hu
    have he : i u = z := by
      apply Subtype.ext
      exact (congrArg Subtype.val hzu).symm
    exact he.symm ▸ hz
  have hJ : ∀ u : rankedBandVertices (D.rank (by omega) hy),
      u.val ∈ D.second.support → i u ∈ {z | z ∈ P.second.support} := by
    intro u hu
    rw [hQs] at hu
    obtain ⟨z,hz,hzu⟩ := List.mem_map.mp hu
    have he : i u = z := by
      apply Subtype.ext
      exact (congrArg Subtype.val hzu).symm
    exact he.symm ▸ hz
  have hyh : P.secondEnd.val.2 ≤ (h:ℤ) := by
    have hh := (PD.FK.mem_latticeRectangle _ _ _ _).mp P.secondEnd.property
    dsimp at hh
    omega
  have htP := coordinateTrace_eq_of_support_map
    (fun z : RectangleVertex (0,0) w h => z.val)
    (fun z : Vertex (2*(w+h)+2) x => z.val)
    (paddedRectangleReference w h x hx hxw) (fun _ => rfl) _ _ hPs
  have htQ := coordinateTrace_eq_of_support_map
    (fun z : RectangleVertex (0,0) w h => z.val)
    (fun z : Vertex (2*(w+h)+2) x => z.val)
    (paddedRectangleReference w h x hx hxw) (fun _ => rfl) _ _ hQs
  have hmap := sourceRectangle_pocket_active_map_le D (by omega) hy w h hx hxw hpD hqD
    (by omega) (by omega) (by omega) hyh
  rw [htP,htQ] at hmap
  exact slit_band_pockets_embedded_active_lower_bound q D (by omega) hy (by omega)
    (sourcePocketActiveGraph w h x P)
    ((pocketInclusion (slitBandPocketCarrier D (by omega) hy)).trans i) hmap
    {z | z ∈ P.first.support} {z | z ∈ P.second.support}
    hgeometry.supports_disjoint
    (fun u hu => hI u.val hu) (fun u hu => hJ u.val hu)

end
end PottsContinuity.Push
