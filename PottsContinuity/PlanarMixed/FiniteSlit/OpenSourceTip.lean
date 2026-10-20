module

public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceCrosscuts
public import PottsContinuity.Thm3.RSW.SlitTipPositive

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- The original disjoint open source arms force a strictly positive tip.
A zero-height return would interlace the bottom-to-right arm. -/
theorem disjoint_openSourceSquare_tip_pos
    (n : ℕ) (x y B : ℤ)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a u)
    (q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0) (hu : u.val.1 = B)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1) (hv : v.val = (x,y))
    (hq : ∀ w ∈ q.support, w.val.1 ≤ B)
    (hdis : ∀ w ∈ p.support, w ∉ q.support) : 0 < y := by
  let φ : openGraph (rectangleGraph (0,0) (2*n) (2*n)) C →g PD.FK.squareLattice := {
    toFun := Subtype.val
    map_rel' := fun h => openGraph_le _ C h }
  let P := (p.map φ).copy (show a.val = (a.val.1,0) from Prod.ext rfl ha)
    (show u.val = (B,u.val.2) from Prod.ext hu rfl)
  let Q := (q.map φ).copy (show b.val = (b.val.1,0) from Prod.ext rfl hb) hv
  have hPs : P.support = p.support.map Subtype.val := by
    rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
    rfl
  have hQs : Q.support = q.support.map Subtype.val := by
    rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
    rfl
  have hnonneg (w : RectangleVertex (0,0) (2*n) (2*n)) : 0 ≤ w.val.2 := by
    have hw := (PD.FK.mem_latticeRectangle _ _ _ _).mp w.property
    dsimp at hw
    omega
  apply disjoint_bottom_right_walk_tip_pos a.val.1 b.val.1 B u.val.2 x y
    hxa hab.le (hq b q.start_mem_support) P Q
  · intro z hz
    rw [hPs] at hz
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
    exact hnonneg w
  · intro z hz
    rw [hQs] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact ⟨hq w hw,hnonneg w⟩
  · intro z hz hzQ
    rw [hPs] at hz
    rw [hQs] at hzQ
    obtain ⟨w,hw,hwz⟩ := List.mem_map.mp hz
    obtain ⟨t,ht,htz⟩ := List.mem_map.mp hzQ
    exact hdis w hw ((Subtype.ext (hwz.trans htz.symm)) ▸ ht)

/-- Coordinate traces are unchanged by an exact mapped support list. -/
theorem coordinateTrace_eq_of_support_map {V W Z : Type*}
    (σ : V → Z) (τ : W → Z) (f : V → W) (hf : ∀ v, τ (f v) = σ v)
    (s : List V) (t : List W) (ht : t = s.map f) :
    τ '' {w | w ∈ t} = σ '' {v | v ∈ s} := by
  rw [ht]
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact ⟨v,hv,(hf v).symm⟩
  · rintro ⟨v,hv,rfl⟩
    exact ⟨f v,List.mem_map.mpr ⟨v,hv,rfl⟩,hf v⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
