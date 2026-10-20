module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceClosedPathGraph
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceTip

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section
local instance closedBandIdentificationEdgeEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
include hM hy

/-- The first marked path cannot meet the opposite reference wired arc. -/
theorem first_support_not_beta (u : Vertex M x) (hu : u ∈ D.first.support) :
    u ∉ beta M x y := by
  intro hbeta
  obtain ⟨z,hz,hzsecond⟩ := (D.orderedCuts hM hy).first_right u hu u hbeta .nil
  have he : z = u := by simpa using hz
  exact D.disjoint u hu (he ▸ hzsecond)

variable (w h : ℕ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
  (hp : ∀ v ∈ D.first.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hq : ∀ v ∈ D.second.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
  (hyh : y ≤ (h:ℤ))
local notation "r" => D.rank hM hy
local notation "G" => rankedBandGraph (graph M x y) r
local notation "R" => bandArcBonds (graph M x y) r
local notation "i" => D.sourceRectangleEmbedding hM hy w h hx hxw hp hq
local notation "f" => rectangleIntoReference M x w h (Nat.one_le_of_lt hM) hleft.le hright.le hh.le
include hleft hright hh hyh
variable (P : SourceWalkPair (rectangleGraph (0,0) w h))
  (hPs : D.first.support = P.first.support.map (rectangleIntoReference M x w h
    (Nat.one_le_of_lt hM) hleft.le hright.le hh.le))
  (hQs : D.second.support = P.second.support.map (rectangleIntoReference M x w h
    (Nat.one_le_of_lt hM) hleft.le hright.le hh.le))
  (htip : P.secondEnd.val.2 = y)
include hleft hright hh hyh hPs hQs htip

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
