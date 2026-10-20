module

public import PottsContinuity.Thm3.Push.IntervalArmStripWindowEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Topology
noncomputable section
local instance stripSourceCylinderEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance stripSourceCylinderEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Fintype.ofFinite _

/-- Read every original bond of the translated source square from the actual
strip configuration. This is a literal restriction on the whole strip carrier. -/
def stripSourceSquareRestriction (n : ℕ) (x : ℤ) (ω : RSW.StripConfiguration n) :
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) :=
  boolConfigurationEquiv _ (fun e => ω ((intervalArmStripGraphEmbedding n x).mapEdgeSet e))

/-- The cylinder defined by a specified actual finite source-square event. -/
def stripSourceSquareEvent (n : ℕ) (x : ℤ)
    (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n)))) :
    Set (RSW.StripConfiguration n) := (stripSourceSquareRestriction n x) ⁻¹' E

/-- The source restriction reads precisely the original translated bond. -/
theorem mem_stripSourceSquareRestriction (n : ℕ) (x : ℤ) (ω : RSW.StripConfiguration n)
    (e : (rectangleGraph (0,0) (2*n) (2*n)).edgeSet) :
    e ∈ stripSourceSquareRestriction n x ω ↔
      ω ((intervalArmStripGraphEmbedding n x).mapEdgeSet e) = true := by
  exact mem_boolConfigurationEquiv _ _ e

/-- Every event on a finite source square is a clopen cylinder in the strip;
no path-choice or limiting-probability hypothesis is required. -/
theorem stripSourceSquareEvent_isClopen (n : ℕ) (x : ℤ)
    (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n)))) :
    IsClopen (stripSourceSquareEvent n x E) := by
  classical
  let F := Finset.univ.map (intervalArmStripGraphEmbedding n x).mapEdgeSet
  apply RSW.strip_isClopen_of_finite_support n F _
  intro ω η hagree
  have hrestriction : stripSourceSquareRestriction n x ω = stripSourceSquareRestriction n x η := by
    ext e
    rw [mem_stripSourceSquareRestriction,mem_stripSourceSquareRestriction]
    rw [hagree _ (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,rfl⟩)]
  change stripSourceSquareRestriction n x ω ∈ E ↔ stripSourceSquareRestriction n x η ∈ E
  rw [hrestriction]

end
end PottsContinuity.Push
