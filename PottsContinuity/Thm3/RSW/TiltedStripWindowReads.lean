module

public import PottsContinuity.Thm3.RSW.TiltedStripDualTransport
public import PottsContinuity.Thm3.Touch.FiniteStripSymmetry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 Thm3.Touch MeasureTheory
noncomputable section

/-- Genuine central-column bonds, deleting exactly the bonds whose crossed
half-turn has an endpoint outside the original tilted strip. -/
def tiltedStripCentralRetainedBond (N : ℕ) (t : ℝ) (k : ℕ) :=
  {b : TiltedBond N t //
    b.val.source ∈ tiltedColumnWindow N k t ∧
    b.val.target ∈ tiltedColumnWindow N k t ∧
    (tiltedStripCrossedBond N b.val).source ∈ tiltedStripVertices N t ∧
    (tiltedStripCrossedBond N b.val).target ∈ tiltedStripVertices N t}

/-- The exact original source-edge read. -/
def tiltedStripCentralSourceEdge (N : ℕ) (t : ℝ) (k : ℕ)
    (b : tiltedStripCentralRetainedBond N t k) : (tiltedStripGraph N t).edgeSet :=
  tiltedBondEdge N t b.val

/-- The genuine crossed-bond target edge; containment is part of retention. -/
def tiltedStripCentralReflectedEdge (N : ℕ) (t : ℝ) (k : ℕ)
    (b : tiltedStripCentralRetainedBond N t k) : (tiltedStripGraph N t).edgeSet :=
  tiltedBondEdge N t ⟨tiltedStripCrossedBond N b.val.val,b.property.2.2⟩

/-- Label the same genuine bond in the finite original column graph. -/
def tiltedStripCentralWindowEdge (N : ℕ) (t : ℝ) (k : ℕ)
    (b : tiltedStripCentralRetainedBond N t k) :
    (squareLattice.induce (tiltedColumnWindow N k t : Set (ℤ × ℤ))).edgeSet :=
  ⟨s(⟨b.val.val.source,b.property.1⟩,⟨b.val.val.target,b.property.2.1⟩),
    (squareLattice.induce (tiltedColumnWindow N k t : Set (ℤ × ℤ))).mem_edgeSet.mpr
      b.val.val.adjacent⟩

/-- The dual labels do not duplicate any sampled original bond. -/
theorem tiltedStripCentralWindowEdge_injective (N : ℕ) (t : ℝ) (k : ℕ) :
    Function.Injective (tiltedStripCentralWindowEdge N t k) := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  apply LatticeBond.toSym2_injective
  have hp := congrArg (fun e => Sym2.map Subtype.val e.val) h
  simpa [tiltedStripCentralWindowEdge,LatticeBond.toSym2] using hp

instance tiltedStripCentralRetainedBond_finite (N : ℕ) (t : ℝ) (k : ℕ) :
    Finite (tiltedStripCentralRetainedBond N t k) :=
  Finite.of_injective _ (tiltedStripCentralWindowEdge_injective N t k)

/-- Complement the actual source bond, indexed by its genuine dual label. -/
def tiltedStripCentralDualConfiguration (N : ℕ) (t : ℝ) (k : ℕ)
    (ω : TiltedConfiguration N t) : tiltedStripCentralRetainedBond N t k → Bool :=
  fun b => !ω (tiltedStripCentralSourceEdge N t k b)

/-- Read the open state of the genuine reflected crossing bond on the same labels. -/
def tiltedStripReflectedCentralDualConfiguration (N : ℕ) (t : ℝ) (k : ℕ)
    (ω : TiltedConfiguration N t) : tiltedStripCentralRetainedBond N t k → Bool :=
  fun b => ω (tiltedStripCentralReflectedEdge N t k b)

end
end PottsContinuity.RSW
