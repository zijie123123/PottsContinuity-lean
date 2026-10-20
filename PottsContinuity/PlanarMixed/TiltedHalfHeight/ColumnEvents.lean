module

public import PottsContinuity.Thm3.Prop4.TiltedBondReflection
public import PottsContinuity.Thm3.Prop4.TiltedIncidentEvents

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial MeasureTheory
noncomputable section
local instance routeTwelveColumnEdgeDecidableEq (N : ℕ) (t : ℝ) :
    DecidableEq (tiltedStripGraph N t).edgeSet := Classical.decEq _
local instance routeTwelveColumnBondDecidableEq (N : ℕ) (t : ℝ) :
    DecidableEq (TiltedBond N t) := Classical.decEq _

/-- The at most N+1 candidate vertical bonds above the lowest column vertex. -/
def verticalColumnIndices (N : ℕ) (t : ℝ) (x : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range (N+1)).filter
    (fun i => (⌈t*(x:ℝ)⌉:ℝ)+(i:ℝ)+1 ≤ t*(x:ℝ)+(N:ℝ))

/-- Each retained candidate is an actual original strip bond. -/
def verticalColumnBond (N : ℕ) (t : ℝ) (x : ℤ)
    (i : {i // i∈verticalColumnIndices N t x}) : TiltedBond N t := by
  let y : ℤ := ⌈t*(x:ℝ)⌉+(i.val:ℤ)
  have hbot : t*(x:ℝ)≤(y:ℝ) := by
    have hc := Int.le_ceil (t*(x:ℝ))
    have hi : (0:ℝ) ≤ (i.val:ℝ) := Nat.cast_nonneg _
    dsimp [y]
    push_cast
    linarith
  have htop : (y:ℝ)+1 ≤ t*(x:ℝ)+(N:ℝ) := by
    have hi := (Finset.mem_filter.mp i.property).2
    simpa [y] using hi
  exact ⟨⟨(x,y),.vertical⟩,by
    constructor <;> simp only [tiltedStripVertices,Set.mem_ofPred_eq,
      tiltedHeight,LatticeBond.source,LatticeBond.target]
    · constructor <;> linarith
    · push_cast
      constructor <;> linarith⟩

/-- All actual vertical bonds in one original strip column. -/
def verticalColumnBonds (N : ℕ) (t : ℝ) (x : ℤ) : Finset (TiltedBond N t) :=
  (verticalColumnIndices N t x).attach.image (verticalColumnBond N t x)

/-- The corresponding genuine original-edge family. -/
def verticalColumnEdges (N : ℕ) (t : ℝ) (x : ℤ) :
    Finset (tiltedStripGraph N t).edgeSet :=
  (verticalColumnBonds N t x).image (tiltedBondEdge N t)

/-- The edge budget is uniform in the slope and column. -/
theorem verticalColumnEdges_card_le (N : ℕ) (t : ℝ) (x : ℤ) :
    (verticalColumnEdges N t x).card≤N+1 := by
  calc
    _ ≤ (verticalColumnBonds N t x).card := Finset.card_image_le
    _ ≤ (verticalColumnIndices N t x).attach.card := Finset.card_image_le
    _ = (verticalColumnIndices N t x).card := Finset.card_attach
    _ ≤ (Finset.range (N+1)).card := Finset.card_filter_le _ _
    _ = N+1 := Finset.card_range _

/-- No actual vertical bond at the given column is missing from the family. -/
theorem mem_verticalColumnBonds_iff (N : ℕ) (t : ℝ) (x : ℤ) (b : TiltedBond N t) :
    b∈verticalColumnBonds N t x ↔ b.val.axis=.vertical ∧ b.val.base.1=x := by
  classical
  constructor
  · intro hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨rfl,rfl⟩
  · rintro ⟨haxis,hx⟩
    let y := b.val.base.2
    let d : ℤ := y-⌈t*(x:ℝ)⌉
    have hybot : t*(x:ℝ)≤(y:ℝ) := by
      have h := b.property.1.1
      simpa [tiltedHeight,LatticeBond.source,hx,y] using h
    have hytop : (y:ℝ)+1≤t*(x:ℝ)+(N:ℝ) := by
      have h := b.property.2.2
      simpa [tiltedHeight,LatticeBond.target,haxis,hx,y,add_comm] using h
    have hd0 : 0≤d := by
      have hc := Int.ceil_le.mpr hybot
      dsimp [d]
      omega
    have hdN : d≤(N:ℤ) := by
      have hc := Int.le_ceil (t*(x:ℝ))
      have hreal : (d:ℝ)≤(N:ℝ) := by dsimp [d]; push_cast; linarith
      exact_mod_cast hreal
    have hcast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd0
    have hi : d.toNat∈verticalColumnIndices N t x := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · have hdreal : (d.toNat:ℝ)=(y:ℝ)-(⌈t*(x:ℝ)⌉:ℝ) := by
          have hZ : (d.toNat:ℤ)=y-⌈t*(x:ℝ)⌉ := hcast
          exact_mod_cast hZ
        rw [hdreal]
        linarith
    apply Finset.mem_image.mpr
    refine ⟨⟨d.toNat,hi⟩,by simp,?_⟩
    apply Subtype.ext
    have hb : b.val = ⟨b.val.base,b.val.axis⟩ := by cases b.val; rfl
    change (⟨(x,⌈t*(x:ℝ)⌉+(d.toNat:ℤ)),.vertical⟩ : LatticeBond)=b.val
    conv_rhs => rw [hb]
    congr 1
    · apply Prod.ext
      · exact hx.symm
      · dsimp [d,y] at hcast
        omega
    · exact haxis.symm

/-- Normalized strip bonds are identified by their actual original edge. -/
theorem tiltedBondEdge_injective (N : ℕ) (t : ℝ) :
    Function.Injective (tiltedBondEdge N t) := by
  intro b c h
  apply Subtype.ext
  apply LatticeBond.toSym2_injective
  have hm := congrArg (fun e : (tiltedStripGraph N t).edgeSet =>
    Sym2.map Subtype.val e.val) h
  simpa [tiltedBondEdge,LatticeBond.toSym2] using hm

/-- Distinct vertical columns have disjoint actual original-edge families. -/
theorem verticalColumnEdges_disjoint (N : ℕ) (t : ℝ) {x y : ℤ} (hxy : x≠y) :
    Disjoint (verticalColumnEdges N t x) (verticalColumnEdges N t y) := by
  apply Finset.disjoint_left.mpr
  intro e hex hey
  obtain ⟨b,hb,hbe⟩ := Finset.mem_image.mp hex
  obtain ⟨c,hc,hce⟩ := Finset.mem_image.mp hey
  have hbc := tiltedBondEdge_injective N t (hbe.trans hce.symm)
  subst c
  exact hxy (((mem_verticalColumnBonds_iff N t x b).mp hb).2.symm.trans
    ((mem_verticalColumnBonds_iff N t y b).mp hc).2)

/-- Fully open means every actual vertical original bond in this column is open. -/
def FullyOpenColumn (N : ℕ) (t : ℝ) (x : ℤ) (ω : TiltedConfiguration N t) : Prop :=
  ∀ b : TiltedBond N t, b.val.axis=.vertical → b.val.base.1=x →
    ω (tiltedBondEdge N t b)=true

/-- The physical definition equals the finite all-open original-edge event. -/
theorem fullyOpenColumn_iff_edges (N : ℕ) (t : ℝ) (x : ℤ) (ω : TiltedConfiguration N t) :
    FullyOpenColumn N t x ω ↔ ∀ e∈verticalColumnEdges N t x, ω e=true := by
  constructor
  · intro h e he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp he
    exact h b ((mem_verticalColumnBonds_iff N t x b).mp hb).1
      ((mem_verticalColumnBonds_iff N t x b).mp hb).2
  · intro h b haxis hx
    exact h _ (Finset.mem_image.mpr ⟨b,(mem_verticalColumnBonds_iff N t x b).mpr
      ⟨haxis,hx⟩,rfl⟩)

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
