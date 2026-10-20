module

public import PottsContinuity.Thm3.RSW.StripEventLimit
public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import PottsContinuity.BD12.TwoBlockConnectivity
public import PottsContinuity.Thm3.RSW.EmbeddedConfinedWalkLift
public import PottsContinuity.Thm3.RSW.StripEvents
public import PottsContinuity.PD.Duality.CrossingDuality

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PD.FK.Medial
noncomputable section
local instance stripCentralReadEdgeEq (n k : ℕ) :
    DecidableEq (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet := Classical.decEq _

/-- The complete central test rectangle is read on its original strip vertices. -/
def stripCentralRectangleEmbedding (n k : ℕ) :
    RectangleVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) ↪ stripVertices n where
  toFun v := ⟨v.val,by
    have hv := (mem_latticeRectangle (-(k:ℤ)*n,0) v.val (2*k*n) (2*n)).mp v.property
    change -(n:ℤ) ≤ v.val.2 ∧ v.val.2 ≤ 3*(n:ℤ)
    simp only [zero_add,Nat.cast_mul,Nat.cast_ofNat] at hv
    constructor <;> omega⟩
  inj' := by
    intro u v huv
    have hv : u.val = v.val := congrArg (fun z : stripVertices n => z.val) huv
    exact Subtype.ext hv

theorem stripCentralRectangle_map_le (n k : ℕ) :
    (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).map (stripCentralRectangleEmbedding n k) ≤
      stripGraph n := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hxy

/-- The actual central original-bond restriction, for every strip sample. -/
def stripCentralRectangleConfiguration (n k : ℕ) (ω : StripConfiguration n) :
    Configuration (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)) :=
  boolConfigurationEquiv _ (fun e => ω (embeddedEdgeEmbedding _ _
    (stripCentralRectangleEmbedding n k) (stripCentralRectangle_map_le n k) e))

/-- The complete complementary dual state of the SAME central original bonds. -/
def stripCentralDualConfiguration (n k : ℕ) (ω : StripConfiguration n) :
    Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)) :=
  rectanglePrimalDualConfigurationEquiv _ _ _ (stripCentralRectangleConfiguration n k ω)

/-- The central open graph is exactly the induced original strip sample,
with every sampled bond and every physical vertex retained. -/
def stripCentralOpenEmbedding (n k : ℕ) (ω : StripConfiguration n) :
    openGraph (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n))
      (stripCentralRectangleConfiguration n k ω) ↪g stripOpenGraph n ω where
  toFun := stripCentralRectangleEmbedding n k
  inj' := (stripCentralRectangleEmbedding n k).injective
  map_rel_iff' := by
    classical
    intro u v
    have hbase : (stripGraph n).Adj (stripCentralRectangleEmbedding n k u)
        (stripCentralRectangleEmbedding n k v) ↔
        (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).Adj u v := by
      change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 ↔
        |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
      rfl
    rw [stripOpenGraph,stripCentralRectangleConfiguration,openGraph_boolConfigurationEquiv]
    simp only [SimpleGraph.fromEdgeSet_adj,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hs,hstate⟩,hne⟩
      have hg : (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).Adj u v :=
        hbase.mp ((stripGraph n).mem_edgeSet.mp hs)
      refine ⟨⟨(rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).mem_edgeSet.mpr hg,?_⟩,?_⟩
      · exact hstate
      · exact fun h => hne (congrArg (stripCentralRectangleEmbedding n k) h)
    · rintro ⟨⟨hg,hstate⟩,hne⟩
      have hs : (stripGraph n).Adj (stripCentralRectangleEmbedding n k u)
        (stripCentralRectangleEmbedding n k v) :=
          hbase.mpr ((rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).mem_edgeSet.mp hg)
      exact ⟨⟨(stripGraph n).mem_edgeSet.mpr hs,hstate⟩,
        (stripCentralRectangleEmbedding n k).injective.ne hne⟩

/-- The finite central crossing is exactly the source strip crossing,
including every original endpoint and the full rectangle confinement. -/
theorem stripCentralRectangle_horizontal_iff (n k : ℕ) (ω : StripConfiguration n) :
    stripCentralRectangleConfiguration n k ω ∈
      rectangleHorizontalCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n) ↔
    ω ∈ stripHorizontalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) 0 (2*n) := by
  have hw : -(k:ℤ)*n + ((2*k*n:ℕ):ℤ) = (k:ℤ)*n := by push_cast; ring
  have hrect (z : RectangleVertex (-(k:ℤ)*n,0) (2*k*n) (2*n)) :
      z.val ∈ Set.Icc (-(k:ℤ)*n) ((k:ℤ)*n) ×ˢ Set.Icc (0:ℤ) (2*n) := by
    have hz := (mem_latticeRectangle _ z.val (2*k*n) (2*n)).mp z.property
    change (-(k:ℤ)*n ≤ z.val.1 ∧ z.val.1 ≤ (k:ℤ)*n) ∧
      0 ≤ z.val.2 ∧ z.val.2 ≤ 2*(n:ℤ)
    simp only [zero_add] at hz
    rw [hw] at hz
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz
  constructor
  · rintro ⟨u,v,hu,hv,⟨p⟩⟩
    let φ := stripCentralOpenEmbedding n k ω
    refine ⟨φ u,φ v,p.map φ.toHom,?_,?_,?_⟩
    · change u.val ∈ ({-(k:ℤ)*n}:Set ℤ) ×ˢ Set.Icc (0:ℤ) (2*n)
      exact ⟨(Finset.mem_filter.mp hu).2,(hrect u).2⟩
    · change v.val ∈ ({(k:ℤ)*n}:Set ℤ) ×ˢ Set.Icc (0:ℤ) (2*n)
      have hx := (Finset.mem_filter.mp hv).2
      change v.val.1 = -(k:ℤ)*n + ((2*k*n:ℕ):ℤ) at hx
      exact ⟨hx.trans hw,(hrect v).2⟩
    · intro z hz
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
      obtain ⟨v,_,rfl⟩ := hz
      exact hrect v
  · rintro ⟨u,v,p,hu,hv,hp⟩
    have hsource (z : stripVertices n) (hz : z ∈ p.support) :
        z.val ∈ PD.FK.latticeRectangle (-(k:ℤ)*n,0) (2*k*n) (2*n) := by
      rw [mem_latticeRectangle]
      simp only [zero_add]
      have ht := hp z hz
      change (-(k:ℤ)*n ≤ z.val.1 ∧ z.val.1 ≤ -(k:ℤ)*n + ((2*k*n:ℕ):ℤ)) ∧
        0 ≤ z.val.2 ∧ z.val.2 ≤ ((2*n:ℕ):ℤ)
      rw [hw]
      change (-(k:ℤ)*n ≤ z.val.1 ∧ z.val.1 ≤ (k:ℤ)*n) ∧
        0 ≤ z.val.2 ∧ z.val.2 ≤ 2*(n:ℤ) at ht
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using ht
    let u' : RectangleVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) := ⟨u.val,hsource u p.start_mem_support⟩
    let v' : RectangleVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) := ⟨v.val,hsource v p.end_mem_support⟩
    have hu' : stripCentralRectangleEmbedding n k u' = u := Subtype.ext rfl
    have hv' : stripCentralRectangleEmbedding n k v' = v := Subtype.ext rfl
    let p' := p.copy hu'.symm hv'.symm
    have hrange : ∀ z ∈ p'.support, z ∈ Set.range (stripCentralOpenEmbedding n k ω) := by
      intro z hz
      have hz' : z ∈ p.support := by simpa only [p',SimpleGraph.Walk.support_copy] using hz
      exact ⟨⟨z.val,hsource z hz'⟩,Subtype.ext rfl⟩
    obtain ⟨P,_⟩ := walk_lift_of_support_in_embedding_range (stripCentralOpenEmbedding n k ω) p' hrange
    refine ⟨u',v',?_,?_,⟨P⟩⟩
    · exact Finset.mem_filter.mpr ⟨u'.property,hu.1⟩
    · apply Finset.mem_filter.mpr
      refine ⟨v'.property,?_⟩
      change v.val.1 = -(k:ℤ)*n + ((2*k*n:ℕ):ℤ)
      exact hv.1.trans hw.symm

/-- Deterministic source crossing duality on the literal strip sample.
No finite or infinite FK dual-law identification is used in this equality. -/
theorem stripCentral_horizontal_complement_eq_dual (n k : ℕ) :
    (stripHorizontalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) 0 (2*n))ᶜ =
      {ω | stripCentralDualConfiguration n k ω ∈
        rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} := by
  ext ω
  change ω ∉ stripHorizontalCrossing n _ _ _ _ ↔ _
  rw [← stripCentralRectangle_horizontal_iff]
  exact rectangle_crossing_duality _ _ _ (stripCentralRectangleConfiguration n k ω)


/-- Exact probability of the literal complementary dual crossing, under
any probability law on the strip. This is deterministic duality plus the
measurability of the original finite-support crossing event. -/
theorem stripCentral_dual_crossing_probability_eq_complement
    (n k : ℕ) (μ : MeasureTheory.Measure (StripConfiguration n)) [MeasureTheory.IsProbabilityMeasure μ] :
    μ.real {ω | stripCentralDualConfiguration n k ω ∈
      rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} =
      1-μ.real (stripHorizontalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) 0 (2*n)) := by
  rw [← stripCentral_horizontal_complement_eq_dual]
  exact MeasureTheory.probReal_compl_eq_one_sub
    (stripHorizontalCrossing_isClopen n _ _ _ _).isOpen.measurableSet

/-- The small-horizontal branch gives the source dual vertical estimate
without any strip dual-law or reflection premise. The subsequent reflected
PRIMAL estimate is a separate step. -/
theorem selfDual_stripCentral_dual_vertical_lower_of_small_horizontal
    (q : Set.Ici (1:ℝ)) (k n : ℕ)
    (hsmall : selfDualStripHorizontalProbability q k n < 1/2) :
    (1/2:ℝ) ≤ (selfDualStripMeasure q n).real {ω | stripCentralDualConfiguration n k ω ∈
      rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} := by
  have hf : Int.floor ((k:ℝ)*(n:ℝ)) = (k:ℤ)*n := by
    rw [← Nat.cast_mul,Int.floor_natCast,Nat.cast_mul]
  have hp : (selfDualStripMeasure q n).real
      (stripHorizontalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) 0 (2*n)) < 1/2 := by
    simpa only [selfDualStripHorizontalProbability,hf,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hsmall
  rw [stripCentral_dual_crossing_probability_eq_complement]
  linarith

end
end PottsContinuity.RSW
