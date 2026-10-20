module

public import PottsContinuity.PlanarMixed.FiniteSlit.DualEmbedding
public import PottsContinuity.PlanarMixed.OrderedCutActive
public import PottsContinuity.PD.FK.ConditionalLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier
public import PottsContinuity.PlanarMixed.SlitActiveReflection

/-! Actual finite active crossing-edge and complementary-state bijections.
Normalized edges follow the proved normalization pattern in SlitFiniteActiveEdges;
the carrier here includes the two finite outer wired arcs. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section
local instance finiteSlitActiveDualEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance finiteSlitActiveDualEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- An active normalized bond is its original sampled remaining edge. -/
def normalizedActiveEdgeEmbedding (M : ℕ) (x y : ℤ) :
    {b : LatticeBond // ActiveBond M x y b} ↪ (activeGraph M x y).edgeSet where
  toFun b := ⟨s(⟨b.val.source,b.property.1⟩,⟨b.val.target,b.property.2.1⟩),
    (activeGraph M x y).mem_edgeSet.mpr
      ((activeGraph_bond_adj_iff M x y b.val _ _).mpr b.property)⟩
  inj' := by
    intro b c h
    apply Subtype.ext
    apply LatticeBond.toSym2_injective
    exact congrArg (Sym2.map Subtype.val) (congrArg Subtype.val h)

/-- The unique normalized representative covers every active source edge. -/
theorem normalizedActiveEdgeEmbedding_surjective (M : ℕ) (x y : ℤ) :
    Function.Surjective (normalizedActiveEdgeEmbedding M x y) := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv := (activeGraph M x y).mem_edgeSet.mp he
    have hG := edgeRestriction_le (graph M x y) (internalEdges M x y) huv
    obtain ⟨b,hb⟩ := LatticeBond.exists_of_adj hG.1
    have hends := Sym2.eq_iff.mp hb
    have hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
      rcases hends with h | h
      · rw [h.1]; exact u.property
      · rw [h.1]; exact v.property
    have ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
      rcases hends with h | h
      · rw [h.2]; exact v.property
      · rw [h.2]; exact u.property
    have hedge : s(⟨b.source,hs⟩,⟨b.target,ht⟩) = s(u,v) :=
      Sym2.map.injective Subtype.val_injective hb
    have hadj : (activeGraph M x y).Adj ⟨b.source,hs⟩ ⟨b.target,ht⟩ := by
      apply (activeGraph M x y).mem_edgeSet.mp
      simpa only [hedge] using he
    exact ⟨⟨b,(activeGraph_bond_adj_iff M x y b hs ht).mp hadj⟩,Subtype.ext hedge⟩

def normalizedActiveEdgeEquiv (M : ℕ) (x y : ℤ) :
    {b : LatticeBond // ActiveBond M x y b} ≃ (activeGraph M x y).edgeSet :=
  Equiv.ofBijective (normalizedActiveEdgeEmbedding M x y)
    ⟨(normalizedActiveEdgeEmbedding M x y).injective,normalizedActiveEdgeEmbedding_surjective M x y⟩

/-- A sampled reflected bond is its literal finite dual edge. -/
def normalizedDualEdgeEmbedding (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    {b : LatticeBond // ActiveBond M x y b} ↪ (dualGraph M x y).edgeSet where
  toFun b := by
    have he := activeBond_reflected_endpoints_mem M x y hM hy hyM b.val b.property
    let u : Vertex M x := ⟨(slitReflectedBond x b.val).source,he.1⟩
    let v : Vertex M x := ⟨(slitReflectedBond x b.val).target,he.2⟩
    exact ⟨s(u,v),(dualGraph M x y).mem_edgeSet.mpr
      ((SimpleGraph.fromEdgeSet_adj _).mpr
        ⟨⟨b.val,b.property,rfl⟩,(slitReflectedBond x b.val).adjacent.ne⟩)⟩
  inj' := by
    intro b c h
    have hp := congrArg (Sym2.map Subtype.val) (congrArg Subtype.val h)
    have hb : slitReflectedBond x b.val = slitReflectedBond x c.val :=
      LatticeBond.toSym2_injective hp
    exact Subtype.ext ((slitReflectedBondEquiv x).injective hb)

/-- Every actual dual edge has its unique original active crossing edge. -/
theorem normalizedDualEdgeEmbedding_surjective (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    Function.Surjective (normalizedDualEdgeEmbedding M x y hM hy hyM) := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv := (dualGraph M x y).mem_edgeSet.mp he
    obtain ⟨⟨b,hb,hpair⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
    refine ⟨⟨b,hb⟩,Subtype.ext ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    exact hpair

def normalizedDualEdgeEquiv (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    {b : LatticeBond // ActiveBond M x y b} ≃ (dualGraph M x y).edgeSet :=
  Equiv.ofBijective (normalizedDualEdgeEmbedding M x y hM hy hyM)
    ⟨(normalizedDualEdgeEmbedding M x y hM hy hyM).injective,
      normalizedDualEdgeEmbedding_surjective M x y hM hy hyM⟩

/-- Crossing-edge bijection between the two actual sampled finite carriers. -/
def activeCrossingEdgeEquiv (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (activeGraph M x y).edgeSet ≃ (dualGraph M x y).edgeSet :=
  (normalizedActiveEdgeEquiv M x y).symm.trans (normalizedDualEdgeEquiv M x y hM hy hyM)

/-- Complement only the sampled active edges and transport their crossing labels. -/
def activeDualConfigurationEquiv (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    Configuration (activeGraph M x y) ≃ Configuration (dualGraph M x y) :=
  ({ toFun := fun C => Cᶜ, invFun := fun C => Cᶜ,
     left_inv := compl_compl, right_inv := compl_compl } :
    Configuration (activeGraph M x y) ≃ Configuration (activeGraph M x y)).trans
      (Equiv.finsetCongr (activeCrossingEdgeEquiv M x y hM hy hyM))

/-- Exact OPEN/CLOSED complement at corresponding sampled crossing edges. -/
theorem activeDualConfigurationEquiv_mem (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (C : Configuration (activeGraph M x y)) (e : (activeGraph M x y).edgeSet) :
    activeCrossingEdgeEquiv M x y hM hy hyM e ∈ activeDualConfigurationEquiv M x y hM hy hyM C ↔
      e ∉ C := by
  classical
  simp [activeDualConfigurationEquiv,Equiv.finsetCongr]

end
end PottsContinuity.PlanarMixed.FiniteSlit
