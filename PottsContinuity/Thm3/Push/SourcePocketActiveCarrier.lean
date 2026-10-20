module

public import PottsContinuity.Thm3.Push.SourcePocketExteriorProjection
public import PottsContinuity.Thm3.Push.SlitBandPocketActiveBound
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceActiveCarrier

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance sourcePocketActiveCarrierEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- On a seeded component, augmentation adds no exterior vertices. -/
theorem pocketAugmented_mem_iff_of_seeded {V : Type*} (G : SimpleGraph V)
    (cut left right : Set V) (v : V)
    (hv : v ∈ closedCutExterior G cut (left ∪ right)) :
    v ∈ pocketAugmentedCutExterior G cut left right ↔
      v ∈ closedCutExterior G cut right := by
  exact or_iff_left (show v ∉ (closedCutExterior G cut (left ∪ right))ᶜ from fun hn => hn hv)

/-- The reduced active reference band embeds into the literal source
carrier after both pocket-augmented exterior records have been deleted. -/
theorem sourceRectangle_pocket_active_map_le
    {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
    (w h : ℕ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hp : ∀ v ∈ D.first.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
    (hq : ∀ v ∈ D.second.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) :
    let H := (rankedBandGraph (graph M x y) (D.rank hM hy)).induce
      (slitBandPocketCarrier D hM hy)
    let f := (pocketInclusion (slitBandPocketCarrier D hM hy)).trans
      (D.sourceRectangleEmbedding hM hy w h hx hxw hp hq)
    (edgeRestriction H (slitBandPocketArcBonds D hM hy)).map f ≤
      edgeRestriction (rectangleGraph (0,0) w h)
        (pocketAugmentedSourceReveal w h x y
          (Subtype.val '' {v | v ∈ D.first.support})
          (Subtype.val '' {v | v ∈ D.second.support})) := by
  classical
  let r := D.rank hM hy
  let S := slitBandPocketCarrier D hM hy
  let H := (rankedBandGraph (graph M x y) r).induce S
  let k := D.sourceRectangleEmbedding hM hy w h hx hxw hp hq
  let i := rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega)
  have hp' : ∀ v ∈ D.first.support, v.val ∈ PD.FK.latticeRectangle (0,0) w h := by
    intro v hv
    have hvp := hp v hv
    have hvr := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    rw [PD.FK.mem_latticeRectangle]
    dsimp
    omega
  have hq' : ∀ v ∈ D.second.support, v.val ∈ PD.FK.latticeRectangle (0,0) w h := by
    intro v hv
    have hvp := hq v hv
    have hvr := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    rw [PD.FK.mem_latticeRectangle]
    dsimp
    omega
  have hpi := sourceCoordinateTrace_image_eq M x w h (by omega) (by omega) (by omega)
    (by omega) {v | v ∈ D.first.support} hp'
  have hqi := sourceCoordinateTrace_image_eq M x w h (by omega) (by omega) (by omega)
    (by omega) {v | v ∈ D.second.support} hq'
  have hki : ∀ v : rankedBandVertices r, i (k v) = v.val := fun v => Subtype.ext rfl
  have hL : ∀ v : S,
      k v.val ∈ pocketAugmentedSourceLeftExterior w h x y
        (sourceCoordinateTrace w h (Subtype.val '' {z | z ∈ D.first.support})) ↔
      k v.val ∈ sourceLeftExterior w h x y
        (sourceCoordinateTrace w h (Subtype.val '' {z | z ∈ D.first.support})) := by
    intro v
    rw [pocketAugmentedSourceLeftExterior_iff M x y w h hM hx hxw hleft hright hh hyh,
      sourceLeftExterior_iff M x y w h hM hx hxw hleft hright hh hyh, hpi]
    change i (k v.val) ∈ _ ↔ i (k v.val) ∈ _
    rw [hki]
    apply pocketAugmented_mem_iff_of_seeded
    simpa only [Set.union_comm] using v.property.1
  have hR : ∀ v : S,
      k v.val ∈ pocketAugmentedSourceRightExterior w h x y
        (sourceCoordinateTrace w h (Subtype.val '' {z | z ∈ D.second.support})) ↔
      k v.val ∈ sourceRightExterior w h x y
        (sourceCoordinateTrace w h (Subtype.val '' {z | z ∈ D.second.support})) := by
    intro v
    rw [pocketAugmentedSourceRightExterior_iff M x y w h hM hx hxw hleft hright hh hyh,
      sourceRightExterior_iff M x y w h hM hx hxw hleft hright hh hyh, hqi]
    change i (k v.val) ∈ _ ↔ i (k v.val) ∈ _
    rw [hki]
    exact pocketAugmented_mem_iff_of_seeded _ _ _ _ _ v.property.2
  dsimp only
  intro a b hab
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hab
  change (edgeRestriction (rectangleGraph (0,0) w h)
    (pocketAugmentedSourceReveal w h x y (Subtype.val '' {z | z ∈ D.first.support})
      (Subtype.val '' {z | z ∈ D.second.support}))).Adj (k u.val) (k v.val)
  obtain ⟨huvH,hn⟩ := (edgeRestriction_adj_exists_not_mem H _ u v).mp huv
  have hactive : (edgeRestriction (rankedBandGraph (graph M x y) r)
      (bandArcBonds (graph M x y) r)).Adj u.val v.val := by
    apply (edgeRestriction_adj_exists_not_mem _ _ _ _).mpr
    refine ⟨huvH,?_⟩
    intro he
    apply hn
    rw [mem_bandArcBonds_pair (graph M x y) r u.val v.val huvH] at he
    change _ ∈ internalBonds H {z | r z.val.val = 1} ∪ internalBonds H {z | r z.val.val = 3}
    rw [Finset.mem_union,mem_internalBonds_pair H _ u v huvH,mem_internalBonds_pair H _ u v huvH]
    exact he
  have hsource := D.sourceRectangle_active_graph_eq hM hy w h hx hxw hp hq hleft hright hh hyh
  have hsourceAdj : (edgeRestriction (rectangleGraph (0,0) w h)
      (sourceExteriorReveal w h x y (Subtype.val '' {z | z ∈ D.first.support})
        (Subtype.val '' {z | z ∈ D.second.support}))).Adj (k u.val) (k v.val) := by
    rw [hsource]
    exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨u.val,v.val,hactive,rfl,rfl⟩
  obtain ⟨hG,hnold⟩ := (edgeRestriction_adj_exists_not_mem _ _ _ _).mp hsourceAdj
  apply (edgeRestriction_adj_exists_not_mem _ _ _ _).mpr
  refine ⟨hG,?_⟩
  intro he
  apply hnold
  rw [pocketAugmentedSourceReveal,Finset.mem_union,Finset.mem_union,
    mem_internalBonds_pair _ _ _ _ hG,mem_internalBonds_pair _ _ _ _ hG] at he
  rw [sourceExteriorReveal,Finset.mem_union,Finset.mem_union,
    mem_internalBonds_pair _ _ _ _ hG,mem_internalBonds_pair _ _ _ _ hG]
  rcases he with hs | hleft | hright
  · exact Or.inl hs
  · exact Or.inr (Or.inl ⟨(hL u).mp hleft.1,(hL v).mp hleft.2⟩)
  · exact Or.inr (Or.inr ⟨(hR u).mp hright.1,(hR v).mp hright.2⟩)

end
end PottsContinuity.Push
