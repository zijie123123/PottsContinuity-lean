module

public import PottsContinuity.PlanarMixed.FiniteSlit.FirstContactCrop

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- The prescribed first-contact crop of two original open source walks
constructs reference crosscuts with exact support and bond-list images.
Forgetting openness does not change the crop index or its terminal bond. -/
theorem openSourceSquare_exists_crosscutData_at_firstContact
    (n : ℕ) (x y B : ℤ) (hx : 1 ≤ x) (hxn : x ≤ (2*n:ℕ))
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a u)
    (q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0) (hu : u.val.1 = B)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1) (hv : v.val = (x,y))
    (hp : ∀ w ∈ p.support, w.val.1 ≤ B)
    (hq : ∀ w ∈ q.support, x ≤ w.val.1 ∧ w.val.1 ≤ B)
    (hdis : ∀ w ∈ p.support, w ∉ q.support)
    (k : ℕ) (hk : IsFirstContact p {w | w.val.1 = x-1 ∧ y ≤ w.val.2} k) :
    let f := sourceSquareSlitEmbedding n x (by omega) hxn
    ∃ D : CrosscutData (2*n+2) x y,
      D.firstStart = f a ∧ D.secondStart = f b ∧
      D.firstEnd = f (p.getVert k) ∧ D.secondEnd = f v ∧
      D.first.support = (p.take k).support.map f ∧
      D.second.support = q.support.map f ∧
      D.first.edges = (p.take k).edges.map (Sym2.map f) ∧
      D.second.edges = q.edges.map (Sym2.map f) := by
  let p₀ := p.mapLe (openGraph_le _ C)
  let q₀ := q.mapLe (openGraph_le _ C)
  have hk₀ := (isFirstContact_mapLe_iff (openGraph_le _ C) p _ k).mpr hk
  obtain ⟨D,hDa,hDb,hDt,hDu,hPs,hQs,hPe,hQe⟩ :=
    sourceSquare_exists_crosscutData_at_firstContact n x y B hx hxn p₀ q₀ ha hb hu hxa hab hv
      (by simpa only [p₀,SimpleGraph.Walk.support_mapLe_eq_support] using hp)
      (by simpa only [q₀,SimpleGraph.Walk.support_mapLe_eq_support] using hq)
      (by simpa only [p₀,q₀,SimpleGraph.Walk.support_mapLe_eq_support] using hdis) k hk₀
  refine ⟨D,hDa,hDb,?_,hDu,?_,?_,?_,?_⟩
  · simpa only [p₀,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,
      SimpleGraph.Hom.ofLE_apply] using hDt
  · simpa only [p₀,SimpleGraph.Walk.support_take,
      SimpleGraph.Walk.support_mapLe_eq_support] using hPs
  · simpa only [q₀,SimpleGraph.Walk.support_mapLe_eq_support] using hQs
  · simpa only [p₀,SimpleGraph.Walk.edges_take,
      SimpleGraph.Walk.edges_mapLe_eq_edges] using hPe
  · simpa only [q₀,SimpleGraph.Walk.edges_mapLe_eq_edges] using hQe

end
end PottsContinuity.PlanarMixed.FiniteSlit
