module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceCrosscuts

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- The actual first index at which a walk visits a specified vertex set.
The index is inside the walk, and every preceding vertex avoids the set. -/
def IsFirstContact {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (target : Set V) (k : ℕ) : Prop :=
  k ≤ p.length ∧ p.getVert k ∈ target ∧ ∀ j < k, p.getVert j ∉ target

/-- First-contact indices are unique, independently of how they are found. -/
theorem IsFirstContact.unique {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} {target : Set V} {k l : ℕ}
    (hk : IsFirstContact p target k) (hl : IsFirstContact p target l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim (hl.2.2 k h hk.2.1)
  · exact h
  · exact False.elim (hk.2.2 l h hl.2.1)

/-- Forgetting the open-edge certificate does not change a first contact. -/
theorem isFirstContact_mapLe_iff {V : Type*} {G H : SimpleGraph V}
    (hGH : G ≤ H) {a b : V} (p : G.Walk a b) (target : Set V) (k : ℕ) :
    IsFirstContact (p.mapLe hGH) target k ↔ IsFirstContact p target k := by
  simp only [IsFirstContact,SimpleGraph.Walk.length_mapLe,
    SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,SimpleGraph.Hom.ofLE_apply]

/-- Actual crosscuts are obtained at the recorded first left-slit contact.
The source provider supplies only the first-contact characterization, rather
than a separately chosen reference-domain crop or a matching interface. -/
theorem sourceSquare_exists_crosscutData_at_firstContact
    (n : ℕ) (x y B : ℤ) (hx : 1 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (rectangleGraph (0,0) (2*n) (2*n)).Walk a u)
    (q : (rectangleGraph (0,0) (2*n) (2*n)).Walk b v)
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
  obtain ⟨l,_,hl,hhit,hfirst,D,hD⟩ := sourceSquare_exists_crosscutData n x y B hx hxn
    p q ha hb hu hxa hab hv hp hq hdis
  have hkl := hk.unique (show IsFirstContact p {w | w.val.1 = x-1 ∧ y ≤ w.val.2} l from
    ⟨hl,hhit,hfirst⟩)
  subst l
  exact ⟨D,hD⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
