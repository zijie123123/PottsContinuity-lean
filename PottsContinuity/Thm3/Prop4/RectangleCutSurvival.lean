module

public import PottsContinuity.Thm3.Prop4.SampledCutProduct

/-!
# Actual endpoint arms surviving any sampled column cut

Adapted from the existing TubeArms proof. The cut keeps its original sampled
edge carrier and only its column geometry is used; no endpoint connection
is assumed to persist after the cut.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

private theorem rectangle_walk_reaches_cut_after_closing {V : Type*} (G : SimpleGraph V)
    [DecidableEq G.edgeSet] (A F : PD.FK.Configuration G) (h : V → ℤ) (k : ℤ)
    (hstep : ∀ a b, G.Adj a b → h b ≤ h a+1)
    (hsafe : ∀ a b, h a ≤ k → h b ≤ k → ∀ e ∈ F, e.val ≠ s(a,b))
    {a b : V} (w : (PD.FK.openGraph G A).Walk a b)
    (ha : h a ≤ k) (hb : k < h b) :
    ∃ z : V, h z = k ∧ PD.FK.ActualConnected G (A \ F) a z := by
  induction w with
  | nil => omega
  | @cons a c b hac w ih =>
    obtain ⟨e,he,heval⟩ := (PD.FK.openGraph_adj G A a c).mp hac
    have hG : G.Adj a c := G.mem_edgeSet.mp (by rw [← heval]; exact e.property)
    by_cases hc : k < h c
    · refine ⟨a, ?_, SimpleGraph.Reachable.refl a⟩
      have hs := hstep a c hG
      omega
    · have hc' : h c ≤ k := by omega
      obtain ⟨z,hz,hcz⟩ := ih hc' hb
      have henot : e ∉ F := by
        intro heF
        exact hsafe a c ha hc' e heF heval
      have hnew : (PD.FK.openGraph G (A \ F)).Adj a c :=
        (PD.FK.openGraph_adj G (A \ F) a c).mpr
          ⟨e, Finset.mem_sdiff.mpr ⟨he,henot⟩,heval⟩
      exact ⟨z,hz,hnew.reachable.trans hcz⟩

local instance rectangleCutSurvivalDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

private theorem rectangle_cut_edge_not_same_side (a : LatticeVertex) (w h : ℕ)
    (K : Configuration (rectangleGraph a w h)) (k : ℤ)
    (hK : ∀ e ∈ K, ∃ y : ℤ, Sym2.map Subtype.val e.val = s((k,y),(k+1,y)))
    (x y : RectangleVertex a w h)
    (hside : (x.val.1 ≤ k ∧ y.val.1 ≤ k) ∨ (k+1 ≤ x.val.1 ∧ k+1 ≤ y.val.1))
    (e : (rectangleGraph a w h).edgeSet) (he : e ∈ K) : e.val ≠ s(x,y) := by
  intro hrepr
  obtain ⟨j,hj⟩ := hK e he
  rw [hrepr,Sym2.map_mk] at hj
  rcases Sym2.eq_iff.mp hj with hp | hp
  all_goals
    have h₁ := congrArg Prod.fst hp.1
    have h₂ := congrArg Prod.fst hp.2
    dsimp only at h₁ h₂
    rcases hside with hs | hs <;> omega

/-- Closing actual sampled bonds in one column preserves original open arms
from the endpoints to their respective neighboring cut columns, in one sample. -/
theorem rectangle_cut_surviving_endpoint_targets (a : LatticeVertex) (w h : ℕ)
    (A K : Configuration (rectangleGraph a w h)) (k : ℤ)
    (hK : ∀ e ∈ K, ∃ y : ℤ, Sym2.map Subtype.val e.val = s((k,y),(k+1,y)))
    (u v : RectangleVertex a w h) (hu : u.val.1 ≤ k) (hv : k < v.val.1)
    (hconn : ActualConnected (rectangleGraph a w h) A u v) :
    A \ K ∈ targetConnectionEvent u {z | z.val.1 = k} ∧
      A \ K ∈ targetConnectionEvent v {z | z.val.1 = k+1} := by
  obtain ⟨p⟩ := hconn
  have hstep (x y : RectangleVertex a w h) (hxy : (rectangleGraph a w h).Adj x y) :
      |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 := hxy
  constructor
  · obtain ⟨z,hz,huz⟩ := rectangle_walk_reaches_cut_after_closing _ A K (fun z => z.val.1) k
      (fun x y hxy => by have hh := hstep x y hxy; simp only [abs_eq_max_neg] at hh; omega)
      (fun x y hx hy e he => rectangle_cut_edge_not_same_side a w h K k hK x y (Or.inl ⟨hx,hy⟩) e he)
      p hu hv
    exact ⟨z,hz,huz⟩
  · obtain ⟨z,hz,hvz⟩ := rectangle_walk_reaches_cut_after_closing _ A K (fun z => -z.val.1) (-k-1)
      (fun x y hxy => by have hh := hstep x y hxy; simp only [abs_eq_max_neg] at hh; omega)
      (fun x y hx hy e he => rectangle_cut_edge_not_same_side a w h K k hK x y
        (Or.inr ⟨by omega,by omega⟩) e he)
      p.reverse (by omega) (by omega)
    exact ⟨z,by change z.val.1 = k+1; omega,hvz⟩

end
end PottsContinuity.Thm3.Prop4
