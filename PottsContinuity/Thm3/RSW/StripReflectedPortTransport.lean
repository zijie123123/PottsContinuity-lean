module

public import PottsContinuity.Thm3.RSW.RectangleDualSidePorts
public import PottsContinuity.Thm3.RSW.StripReflectedCentralDualRead
public import PottsContinuity.Thm3.RSW.StripShiftedVerticalClip

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- Collapse expanded side ports into their physical neighbour before
reflecting. Every value belongs to the literal source shifted rectangle. -/
def stripReflectedCentralClampedVertex (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (v : RectangleDualVertex (-(k:ℤ)*n,0) (2*k*n) (2*n)) :
    {z : stripVertices n // z ∈
      stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n)} := by
  let x := max (-(k:ℤ)*n) (min ((k:ℤ)*n-1) v.val.1)
  have hkn : 1 ≤ (k:ℤ)*(n:ℤ) := by
    exact_mod_cast (show 1 ≤ k*n by nlinarith)
  have hv : v.val ∈ PD.FK.latticeRectangle (-(k:ℤ)*n-1,-1) (2*k*n+1) (2*n+1) := v.property
  rw [mem_latticeRectangle] at hv
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hv
  refine ⟨⟨(x,2*(n:ℤ)-1-v.val.2),?_⟩,?_⟩
  · change -(n:ℤ) ≤ 2*(n:ℤ)-1-v.val.2 ∧ 2*(n:ℤ)-1-v.val.2 ≤ 3*(n:ℤ)
    constructor <;> omega
  · simp only [stripRectangleVertices,Finset.mem_preimage,latticeRectangle,
      Finset.mem_product,Finset.mem_Icc]
    change (-(k:ℤ)*n ≤ max (-(k:ℤ)*n) (min ((k:ℤ)*n-1) v.val.1) ∧
      max (-(k:ℤ)*n) (min ((k:ℤ)*n-1) v.val.1) ≤ (k:ℤ)*n-1) ∧
      (-1 ≤ 2*(n:ℤ)-1-v.val.2 ∧ 2*(n:ℤ)-1-v.val.2 ≤ 2*(n:ℤ))
    exact ⟨⟨le_max_left _ _,max_le (by nlinarith only [hkn]) (min_le_left _ _)⟩,by omega⟩

private theorem reachable_of_adj_eq_or_adj {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → W)
    (h : ∀ u v, G.Adj u v → f u = f v ∨ H.Adj (f u) (f v))
    {u v : V} (huv : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
    rcases h u v huv with he | he
    · rw [he]
      exact ih
    · exact he.reachable.trans ih

/-- Side-port collapse preserves the actual sampled connection in the
induced shifted rectangle; every noncollapsed edge is unchanged. -/
theorem stripReflectedCentralClampedVertex_adj_or_eq
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (ω : StripConfiguration n)
    (u v : RectangleDualVertex (-(k:ℤ)*n,0) (2*k*n) (2*n))
    (huv : (openGraph _ (stripReflectedCentralDualConfiguration n k hn ω)).Adj u v) :
    stripReflectedCentralClampedVertex n k hn hk u = stripReflectedCentralClampedVertex n k hn hk v ∨
    ((stripOpenGraph n ω).induce
      (stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n) : Set (stripVertices n))).Adj
      (stripReflectedCentralClampedVertex n k hn hk u) (stripReflectedCentralClampedVertex n k hn hk v) := by
  have hg := openGraph_le _ _ huv
  have hwidth : 1 ≤ 2*k*n := by
    have hh : 0 < k*n := Nat.mul_pos hk hn
    simpa only [Nat.mul_assoc] using (show 1 ≤ 2*(k*n) by omega)
  have hc := rectangleDual_horizontal_clamp_edge (-(k:ℤ)*n,0) (2*k*n) (2*n) hwidth u v hg
  have he : (-(k:ℤ)*n)+(2*k*n:ℕ)-1 = (k:ℤ)*n-1 := by push_cast; ring
  simp only [he] at hc
  rcases hc with heq | ⟨hu,hv⟩
  · left
    apply Subtype.ext
    apply Subtype.ext
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    change (max (-(k:ℤ)*n) (min ((k:ℤ)*n-1) u.val.1),2*(n:ℤ)-1-u.val.2) =
      (max (-(k:ℤ)*n) (min ((k:ℤ)*n-1) v.val.1),2*(n:ℤ)-1-v.val.2)
    exact Prod.ext hx (by dsimp at hy; omega)
  · right
    have hu' : (stripReflectedCentralClampedVertex n k hn hk u).val =
        stripReflectedCentralDualEmbedding n k hn u := by
      apply Subtype.ext
      have hx := congrArg Prod.fst hu
      exact Prod.ext hx rfl
    have hv' : (stripReflectedCentralClampedVertex n k hn hk v).val =
        stripReflectedCentralDualEmbedding n k hn v := by
      apply Subtype.ext
      have hx := congrArg Prod.fst hv
      exact Prod.ext hx rfl
    change (stripOpenGraph n ω).Adj (stripReflectedCentralClampedVertex n k hn hk u).val
      (stripReflectedCentralClampedVertex n k hn hk v).val
    rw [hu',hv']
    exact (stripReflectedCentralDualOpenHom n k hn ω).map_rel huv

/-- The actual reflected finite-dual port event produces the source confined
shifted primal crossing. Side-port excursions are removed, not assumed absent. -/
theorem strip_reflected_dual_port_crossing_subset_shifted
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    {ω | stripReflectedCentralDualConfiguration n k hn ω ∈
      rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} ⊆
      stripConfinedConnection n
        (stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n))
        {u | u.val.2 = -1} {v | v.val.2 = 2*n} := by
  rintro ω ⟨b,hb,t,ht,hbt⟩
  let S := stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n)
  let f := stripReflectedCentralClampedVertex n k hn hk
  have hc := reachable_of_adj_eq_or_adj _ ((stripOpenGraph n ω).induce (S : Set (stripVertices n))) f
    (stripReflectedCentralClampedVertex_adj_or_eq n k hn hk ω) hbt
  obtain ⟨p⟩ := hc
  let i : ((stripOpenGraph n ω).induce (S : Set (stripVertices n))) →g stripOpenGraph n ω :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  refine ⟨(f t).val,(f b).val,p.reverse.map i,?_,?_,?_⟩
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    change 2*(n:ℤ)-1-(rectangleDualTopPortVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) j).val.2 = -1
    simp [rectangleDualTopPortVertex]
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    change 2*(n:ℤ)-1-(rectangleDualBottomPortVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) j).val.2 = 2*(n:ℤ)
    simp [rectangleDualBottomPortVertex]
  · intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact w.property

/-- The port-event containment also includes zero width, where the actual
bottom-port set is empty. -/
theorem strip_reflected_dual_port_crossing_subset_shifted_all
    (n k : ℕ) (hn : 1 ≤ n) :
    {ω | stripReflectedCentralDualConfiguration n k hn ω ∈
      rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} ⊆
      stripConfinedConnection n
        (stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n))
        {u | u.val.2 = -1} {v | v.val.2 = 2*n} := by
  by_cases hk : 1 ≤ k
  · exact strip_reflected_dual_port_crossing_subset_shifted n k hn hk
  · have hk0 : k=0 := by omega
    subst k
    rintro ω ⟨b,hb,t,ht,hbt⟩
    simp [rectangleDualBottomPorts] at hb

end
end PottsContinuity.RSW
