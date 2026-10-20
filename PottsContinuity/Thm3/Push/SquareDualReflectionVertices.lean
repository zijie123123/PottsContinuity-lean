module

public import PottsContinuity.Thm3.Push.SquareArmReflection
public import PottsContinuity.Thm3.Push.ClosedClusterFrontier

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial
noncomputable section

/-- Original face-base labels reflect one unit left of primal vertex labels. -/
def squareDualReflectionVertex (N : ℕ) (v : RectangleDualVertex (0,0) N N) :
    RectangleDualVertex (0,0) N N :=
  ⟨((N:ℤ)-v.val.1-1,v.val.2),by
    have hv := (PD.FK.mem_latticeRectangle (-1,-1) v.val (N+1) (N+1)).mp v.property
    change ((N:ℤ)-v.val.1-1,v.val.2) ∈ PD.FK.latticeRectangle (-1,-1) (N+1) (N+1)
    rw [PD.FK.mem_latticeRectangle]
    dsimp at hv ⊢
    omega⟩

@[simp] theorem squareDualReflectionVertex_involutive (N : ℕ)
    (v : RectangleDualVertex (0,0) N N) :
    squareDualReflectionVertex N (squareDualReflectionVertex N v) = v := by
  apply Subtype.ext
  apply Prod.ext
  · change (N:ℤ)-((N:ℤ)-v.val.1-1)-1=v.val.1
    omega
  · rfl

/-- Reflect a normalized original bond, retaining its positive orientation. -/
def squareReflectedBond (N : ℕ) (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨((N:ℤ)-b.base.1-1,b.base.2),.horizontal⟩
  | .vertical => ⟨((N:ℤ)-b.base.1,b.base.2),.vertical⟩

/-- The reflected original endpoint pair is the actual normalized reflected bond. -/
theorem squareReflectedBond_pair (N : ℕ) (b : LatticeBond) :
    Sym2.map (fun z : LatticeVertex => ((N:ℤ)-z.1,z.2)) b.toSym2 =
      (squareReflectedBond N b).toSym2 := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis with
  | horizontal =>
    apply Sym2.eq_iff.mpr
    right
    constructor <;> apply Prod.ext <;>
      dsimp [squareReflectedBond,LatticeBond.source,LatticeBond.target] <;> omega
  | vertical => rfl

/-- Normalization of the primal edge relabeling agrees with the literal
reflected bond, in both orientations and at the rectangle boundary. -/
theorem rectanglePrimalEdgeBond_square_reflection (N : ℕ)
    (f : (rectangleGraph (0,0) N N).edgeSet) :
    rectanglePrimalEdgeBond (0,0) N N (configurationIsoEdgeEquiv (squareArmReflectionIso N) f) =
      squareReflectedBond N (rectanglePrimalEdgeBond (0,0) N N f) := by
  apply LatticeBond.toSym2_injective
  have hf := rectanglePrimalEdgeBond_toSym2_public (0,0) N N f
  have hm := rectanglePrimalEdgeBond_toSym2_public (0,0) N N
    (configurationIsoEdgeEquiv (squareArmReflectionIso N) f)
  calc
    _ = Sym2.map (fun t : RectangleVertex (0,0) N N => t.val)
        (Sym2.map (squareArmReflectionIso N) f.val) := hm
    _ = Sym2.map (fun z : LatticeVertex => ((N:ℤ)-z.1,z.2))
        (Sym2.map (fun t : RectangleVertex (0,0) N N => t.val) f.val) := by
      rw [Sym2.map_map,Sym2.map_map]
      rfl
    _ = Sym2.map (fun z : LatticeVertex => ((N:ℤ)-z.1,z.2))
        (rectanglePrimalEdgeBond (0,0) N N f).toSym2 := congrArg _ hf.symm
    _ = _ := squareReflectedBond_pair N _

/-- The crossing pair reflects on face bases with the exact minus-one shift. -/
theorem squareReflectedBond_face_pair (N : ℕ) (b : LatticeBond) :
    s(((N:ℤ)-(b.faceBase false).1-1,(b.faceBase false).2),
      ((N:ℤ)-(b.faceBase true).1-1,(b.faceBase true).2)) =
    s((squareReflectedBond N b).faceBase false,(squareReflectedBond N b).faceBase true) := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis with
  | horizontal => rfl
  | vertical =>
    apply Sym2.eq_iff.mpr
    right
    constructor
    · apply Prod.ext
      · change (N:ℤ)-(x-1)-1 = (N:ℤ)-x
        omega
      · rfl
    · rfl

/-- The actual rectangle primal/dual edge bijection commutes with reflection.
This identity retains both the original sampled edge and its true dual faces. -/
theorem squareDualReflection_crossing_pair (N : ℕ)
    (f : (rectangleGraph (0,0) N N).edgeSet) :
    Sym2.map (squareDualReflectionVertex N) (DualityExt.rectangleDualEdgeEquiv (0,0) N N f).val =
      (DualityExt.rectangleDualEdgeEquiv (0,0) N N
        (configurationIsoEdgeEquiv (squareArmReflectionIso N) f)).val := by
  let d := rectanglePrimalDualEdgeEquiv (0,0) N N f
  let g := configurationIsoEdgeEquiv (squareArmReflectionIso N) f
  let d' := rectanglePrimalDualEdgeEquiv (0,0) N N g
  apply Sym2.map.injective Subtype.val_injective
  change s(((N:ℤ)-(rectangleDualEdgeSource (0,0) N N d).val.1-1,
      (rectangleDualEdgeSource (0,0) N N d).val.2),
      ((N:ℤ)-(rectangleDualEdgeTarget (0,0) N N d).val.1-1,
      (rectangleDualEdgeTarget (0,0) N N d).val.2)) =
    s((rectangleDualEdgeSource (0,0) N N d').val,(rectangleDualEdgeTarget (0,0) N N d').val)
  rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase,
    rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase]
  change s(((N:ℤ)-((rectanglePrimalEdgeBond (0,0) N N f).faceBase false).1-1,
      ((rectanglePrimalEdgeBond (0,0) N N f).faceBase false).2),
      ((N:ℤ)-((rectanglePrimalEdgeBond (0,0) N N f).faceBase true).1-1,
      ((rectanglePrimalEdgeBond (0,0) N N f).faceBase true).2)) =
    s((rectanglePrimalEdgeBond (0,0) N N g).faceBase false,
      (rectanglePrimalEdgeBond (0,0) N N g).faceBase true)
  have hg := rectanglePrimalEdgeBond_square_reflection N f
  change rectanglePrimalEdgeBond (0,0) N N g = squareReflectedBond N _ at hg
  rw [hg]
  exact squareReflectedBond_face_pair N _

private theorem squareDualReflection_adj (N : ℕ)
    {u v : RectangleDualVertex (0,0) N N}
    (huv : (rectangleDualGraph (0,0) N N).Adj u v) :
    (rectangleDualGraph (0,0) N N).Adj (squareDualReflectionVertex N u) (squareDualReflectionVertex N v) := by
  let e := DualityExt.rectangleDualEdgeEquiv (0,0) N N
  let f := e.symm ⟨s(u,v),(rectangleDualGraph (0,0) N N).mem_edgeSet.mpr huv⟩
  have hf : (e f).val = s(u,v) := congrArg Subtype.val (e.apply_symm_apply _)
  have hp := squareDualReflection_crossing_pair N f
  change Sym2.map (squareDualReflectionVertex N) (e f).val = _ at hp
  rw [hf] at hp
  have hm := (e (configurationIsoEdgeEquiv (squareArmReflectionIso N) f)).property
  rw [← hp] at hm
  exact (rectangleDualGraph (0,0) N N).mem_edgeSet.mp hm

/-- The literal face-base reflection is an isomorphism of the actual finite
rectangle dual graph, with the same original crossing-bond labels. -/
def squareDualReflectionIso (N : ℕ) :
    rectangleDualGraph (0,0) N N ≃g rectangleDualGraph (0,0) N N where
  toFun := squareDualReflectionVertex N
  invFun := squareDualReflectionVertex N
  left_inv := squareDualReflectionVertex_involutive N
  right_inv := squareDualReflectionVertex_involutive N
  map_rel_iff' := by
    intro u v
    constructor
    · intro h
      have hh := squareDualReflection_adj N h
      change (rectangleDualGraph (0,0) N N).Adj
        (squareDualReflectionVertex N (squareDualReflectionVertex N u))
        (squareDualReflectionVertex N (squareDualReflectionVertex N v)) at hh
      simpa only [squareDualReflectionVertex_involutive] using hh
    · exact squareDualReflection_adj N

/-- The actual dual-edge relabeling and the actual original-edge relabeling
commute with the primal/dual bijection. -/
theorem squareDualReflection_edge_commutes (N : ℕ)
    (f : (rectangleGraph (0,0) N N).edgeSet) :
    configurationIsoEdgeEquiv (squareDualReflectionIso N)
      (DualityExt.rectangleDualEdgeEquiv (0,0) N N f) =
    DualityExt.rectangleDualEdgeEquiv (0,0) N N
      (configurationIsoEdgeEquiv (squareArmReflectionIso N) f) := by
  apply Subtype.ext
  exact squareDualReflection_crossing_pair N f

end
end PottsContinuity.Push
