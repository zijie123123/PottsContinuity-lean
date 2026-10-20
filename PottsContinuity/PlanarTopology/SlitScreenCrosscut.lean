module

public import PottsContinuity.PlanarTopology.SlitArchIndexInvariance

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.FiniteFK FKC.Medial Thm4Plane
noncomputable section

/-- The actual source-screen arch separates the bottom cap center from the
wired slit after deletion of precisely its crossed original bonds. The result
holds for arbitrary walks, including walks with repeated vertices. -/
theorem slitScreen_crossedDualWalk_separatesCapFromWiredArc
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16*m))) (lb rb : LatticeVertex)
    (hlb : lb ∈ generalScreenBottomTerminals (16*m) (generalScreenLeftFaceBases (16*m)))
    (hrb : rb ∈ generalScreenBottomTerminals (16*m) (generalScreenRightFaceBases (16*m)))
    (p : (generalScreenActualClosedDualGraph (16*m) A
      (generalScreenArchFaceBases (16*m))).Walk lb rb) :
    ∀ v ∈ slitBoxWiredArc (16*m),
      v ∉ screenTargetCapEdgeDeletedComponent m (screenArchCrossedBondConfiguration m A p) := by
  intro v hv hconn
  obtain ⟨q⟩ := hconn
  have hlY : lb.2 = -(16*(m : ℤ))-1 := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hlb.2
  have hrY : rb.2 = -(16*(m : ℤ))-1 := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hrb.2
  have hlC := (generalScreenLeftFaceBases_mem_iff (16*m) lb.1 lb.2).mp hlb.1
  have hrC := (generalScreenRightFaceBases_mem_iff (16*m) rb.1 rb.2).mp hrb.1
  push_cast at hlC hrC
  have hlX : lb.1 < 0 := by omega
  have hrX : 0 ≤ rb.1 := by omega
  have hvC := (mem_slitBoxWiredArc_iff (16*m) v).mp hv
  have hstart : lb ∈ generalScreenArchFaceBases (16*m) :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hlb.1)))
  have hsupport := slitScreen_actual_walk_support (16*m) A
    (generalScreenArchFaceBases (16*m)) p hstart
  let P := p.map (slitScreenDualToIndexLattice (16*m) A (generalScreenArchFaceBases (16*m)))
  have hPsupport : P.support = p.support := slitScreenDualToIndexLattice_walk_support _ _ _ p
  have hlow : PD.Duality.rayIndex (0,-(16*(m : ℤ))) P = -1 := by
    have hformula := rayIndex_telescope_of_low_column_absent (0,-(16*(m : ℤ))) P
      (fun z hz hy hx => by
        have hz' := hsupport z (hPsupport ▸ hz)
        have hb := slitScreen_arch_column_bounds m hm z hz' hx
        omega)
    have hl : lb.2 < -(16*(m : ℤ)) := by omega
    have hr : rb.2 < -(16*(m : ℤ)) := by omega
    change PD.Duality.rayIndex (0,-(16*(m : ℤ))) P =
      (if lb.2 < -(16*(m : ℤ)) then 1 else 0)*(if 0 ≤ lb.1 then 1 else 0) -
      (if rb.2 < -(16*(m : ℤ)) then 1 else 0)*(if 0 ≤ rb.1 then 1 else 0) at hformula
    simpa only [ite_eq_left hl,ite_eq_left hr,ite_eq_right (by omega : ¬ 0 ≤ lb.1),ite_eq_left hrX,
      mul_zero,mul_one,zero_sub] using hformula
  have hhigh : PD.Duality.rayIndex v.val P = 0 := by
    have hformula := rayIndex_telescope_of_high_column_absent (0,v.val.2) P
      (fun z hz hy hx => by
        have hz' := hsupport z (hPsupport ▸ hz)
        have hb := slitScreen_arch_column_bounds m hm z hz' hx
        omega)
    have hl : lb.2 < v.val.2 := by omega
    have hr : rb.2 < v.val.2 := by omega
    change PD.Duality.rayIndex (0,v.val.2) P =
      ((if lb.2 < v.val.2 then 1 else 0)-1)*(if 0 ≤ lb.1 then 1 else 0) -
      ((if rb.2 < v.val.2 then 1 else 0)-1)*(if 0 ≤ rb.1 then 1 else 0) at hformula
    have hvpair : v.val = (0,v.val.2) := Prod.ext hvC.1 rfl
    rw [hvpair]
    simpa only [ite_eq_left hl,ite_eq_left hr,sub_self,zero_mul] using hformula
  have hindex := slit_arch_index_eq_of_residual_walk m A p q (fun z hz => by
    have hb := (mem_latticeRectangle _ z.val _ _).mp z.property
    push_cast at hb
    constructor <;> omega)
  change PD.Duality.rayIndex (0,-((16*m : ℕ) : ℤ)) P = PD.Duality.rayIndex v.val P at hindex
  push_cast at hindex
  rw [hlow,hhigh] at hindex
  omega

end
end PottsContinuity.PlanarTopology
