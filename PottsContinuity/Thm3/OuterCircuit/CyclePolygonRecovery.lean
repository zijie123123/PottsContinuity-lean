module

public import PottsContinuity.Thm3.OuterCircuit.EnvelopeShell

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.FKC

noncomputable section

private theorem interiorCellBases_cast_eq {m k : ℕ}
    (e : m = k) (P : FKC.LatticePolygon m) :
    (e ▸ P).interiorCellBases ⟨1, zero_lt_one⟩ =
      P.interiorCellBases ⟨1, zero_lt_one⟩ := by
  cases e
  rfl

theorem sourcePolygonWalk_envelopePolygon_cast_eq {m : ℕ}
    (P : FKC.LatticePolygon m)
    (hlen : ((sourcePolygonWalk P).map RSW.polygonRayLatticeHom).length - 3 = m) :
    hlen ▸ outerCircuitEnvelopePolygon (sourcePolygonWalk P)
      (sourcePolygonWalk_isCycle P) = P := by
  change sourcePolygonWalkPolygon P = P
  exact sourcePolygonWalk_recovered_polygon_eq P

theorem outerCircuitCodePolygon_envelopePolygon_region_eq {n : ℕ}
    (i : OuterCircuitPolygonCode n) :
    (outerCircuitEnvelopePolygon (sourcePolygonWalk (outerCircuitCodePolygon i))
      (sourcePolygonWalk_isCycle (outerCircuitCodePolygon i))).interiorCellBases
        ⟨1, zero_lt_one⟩ =
      (outerCircuitCodePolygon i).interiorCellBases ⟨1, zero_lt_one⟩ := by
  let P := outerCircuitCodePolygon i
  have hlen : ((sourcePolygonWalk P).map RSW.polygonRayLatticeHom).length - 3 = i.1.val := by
    rw [sourcePolygonWalk_onFKC_length]
    omega
  have hpoly := sourcePolygonWalk_envelopePolygon_cast_eq P hlen
  have hregion := congrArg (fun Q : FKC.LatticePolygon i.1.val =>
    Q.interiorCellBases ⟨1, zero_lt_one⟩) hpoly
  have hcast := interiorCellBases_cast_eq hlen
    (outerCircuitEnvelopePolygon (sourcePolygonWalk P)
      (sourcePolygonWalk_isCycle P))
  calc
    (outerCircuitEnvelopePolygon (sourcePolygonWalk P)
      (sourcePolygonWalk_isCycle P)).interiorCellBases ⟨1, zero_lt_one⟩ =
        (hlen ▸ outerCircuitEnvelopePolygon (sourcePolygonWalk P)
          (sourcePolygonWalk_isCycle P)).interiorCellBases ⟨1, zero_lt_one⟩ := hcast.symm
    _ = P.interiorCellBases ⟨1, zero_lt_one⟩ := hregion

end
end PottsContinuity.OuterCircuit
