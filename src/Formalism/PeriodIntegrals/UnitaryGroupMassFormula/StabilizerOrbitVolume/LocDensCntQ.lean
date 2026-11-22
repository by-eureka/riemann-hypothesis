import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensCntQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

noncomputable section

namespace PI.VolStabSW

open Polynomial

theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) :=
  PI.VolStabW.exists_quadAlg k h2 D hD

end PI.VolStabSW
