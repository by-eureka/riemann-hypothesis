import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

noncomputable section

namespace PI.VolStabSW.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  exact PI.VolStabS.TopoPolish.polish_of_lcsc Y

end PI.VolStabSW.TopoPolish
