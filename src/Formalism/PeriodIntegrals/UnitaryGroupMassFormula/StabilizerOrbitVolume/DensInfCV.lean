import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfCV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfLoc

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

theorem changeVar_holds : ChangeVar := by
  exact PI.VolStabW.changeVar_holds

end PI.VolStabSW
