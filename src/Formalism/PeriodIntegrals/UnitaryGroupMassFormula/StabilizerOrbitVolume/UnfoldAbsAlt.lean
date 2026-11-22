import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnfoldAbsAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LintFibre

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs3

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]

theorem unfold_abs {Γ H : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] [μ'.IsInvInvariant]
    (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (ν : Measure Y) (Φ : Y → ℝ≥0∞) (hΦ : AEMeasurable Φ ν)
    (hΨ : Measurable fun g : G => Φ (g • y0))
    (hcov : ν {y | ¬ ∃ g : G, g • y0 = y} = 0)
    (hcomp : ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : Y → G,
      (∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ k, f (s y * (k : G)) ∂μ' ∂ν)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ') :
    ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
  exact PI.VolStabW.unfold_abs μ μ' y0 hH ν Φ hΦ hΨ hcov hcomp 𝓕 h𝓕 𝓕' h𝓕'

end Abs3

end PI.VolStabSW
