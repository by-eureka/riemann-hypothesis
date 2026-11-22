import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnfoldAbs

noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

instance subMeasurableMul (H : Subgroup G) : MeasurableMul H where
  measurable_const_mul c := by
    exact (((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(c : G) * x, H.mul_mem c.2 x.2⟩ : H))
  measurable_mul_const c := by
    exact (((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G) * c, H.mul_mem x.2 c.2⟩ : H))

instance subMeasurableInv (H : Subgroup G) : MeasurableInv H where
  measurable_inv := by
    exact ((measurable_inv.comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G)⁻¹, H.inv_mem x.2⟩ : H))

theorem countable_subgroupOf {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by
  refine Function.Injective.countable
    (f := fun x : (Γ ⊓ H).subgroupOf H =>
      (⟨((x : H) : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩ : Γ)) ?_
  intro a b hab
  have e : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) hab
  exact Subtype.ext (Subtype.ext e)

variable [MulAction G Y]

def orbS (Γ : Subgroup G) (y0 : Y) : Set Y := {x | ∃ γ ∈ Γ, γ • y0 = x}

def repO (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : G :=
  Classical.choose (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))

theorem repO_mem (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by
  exact (Classical.choose_spec x.2).1

theorem repO_smul (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x • y0 = x := by
  exact (Classical.choose_spec x.2).2

def cntN (Γ : Subgroup G) (A : Set G) (g : G) : ℝ≥0∞ :=
  ∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g)

def cfun (Γ : Subgroup G) (A : Set G) (y0 : Y) (g : G) : ℝ≥0∞ :=
  ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹)

theorem meas_cfun (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.ennreal_tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul (repO Γ y0 x)).comp measurable_inv)

theorem sum_rep_eq {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by
  exact PI.VolStabW.sum_rep_eq y0 hH u

end Abs

end PI.VolStabS
