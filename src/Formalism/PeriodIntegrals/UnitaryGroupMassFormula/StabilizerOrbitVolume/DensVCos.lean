import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVGen

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def DensCos (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν

theorem hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0) := by
  exact ⟨integrable_zero _ _ _, continuous_const, fun S _ => by simp⟩

theorem HasDens.add [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  obtain ⟨hi1, hc1, he1⟩ := h₁
  obtain ⟨hi2, hc2, he2⟩ := h₂
  refine ⟨hi1.add hi2, hc1.add hc2, fun S hS => ?_⟩
  have hg1 : IntegrableOn g₁ S ν := by
    first
      | exact hc1.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc1.continuousOn
  have hg2 : IntegrableOn g₂ S ν := by
    first
      | exact hc2.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc2.continuousOn
  rw [integral_add hi1.integrableOn hi2.integrableOn, integral_add hg1 hg2, he1 S hS, he2 S hS]

theorem hasDens_sum [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  intro T
  induction T using Finset.cons_induction with
  | empty =>
    intro _
    simpa using (hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0))
  | cons a s ha ih =>
    intro hT
    have h1 := hT a (Finset.mem_cons_self a s)
    have h2 := ih (fun i hi => hT i (Finset.mem_cons_of_mem hi))
    simpa [Finset.sum_cons] using h1.add h2

def DensCosB (B : AddSubgroup V → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν

omit [IsTopologicalAddGroup V] in

def IsCOBasis (B : AddSubgroup V → Prop) : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, B Λ ∧ IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem isCompact_cos (Λ : AddSubgroup V) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    IsCompact {z | z - y ∈ Λ} := by
  have he : {z | z - y ∈ Λ} = (fun w => w + y) '' (Λ : Set V) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, sub_add_cancel z y⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [he]
  exact hΛc.image (continuous_add_right y)

theorem integrable_cos [IsFiniteMeasureOnCompacts μ] (Λ : AddSubgroup V)
    (hΛo : IsOpen (Λ : Set V)) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    Integrable ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) μ := by
  have hK := isCompact_cos Λ hΛc y
  have hO : IsOpen {z : V | z - y ∈ Λ} := hΛo.preimage (continuous_sub_right y)
  have hI : IntegrableOn (fun _ : V => (1 : ℝ)) {z : V | z - y ∈ Λ} μ := by
    first
      | exact ContinuousOn.integrableOn_compact hK continuousOn_const
      | exact integrableOn_const hK.measure_lt_top.ne
      | exact integrableOn_const.2 (Or.inr hK.measure_lt_top)
  exact hI.integrable_indicator hO.measurableSet

theorem densLC_of_cosB [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (B : AddSubgroup V → Prop) (hB : IsCOBasis B) (h : DensCosB B μ f ι ν U) :
    DensOn (IsLCcOn U) μ f ι ν :=
  PI.VolStabW.densLC_of_cosB U B hB h

theorem densLC_of_cos [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (hNA : HasCOSub V) (h : DensCos μ f ι ν U) : DensOn (IsLCcOn U) μ f ι ν := by
  refine densLC_of_cosB U (fun _ => True) ?_ ?_
  · intro N hN
    first
      | (obtain ⟨Λ, h1, h2, h3⟩ := hNA N hN
         exact ⟨Λ, trivial, h1, h2, h3⟩)
      | (obtain ⟨Λ, h1, h2, h3⟩ := hNA hN
         exact ⟨Λ, trivial, h1, h2, h3⟩)
      | (obtain ⟨Λ, h2, h1, h3⟩ := hNA N hN
         exact ⟨Λ, trivial, h1, h2, h3⟩)
  · intro x hx
    obtain ⟨N, hN, h'⟩ := h x hx
    exact ⟨N, hN, fun y hy Λ _ => h' y hy Λ⟩

end Cos

end PI.VolStabSW
