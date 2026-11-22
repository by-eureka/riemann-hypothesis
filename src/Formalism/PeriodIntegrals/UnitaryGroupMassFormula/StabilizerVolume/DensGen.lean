import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensGen
import Formalism.PeriodIntegrals.VolFromSW

noncomputable section

namespace PI.VolStabS.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b := by
  have h0 := hfib.1 b
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) h0
  intro hmem
  exact hv (hι (by rw [← hff']; exact hmem.1))

theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  exact PI.VolStabW.DensGen.fib_set_nonneg hfib hf' hff' hι ρ hρc hρs hρU hρ0 S hS hSB

theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  exact PI.VolStabW.DensGen.fib_set hfib hf' hff' hι ρ hρc hρs hρU S hS hSB

theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have key : ∀ E : X → ℝ, ContinuousOn E W →
      (∀ S, IsCompact S → S ⊆ W → ∫ b in S, E b ∂ν = 0) → ¬ 0 < E b0 := by
    intro E hE h0E hpos
    have hca : ContinuousAt E b0 := hE.continuousAt hW
    have hnhd : E ⁻¹' Set.Ioi (E b0 / 2) ∈ 𝓝 b0 := hca.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
    obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hnhd hW)
    have hKW : K ⊆ W := fun x hx => (hKsub hx).2
    have hpos' : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
    have hfin : ν K < ⊤ := hKc.measure_lt_top
    have hint : IntegrableOn E K ν := (hE.mono hKW).integrableOn_compact hKc
    have hconst : IntegrableOn (fun _ => E b0 / 2) K ν := by
      first
        | exact integrableOn_const hfin.ne
        | exact integrableOn_const.2 (Or.inr hfin)
        | exact (integrableOn_const (C := E b0 / 2)).2 (Or.inr hfin)
    have hmono : ∫ b in K, E b0 / 2 ∂ν ≤ ∫ b in K, E b ∂ν :=
      setIntegral_mono_on hconst hint hKc.measurableSet (fun x hx => (hKsub hx).1.le)
    rw [h0E K hKc hKW, setIntegral_const] at hmono
    have hr : 0 < (ν K).toReal := ENNReal.toReal_pos hpos'.ne' hfin.ne
    first
      | (rw [smul_eq_mul] at hmono; nlinarith)
      | (simp only [Measure.real, smul_eq_mul] at hmono; nlinarith)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine key (fun b => -D b) hD.neg (fun S hS hSW => ?_) (by simpa using hneg)
    rw [integral_neg, h0 S hS hSW, neg_zero]
  · exact key D hD h0 hpos

theorem eq_zero_of_setIntegral_c [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℂ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have hre := eq_zero_of_setIntegral (ν := ν) (fun b => (D b).re) W b0 hW
    (Complex.continuous_re.comp_continuousOn hD) (fun S hS hSW => by
      have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
      have h1 := integral_re hint
      simp only [RCLike.re_to_complex] at h1
      rw [h1, h0 S hS hSW, Complex.zero_re])
  have him := eq_zero_of_setIntegral (ν := ν) (fun b => (D b).im) W b0 hW
    (Complex.continuous_im.comp_continuousOn hD) (fun S hS hSW => by
      have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
      have h1 := integral_im hint
      simp only [RCLike.im_to_complex] at h1
      rw [h1, h0 S hS hSW, Complex.zero_im])
  exact Complex.ext hre him

theorem cut_props {f' : V → X} (hf' : Continuous f') (q : V → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (ψ : X → ℝ) (hψ : Continuous ψ) (C : Set X) (hC : IsClosed C)
    (hψC : ∀ x, ψ x ≠ 0 → x ∈ C) (hCU : ∀ v, f' v ∈ C → v ∈ U) :
    Continuous (fun v => q v * ψ (f' v)) ∧ HasCompactSupport (fun v => q v * ψ (f' v)) ∧
      tsupport (fun v => q v * ψ (f' v)) ⊆ U := by
  refine ⟨hq.mul (hψ.comp hf'), hqs.mul_right, ?_⟩
  have hcl : IsClosed (f' ⁻¹' C) := hC.preimage hf'
  have hsub : Function.support (fun v => q v * ψ (f' v)) ⊆ f' ⁻¹' C := by
    intro v hv
    exact hψC _ (right_ne_zero_of_mul hv)
  exact (closure_minimal hsub hcl).trans (fun v hv => hCU v hv)

theorem densGen [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {B' N : Set X} (hfib : IsFibreFamily μ f ι U ν B fib)
    {f' : V → X} (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (hNU : ∀ v, f' v ∈ N → v ∈ U)
    {Φ : V → ℂ} (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) {g : X → ℂ}
    (hg : IsContDensityOn μ f ι ν B' Φ g) {b0 : X} (hB : B ∈ 𝓝 b0) (hB' : B' ∈ 𝓝 b0)
    (hN : N ∈ 𝓝 b0) :
    g b0 = ∫ v, Φ v ∂(fib b0) := by
  exact PI.VolStabW.DensGen.densGen hfib hf' hff' hι hNU hΦc hΦs hg hB hB' hN

end PI.VolStabS.DensGen
