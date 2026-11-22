import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExStabTop

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal NNReal Pointwise

section AbstractU

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by
  have hc : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
    continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
  exact (hf.comp hc.measurable).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using this

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) ∘ Quotient.mk'') =
      fun g => ∫⁻ h, f (g * (h : G)) ∂ν := by
    funext g
    exact avg_out H ν f g
  rw [this]
  exact meas_avg H ν hf

theorem meas_smul_q (H : Subgroup G) (g : G) : Measurable (fun q : G ⧸ H => g • q) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => g • q) ∘ Quotient.mk'') = (QuotientGroup.mk : G → G ⧸ H) ∘ (g * ·) := by
    funext k
    rfl
  rw [this]
  exact measurable_quotient_mk''.comp (measurable_const_mul g)

theorem induced_eq (H : Subgroup G) (hcl : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] (ρ' : Measure (G ⧸ H))
    (hinv : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s)
    (hfin : ∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) (hne : ρ' ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ q, ∫⁻ h, f (q.out * (h : G)) ∂ν ∂ρ' :=
  PI.VolStabW.induced_eq H hcl μ ν ρ' hinv hfin hne

end AbstractU

section OrbitU

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem weil_orbit_u (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (νX : Measure X) (hnull : νX {y | ¬ ∃ g : G, g • x0 = y} = 0)
    (hinv : ∀ (g : G) (s : Set X), MeasurableSet s → νX ((fun y => g • y) ⁻¹' s) = νX s)
    (hfin : ∀ K : Set X, IsCompact K → νX K < ⊤) (hne : νX ≠ 0)
    (hemb : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0))
    (hcont : Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0)) :
    ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧
      ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) →
        ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂νX :=
  PI.VolStabW.weil_orbit_u x0 hcl μ νX hnull hinv hfin hne hemb hcont

end OrbitU

theorem exStab_of_U (hW : SecCtblW) (hP : LCSCPolish) (hO : OrbTup) (hI : NuInv) (hF : NuFin)
    (hN : NuNeZero) : ExStab := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secCtblG_of hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : μ.IsHaarMeasure := hμ
  have hnull : νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0 := by
    apply measure_mono_null _ hν.1
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    intro hg
    exact hy (hO F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet y hg)
  obtain ⟨hemb, hcont⟩ := orbEmb_of hW hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨μ', h1, h2⟩ := weil_orbit_u (G := HA (AF F) σ J) (ratTup (AF F) X0)
    (stabClosed_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet) μ νX hnull
    (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hN F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν) hemb hcont
  exact ⟨μ', h1, hnull, fun f hf s hs => h2 f hf s hs⟩

end PI.VolStabSW
