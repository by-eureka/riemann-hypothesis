import Mathlib

theorem UpperTheory.Reformulated.B.IntegralSumCosets.integral_eq_measure_mul_sum_cosets :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulRightInvariant] [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
          (∀ (a b : ι), R a * (R b)⁻¹ ∈ K → a = b) →
            (∀ κ ∈ K, ∀ (g : G), f (κ * g) = f g) →
              (∀ (g : G), f g ≠ (0 : ℂ) → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
                ∫ (g : G), f g ∂μ = (↑(μ.real (↑K : Set G)) : ℂ) * ∑ a ∈ S, f (R a) := by
  intro G _ _ _ _ _ μ _ _ K hKo hKc ι R S f hR hf hsupp
  classical
  have hmeas : ∀ a : ι, MeasurableSet ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)) := fun a =>
    (hKo.preimage (continuous_id.mul continuous_const)).measurableSet
  have hμ : ∀ a : ι, μ ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)) = μ (K : Set G) := fun a =>
    MeasureTheory.measure_preimage_mul_right μ _ _
  have hval : ∀ (a : ι) (g : G), g * (R a)⁻¹ ∈ K → f g = f (R a) := fun a g hg =>
    by simpa using hf _ hg (R a)
  have hdisj : ∀ (a b : ι) (g : G), g * (R a)⁻¹ ∈ K → g * (R b)⁻¹ ∈ K → a = b := by
    intro a b g ha hb
    exact (hR b a (by simpa [mul_assoc] using K.mul_mem (K.inv_mem hb) ha)).symm
  have hdec : f = fun g => ∑ a ∈ S,
      ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g := by
    funext g
    by_cases hex : ∃ a ∈ S, g * (R a)⁻¹ ∈ K
    · obtain ⟨a, haS, ha⟩ := hex
      rw [Finset.sum_eq_single_of_mem a haS]
      · rw [Set.indicator_of_mem (by exact ha), hval a g ha]
      · intro b _ hba
        apply Set.indicator_of_notMem
        exact fun h => hba (hdisj a b g ha h).symm
    · have h0 : f g = 0 := of_not_not (mt (hsupp g) hex)
      rw [h0]
      refine (Finset.sum_eq_zero fun a haS => ?_).symm
      apply Set.indicator_of_notMem
      exact fun h => hex ⟨a, haS, h⟩
  have hint : ∀ a ∈ S, MeasureTheory.Integrable
      (((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a))) μ := fun a _ =>
    (MeasureTheory.integrable_indicator_iff (hmeas a)).mpr
      (MeasureTheory.integrableOn_const (by rw [hμ a]; exact hKc.measure_lt_top.ne))
  calc ∫ g, f g ∂μ
      = ∫ g, ∑ a ∈ S,
          ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g ∂μ :=
        congrArg (fun F => ∫ g, F g ∂μ) hdec
    _ = ∑ a ∈ S, ∫ g,
          ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g ∂μ :=
        MeasureTheory.integral_finsetSum S hint
    _ = (↑(μ.real (↑K : Set G)) : ℂ) * ∑ a ∈ S, f (R a) := by
        simp [Finset.mul_sum, MeasureTheory.integral_indicator_const, hmeas, hμ,
          MeasureTheory.measureReal_def, Complex.real_smul]
