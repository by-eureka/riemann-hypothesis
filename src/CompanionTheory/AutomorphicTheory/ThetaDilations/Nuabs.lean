import Development.WeilBound.CoreStatements.ThetaDilations.Nuabs

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

theorem lower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∀ φ : G → ℝ≥0∞, Continuous φ → (∀ c ∈ C, φ c ≠ 0) → ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ p ∈ P, ∀ c ∈ C, m ≤ ∫⁻ q, φ (q⁻¹ * (p * c)) ∂ν := by
  intro G _ _ _ _ _ _ _ _ P ν _ hν hU C hC φ hφ hφC
  have key : ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ c ∈ C, m ≤ ∫⁻ q, φ (q⁻¹ * c) ∂ν := by
    refine hC.induction_on (p := fun s => ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ c ∈ s, m ≤ ∫⁻ q, φ (q⁻¹ * c) ∂ν)
      ⟨1, one_ne_zero, ENNReal.one_ne_top, fun _ h => h.elim⟩
      (fun s t hst ⟨m, h1, h2, h3⟩ => ⟨m, h1, h2, fun c hc => h3 c (hst hc)⟩)
      (fun s t ⟨m, h1, h2, h3⟩ ⟨m', h1', _, h3'⟩ => ⟨min m m', (lt_min h1.bot_lt h1'.bot_lt).ne',
        ((min_le_left _ _).trans_lt h2.lt_top).ne, fun c hc => hc.elim (fun h => (min_le_left _ _).trans (h3 c h))
        fun h => (min_le_right _ _).trans (h3' c h)⟩) fun c₀ hc₀ => ?_
    obtain ⟨ε, h0, hε⟩ := exists_between (hφC c₀ hc₀).bot_lt
    have hO : {z : G × G | ε < φ (z.1⁻¹ * z.2)} ∈ 𝓝 ((1 : G), c₀) :=
      (isOpen_lt continuous_const (hφ.comp (continuous_fst.inv.mul continuous_snd))).mem_nhds (by simpa using hε)
    obtain ⟨U, hU1, W, hW, hsub⟩ := mem_nhds_prod_iff.1 hO
    refine ⟨W, mem_nhdsWithin_of_mem_nhds hW, min 1 (ε * ν (interior U)),
      (lt_min one_pos (ENNReal.mul_pos h0.ne' (hU _ (interior_mem_nhds.2 hU1)))).ne',
      ((min_le_left _ _).trans_lt ENNReal.one_lt_top).ne, fun c hc => (min_le_right _ _).trans ?_⟩
    rw [← lintegral_indicator_const isOpen_interior.measurableSet]
    refine lintegral_mono fun q => ?_
    by_cases hq : q ∈ interior U
    · rw [Set.indicator_of_mem hq]
      exact (hsub (Set.mk_mem_prod (interior_subset hq) hc)).le
    · rw [Set.indicator_of_notMem hq]
      exact zero_le
  obtain ⟨m, h1, h2, h3⟩ := key
  refine ⟨m, h1, h2, fun p hp c hc => (h3 c hc).trans (le_of_eq ?_)⟩
  conv_rhs => rw [← hν p hp]
  rw [lintegral_map (f := fun q => φ (q⁻¹ * (p * c))) (hφ.measurable.comp (measurable_inv.mul_const _)) (measurable_const_mul p)]
  simp [mul_assoc]

theorem cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  intro G _ _ _ _ _ _ _ _ μ _ P ν _ hν hU C hC
  obtain ⟨u, hu1, -, hus, hu⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  set φ : G → ℝ≥0∞ := fun x => ENNReal.ofReal (u x) with hφ
  have hφc : Continuous φ := ENNReal.continuous_ofReal.comp u.continuous
  obtain ⟨m, h1, h2, h3⟩ := lower G P ν hν hU C hC φ hφc fun c hc => by simp [hφ, hu1 hc]
  refine ⟨tsupport u, m⁻¹ * μ (tsupport u), hus.isCompact, ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 h1.bot_lt)
    hus.isCompact.measure_lt_top, fun Γ _ hΓ 𝓕 h𝓕 S hS hcov f g hf hg hfi hfs hfg => ?_⟩
  have hk : Measurable fun z : G × G => φ (z.2⁻¹ * z.1) := hφc.measurable.comp (measurable_snd.inv.mul measurable_fst)
  set β : G → ℝ≥0∞ := fun x => ∫⁻ p in S, φ (p⁻¹ * x) ∂ν with hβ
  have hβm : Measurable β := hk.lintegral_prod_right'
  have hφx : ∀ x, Measurable fun q : G => φ (q⁻¹ * x) := fun x => hφc.measurable.comp (measurable_inv.mul_const _)
  have k1 : ∀ x, m * f x ≤ ∑' γ : Γ, β (γ • x) * f (γ • x) := fun x => by
    by_cases h0 : f x = 0
    · simp [h0]
    obtain ⟨p, hp, c, hc, rfl⟩ := hfs x h0
    have e : ∀ γ : Γ, f (γ • (p * c)) = f (p * c) := fun γ => hfi γ γ.2 _
    simp only [e, ENNReal.tsum_mul_right]
    refine mul_le_mul_left ((h3 p hp c hc).trans ?_) _
    have e2 : ∀ γ : Γ, β (γ • (p * c)) = ∫⁻ q, S.indicator (fun q => φ (q⁻¹ * (γ * (p * c)))) (γ * q) ∂ν := fun γ => by
      rw [← lintegral_map ((hφx _).indicator hS) (measurable_const_mul (γ : G)), hν _ (hΓ γ.2), lintegral_indicator hS]
      rfl
    simp only [e2]
    rw [← lintegral_tsum (f := fun (γ : Γ) q => S.indicator (fun q => φ (q⁻¹ * (γ * (p * c)))) (γ * q)) fun γ : Γ => (((hφx _).indicator hS).comp (measurable_const_mul (γ : G))).aemeasurable]
    refine lintegral_mono_ae (hcov.mono fun q ⟨γ, hγ, hq⟩ => le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : Γ)))
    simp [Set.indicator_of_mem hq, mul_assoc]
  have k2 : m * ∫⁻ x in 𝓕, f x ∂μ ≤ ∫⁻ x, β x * f x ∂μ := by
    rw [h𝓕.lintegral_eq_tsum'', ← lintegral_const_mul _ hf, ← lintegral_tsum (f := fun (γ : Γ) x => β (γ • x) * f (γ • x)) fun γ : Γ =>
      ((hβm.mul hf).comp (measurable_const_smul γ)).aemeasurable]
    exact lintegral_mono k1
  have k3 : ∫⁻ x, β x * f x ∂μ ≤ μ (tsupport u) * ∫⁻ p in S, g p ∂ν := by
    have e : ∀ x, β x * f x = ∫⁻ p in S, φ (p⁻¹ * x) * f x ∂ν := fun x => (lintegral_mul_const (f x) (hφx x)).symm
    simp only [e]
    rw [lintegral_lintegral_swap (f := fun x p => φ (p⁻¹ * x) * f x) (hk.mul (hf.comp measurable_fst)).aemeasurable, ← lintegral_const_mul _ hg]
    refine setLIntegral_mono' hS fun p hp => ?_
    rw [← lintegral_mul_left_eq_self _ p, mul_comm, ← lintegral_indicator_const (isClosed_tsupport u).measurableSet]
    refine lintegral_mono fun y => ?_
    rw [inv_mul_cancel_left]
    by_cases hy : y ∈ tsupport u
    · rw [Set.indicator_of_mem hy]
      exact (mul_le_of_le_one_left' (ENNReal.ofReal_le_one.2 (hu y).2)).trans (hfg p hp y hy)
    · simp [hφ, image_eq_zero_of_notMem_tsupport hy]
  rw [mul_assoc, ← ENNReal.mul_le_iff_le_inv h1 h2]
  exact k2.trans k3

theorem unf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  exact PositivityTheory.PlacePermOperatorBicommutantSpan.unf

theorem nuabs : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  exact PositivityTheory.PlacePermOperatorBicommutantSpan.nuabs

end CompanionTheory.PlacePermOperatorBicommutantSpan
