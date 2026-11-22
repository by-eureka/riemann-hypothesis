import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibFour

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter
open scoped Pointwise

def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  obtain ⟨i1, c1, e1⟩ := h₁
  obtain ⟨i2, c2, e2⟩ := h₂
  refine ⟨i1.sub i2, c1.sub c2, fun S hS => ?_⟩
  rw [integral_sub i1.integrableOn i2.integrableOn,
    integral_sub (c1.continuousOn.integrableOn_compact hS) (c2.continuousOn.integrableOn_compact hS),
    e1 S hS, e2 S hS]

theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) := by
  obtain ⟨hi, hc, he⟩ := h
  refine ⟨hi.const_mul c, continuous_const.mul hc, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, he S hS]

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  push_neg at hneg
  have hU : {b | D b < D b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hD continuous_const).mem_nhds (by show D b0 < D b0 / 2; linarith)
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hKc.measure_lt_top
  have h1 : ∫ b in K, D b ∂ν ≤ ∫ b in K, D b0 / 2 ∂ν :=
    setIntegral_mono_on (hD.continuousOn.integrableOn_compact hKc)
      (continuousOn_const.integrableOn_compact hKc) hKc.measurableSet
      (fun x hx => le_of_lt (hKU hx))
  rw [setIntegral_const, smul_eq_mul] at h1
  try simp only [Measure.real] at h1
  have h2 : 0 < (ν K).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have h3 := h0 K hKc
  nlinarith

theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have hS : ∀ S, IsCompact S → 0 ≤ ∫ x in S, g₂ x - g₁ x ∂ν := by
    intro S hS
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.mpr (hle v)
  have key : 0 ≤ g₂ b - g₁ b := nonneg_of_setIntegral (fun x => g₂ x - g₁ x) h.2.1 hS b
  linarith

end Dens

section Approx

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem isOpen_inf_iInf (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := (0 : V)) ?_
  have h1 : (Λ₀ : Set V) ∈ 𝓝 (0 : V) := h₀o.mem_nhds Λ₀.zero_mem
  have h2 : (⋂ i ∈ t, (L i : Set V)) ∈ 𝓝 (0 : V) :=
    (Filter.biInter_finset_mem t).2 fun i _ => (hLo i).mem_nhds (L i).zero_mem
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Set.mem_iInter, SetLike.mem_coe] at hx1 hx2
  simp only [SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
  exact ⟨hx1, fun i hi => hx2 i hi⟩

theorem exists_sub_osc (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hloc : ∀ x : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧
      ∀ w ∈ W, |φ (x + w) - φ x| < ε / 2 := by
    intro x
    have hcx : ContinuousAt (fun w => φ (x + w)) 0 :=
      (hc.comp (continuous_const.add continuous_id)).continuousAt
    have hN : {w | |φ (x + w) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
      have h1 := hcx.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [h1] with w hw
      simpa [Real.dist_eq] using hw
    obtain ⟨W, hWo, -, hWN⟩ := hNA _ hN
    exact ⟨W, hWo, fun w hw => hWN hw⟩
  choose W hWo hW using hloc
  have hUo : ∀ i, IsOpen ((fun y => -i + y) ⁻¹' (W i : Set V)) :=
    fun i => (hWo i).preimage (continuous_const.add continuous_id)
  have hcov : tsupport φ ⊆ ⋃ i, (fun y => -i + y) ⁻¹' (W i : Set V) := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    show -y + y ∈ W y
    simp
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun i => (fun y => -i + y) ⁻¹' (W i : Set V)) hUo hcov
  have hΛo := isOpen_inf_iInf Λ₀ h₀o t W hWo
  refine ⟨Λ₀ ⊓ ⨅ i ∈ t, W i, hΛo,
    h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hΛo)
      (SetLike.coe_subset_coe.mpr inf_le_left), inf_le_left, ?_⟩
  intro x z hz
  have hz' := hz
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hz'
  have hzW : ∀ i ∈ t, z ∈ W i := hz'.2
  have hzero : ∀ y, y ∉ tsupport φ → φ y = 0 := fun y hy => by
    by_contra hne
    exact hy (subset_tsupport φ (Function.mem_support.mpr hne))
  by_cases hx : x ∈ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hxi' : -i + x ∈ W i := hxi
    have h1 := hW i (-i + x) hxi'
    have h2 := hW i (-i + (x + z)) (by
      have e : -i + (x + z) = (-i + x) + z := by abel
      rw [e]
      exact (W i).add_mem hxi' (hzW i hi))
    simp only [add_neg_cancel_left] at h1 h2
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have hxz : x + z ∉ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V) := by
      intro hc'
      apply hx
      simp only [Set.mem_iUnion] at hc' ⊢
      obtain ⟨i, hi, hxi⟩ := hc'
      refine ⟨i, hi, ?_⟩
      have hxi' : -i + (x + z) ∈ W i := hxi
      show -i + x ∈ W i
      have e : -i + x = (-i + (x + z)) + -z := by abel
      rw [e]
      exact (W i).add_mem hxi' ((W i).neg_mem (hzW i hi))
    rw [hzero x (fun h => hx (ht h)), hzero (x + z) (fun h => hxz (ht h))]
    simpa using hε

end Approx

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_sub_mem (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ := by
  have h : ((((x : V ⧸ Λ).out : V) : V ⧸ Λ)) = (x : V ⧸ Λ) := Quotient.out_eq _
  exact QuotientAddGroup.eq.mp h

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_eq (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x := by
  have e : (y : V ⧸ Λ) = (x : V ⧸ Λ) := (QuotientAddGroup.eq.mpr h).symm
  show φ ((y : V ⧸ Λ).out) = φ ((x : V ⧸ Λ).out)
  rw [e]

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem cosApx_lc (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : V => -x + y := continuous_const.add continuous_id
  have hm : (fun y : V => -x + y) ⁻¹' (Λ : Set V) ∈ 𝓝 x :=
    (hΛ.preimage hc).mem_nhds (by show -x + x ∈ Λ; simp)
  filter_upwards [hm] with y hy
  exact cosApx_eq Λ φ hy

theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  exact PI.VolStabW.densApprox_lc μ f ι ν U hU hNA

end Main

end PI.VolStabSW
