import Development.WeilBound.CoreStatements.ThetaDilations.SqPosOfNe
import CompanionTheory.AutomorphicTheory.ThetaDilations.IsOpenCoset

open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]

theorem bsym {B : Matrix ι ι R} (hB : B.IsSymm) (x y : ι → R) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq, dotProduct_comm]

variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}

theorem impl_one : Impl ψ h B μ 1 id :=
  ⟨fun _ hφ => hφ, fun φ hφ => ⟨φ, hφ, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun x y φ _ => by simp⟩

variable (H : NAQuad ψ h B μ)
include H

theorem sb_heis (x y : ι → R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (Heisenberg₂ ψ h B x y φ) := by
  have hD := H.2.2.2.2.2
  have := hD.1
  have e : Heisenberg₂ ψ h B x y φ =
      ψ (h * (x ⬝ᵥ (B *ᵥ y))) • fun u => (φ ∘ Homeomorph.addRight x) u * chiB ψ B u y := by
    funext u
    simp only [Heisenberg₂, chiB, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul, Function.comp, Homeomorph.coe_addRight]
    ring
  exact e ▸ sb_smul _ (sb_chi hD (sb_homeo hφ _) y)

theorem sb_opU (b : R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opU ψ h B b φ) := by
  have hD := H.2.2.2.2.2
  have := hD.1
  have := H.1
  refine sb_mul ((IsLocallyConstant.iff_exists_open _).2 fun u => ?_) hφ
  obtain ⟨L₀, hL₀, -⟩ := co_cpt hD isCompact_empty
  obtain ⟨L, hL, hKL⟩ := co_cpt hD ((hL₀.1.image (continuous_const_smul (b * h))).insert (b • u))
  refine ⟨{y | y - u ∈ L₀ ⊓ perpG hD L}, isOpen_coset u (hL₀.inf (co_perp hD hL).2).2, by simp, fun y hy => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, y = u + l := ⟨y - u, by abel⟩
  simp only [mem_setOf_eq, add_sub_cancel_left] at hy
  have h1 : chiB ψ B (b • u) l = 1 := hy.2 _ (hKL (mem_insert _ _))
  have h2 : chiB ψ B ((b * h) • l) l = 1 := hy.2 _ (hKL (mem_insert_of_mem _ ⟨l, hy.1, rfl⟩))
  have e : b * qf h B (u + l) = b * qf h B u + (b • u) ⬝ᵥ (B *ᵥ l) + ((b * h) • l) ⬝ᵥ (B *ᵥ l) := by
    simp only [qf, mulVec_add, add_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul, bsym H.2.2.2.2.1 l u]
    linear_combination (b * (u ⬝ᵥ (B *ᵥ l))) * H.2.1
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  exact (congrArg₂ _ (congrArg _ h1) h2).trans (by simp)

theorem sb_opD (m : ℝ) (a : Rˣ) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opD m (a : R) φ) := by
  have := H.1
  exact sb_smul (m : ℂ) (sb_homeo hφ (Homeomorph.smul a))

omit H in
theorem impl_mul {g g' : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g' T') : Impl ψ h B μ (g * g') (T ∘ T') := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hT
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hT'
  refine ⟨fun φ hφ => a1 _ (b1 φ hφ), fun φ hφ => ?_, fun φ φ' hφ hφ' => ?_, fun c φ hφ => ?_, fun φ hφ => ?_,
    fun x y φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, rfl⟩ := a2 φ hφ
    obtain ⟨φ₂, h2, rfl⟩ := b2 φ₁ h1
    exact ⟨φ₂, h2, rfl⟩
  · simp only [Function.comp, b3 φ φ' hφ hφ', a3 _ _ (b1 φ hφ) (b1 φ' hφ')]
  · simp only [Function.comp, b4 c φ hφ, a4 c _ (b1 φ hφ)]
  · exact (a5 _ (b1 φ hφ)).trans (b5 φ hφ)
  · simp only [Function.comp, a6 x y _ (b1 φ hφ), b6 _ _ φ hφ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    congr 3 <;> module

theorem impl_U (b : R) : Impl ψ h B μ (nMat b) (opU ψ h B b) := by
  refine ⟨fun φ hφ => sb_opU H b hφ, fun φ hφ => ⟨_, sb_opU H (-b) hφ, ?_⟩, fun φ φ' _ _ => ?_, fun c φ _ => ?_,
    fun φ _ => ?_, fun x y φ _ => ?_⟩
  · funext u; simp only [opU, ← mul_assoc, ← AddChar.map_add_eq_mul]; simp
  · funext u; simp only [opU, Pi.add_apply, mul_add]
  · funext u; simp only [opU, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [opU, norm_mul, H.2.2.2.1, one_mul]
  · funext u
    simp only [Heisenberg₂, opU, ← mul_assoc, ← AddChar.map_add_eq_mul, nMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, zero_smul, add_zero]
    congr 2
    simp only [qf, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul,
      bsym H.2.2.2.2.1 x u]
    linear_combination (b * (u ⬝ᵥ (B *ᵥ x))) * H.2.1

theorem impl_D (a : Rˣ) {m : ℝ} (hm : 0 < m)
    (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    Impl ψ h B μ (mMat a) (opD m (a : R)) :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.impl_D H a hm hμ

theorem impl_fou_chiB : Impl ψ h B μ wMat (fou (chiB ψ B) μ) := by
  have hD := H.2.2.2.2.2
  have hh := hD
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  refine ⟨fun φ hφ => (fou_sb hD hφ).1, fun φ hφ => ?_, fun φ φ' hφ hφ' => fou_add hD hφ hφ',
    fun c φ _ => fou_smul c φ, fun φ hφ => planch hD hφ, fun x y φ _ => ?_⟩
  · have h1 := sb_homeo hφ (Homeomorph.neg _)
    exact ⟨_, (fou_sb hD h1).1, funext fun u => by rw [(fou_sb hD h1).2]; simp⟩
  · funext u
    simp only [Heisenberg₂, fou, wMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_smul, zero_smul, add_zero, zero_add, neg_smul, ← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ y]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [add_neg_cancel_right, chiB]
    rw [mul_left_comm, mul_right_comm, mul_comm _ (φ v), ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [mulVec_add, add_dotProduct, dotProduct_add, neg_dotProduct, bsym H.2.2.2.2.1 y u, bsym H.2.2.2.2.1 y x]
    linear_combination (x ⬝ᵥ (B *ᵥ y)) * H.2.1

theorem sq_pos_of_ne {φ : (ι → R) → ℂ} (hφ : SB φ) (hne : φ ≠ 0) : ∫ u, ‖φ u‖ ^ 2 ∂μ ≠ 0 := by
  have hh := H.2.2.2.2.2
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  intro h0
  have hc : Continuous fun u => ‖φ u‖ ^ 2 := hφ.1.continuous.norm.pow 2
  have h1 := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) (hc.integrable_of_hasCompactSupport
    (hφ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)))).1 h0
  have h2 := (hc.ae_eq_iff_eq μ continuous_zero).1 h1
  exact hne (funext fun u => by simpa using congrFun h2 u)

theorem impl_uniq {g : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g T') : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, SB φ → T' φ = c • T φ :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.impl_uniq H hT hT'

theorem weil_id (b : Rˣ) {m : ℝ} (hm : 0 < m) (hμ : ∀ s : Set (ι → R), MeasurableSet s →
      μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) =
      γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R)
        (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) := by
  have h1 := impl_mul (impl_U H b) (impl_fou_chiB H)
  have h2 := impl_mul (impl_fou_chiB H) (impl_mul (impl_U H (-((b⁻¹ : Rˣ) : R))) (impl_mul (impl_D H b⁻¹ hm hμ)
    (impl_mul (impl_fou_chiB H) (impl_U H (-((b⁻¹ : Rˣ) : R))))))
  have e : wMat * (nMat (-((b⁻¹ : Rˣ) : R)) * (mMat b⁻¹ * (wMat * nMat (-((b⁻¹ : Rˣ) : R))))) =
      nMat (b : R) * wMat := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [wMat, nMat, mMat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at h2
  exact impl_uniq H h2 h1

theorem orbit_bd (O : Set R) {L : AddSubgroup (ι → R)} (hL : CO L) (hst : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    {φ : (ι → R) → ℂ} (hφ : SB φ) (hfix : ∀ x ∈ L, ∀ y ∈ L, Heisenberg₂ ψ h B x y φ = φ) :
    ∃ (L' : AddSubgroup (ι → R)) (s : Finset (ι → R)) (C : ℝ), CO L' ∧ ∀ k : SL(2, R), (∀ i j, k i j ∈ O) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧ ∃ c : (ι → R) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.orbit_bd H O hL hst hφ hfix

end CompanionTheory.PlacePermOperatorBicommutantSpan
