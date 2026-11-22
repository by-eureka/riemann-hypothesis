import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.URepSchur
import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection

namespace GroundTheory.Automorphic

namespace UnitaryRep

open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}

omit [CompleteSpace H] in

lemma nontrivial_endomorphisms [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : H →L[ℂ] H => T v) h)⟩⟩

theorem IsIrreducible.spectrum_subsingleton (hπ : π.IsIrreducible) {A : H →L[ℂ] H}
    (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) : (spectrum ℝ A).Subsingleton :=
  CompanionTheory.LimBd.URep.UnitaryRep.IsIrreducible.spectrum_subsingleton
    (π := (⟨π.toHom, π.continuous_orbit'⟩ : CompanionTheory.LimBd.URep.UnitaryRep G H))
    hπ hA hsa

theorem IsIrreducible.exists_eq_algebraMap_of_isSelfAdjoint (hπ : π.IsIrreducible)
    {A : H →L[ℂ] H} (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have := hπ.1
  have := nontrivial_endomorphisms (H := H)
  have hne : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hsa
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  have hsub := hπ.spectrum_subsingleton hA hsa
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hsa).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hsub hx hc
    _ = algebraMap ℝ _ c := cfc_const c A hsa

theorem IsIrreducible.exists_eq_smul_one (hπ : π.IsIrreducible) {T : H →L[ℂ] H}
    (hT : T ∈ π.intertwiners π) : ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  have hstar := star_mem_intertwiners hT
  have hre : (ℜ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [realPart_apply_coe]
    exact Submodule.smul_of_tower_mem _ _ (add_mem hT hstar)
  have him : (ℑ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [imaginaryPart_apply_coe]
    exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (sub_mem hT hstar))
  obtain ⟨a, ha⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint hre (ℜ T).2
  obtain ⟨b, hb⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint him (ℑ T).2
  refine ⟨a + I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

theorem isIrreducible_iff :
    π.IsIrreducible ↔
      Nontrivial H ∧ ∀ T ∈ π.intertwiners π, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  refine ⟨fun hπ => ⟨hπ.1, fun T hT => hπ.exists_eq_smul_one hT⟩, fun ⟨hnt, h⟩ => ⟨hnt, ?_⟩⟩
  intro V hcl hinv
  have : CompleteSpace V := hcl.completeSpace_coe
  have hP : V.starProjection ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun g => ((isInvariant_iff_commute_starProjection V).mp hinv g).symm
  obtain ⟨c, hc⟩ := h _ hP
  have hPv : ∀ v, V.starProjection v = c • v := fun v => by simp [hc]
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot, ← Submodule.starProjection_eq_self_iff.mpr hv, hPv, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have hmem : V.starProjection v ∈ V := V.starProjection_apply_mem v
    rw [hPv] at hmem
    simpa [hc0] using V.smul_mem c⁻¹ hmem

theorem IsIrreducible.isEquivalent_of_mem_intertwiners (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) (hT0 : T ≠ 0) :
    π.IsEquivalent σ := by
  obtain ⟨e⟩ := CompanionTheory.LimBd.URep.UnitaryRep.IsIrreducible.isEquivalent_of_mem_intertwiners
    (π := (⟨π.toHom, π.continuous_orbit'⟩ : CompanionTheory.LimBd.URep.UnitaryRep G H))
    (σ := (⟨σ.toHom, σ.continuous_orbit'⟩ : CompanionTheory.LimBd.URep.UnitaryRep G K))
    hπ hσ hT hT0
  exact ⟨⟨e.toLinearIsometryEquiv, e.map_apply'⟩⟩

theorem IsIrreducible.exists_eq_smul_of_mem_intertwiners (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {S T : H →L[ℂ] K} (hS : S ∈ π.intertwiners σ)
    (hT : T ∈ π.intertwiners σ) (hS0 : S ≠ 0) : ∃ c : ℂ, T = c • S := by
  obtain ⟨a, ha⟩ := hπ.exists_eq_smul_one
    (comp_mem_intertwiners (adjoint_mem_intertwiners hS) hT)
  obtain ⟨d, hd⟩ := hσ.exists_eq_smul_one
    (comp_mem_intertwiners hS (adjoint_mem_intertwiners hS))
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hS0
    have hSS : S ∘L adjoint S = 0 := by rw [hd, zero_smul]
    have hadj : adjoint S = 0 := by
      ext w
      have h1 : ⟪adjoint S w, adjoint S w⟫_ℂ = ⟪w, (S ∘L adjoint S) w⟫_ℂ := by
        rw [comp_apply, adjoint_inner_left]
      rw [hSS, zero_apply, inner_zero_right, inner_self_eq_zero] at h1
      simpa using h1
    rw [← adjoint_adjoint S, hadj, map_zero]
  refine ⟨a / d, ?_⟩
  have e1 : S ∘L (adjoint S ∘L T) = a • S := by rw [ha]; ext v; simp
  have e2 : (S ∘L adjoint S) ∘L T = d • T := by rw [hd]; ext v; simp
  have e3 : d • T = a • S := by rw [← e1, ← e2, comp_assoc]
  rw [div_eq_inv_mul, mul_smul, ← e3, smul_smul, inv_mul_cancel₀ hd0, one_smul]

theorem IsIrreducible.eq_zero_of_not_isEquivalent (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hne : ¬ π.IsEquivalent σ) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) : T = 0 := by
  by_contra h
  exact hne (hπ.isEquivalent_of_mem_intertwiners hσ hT h)

end UnitaryRep

end GroundTheory.Automorphic
