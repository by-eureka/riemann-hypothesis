import Mathlib

open NumberField

theorem UpperTheory.Reformulated.B.Qh9.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  have hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx φ
      simpa [hx] using (hc x φ).symm
    · intro hx
      apply φ₀.injective
      simpa [hc] using hx φ₀
  have hinv : ∀ x : K, c (c x) = x := fun x => φ₀.injective (by simp [hc])
  let σ : K ≃ₐ[maximalRealSubfield K] K :=
    { toFun := c
      invFun := c
      left_inv := hinv
      right_inv := hinv
      map_mul' := fun x y => φ₀.injective (by simp [hc])
      map_add' := fun x y => φ₀.injective (by simp [hc])
      commutes' := fun x => (hfix _).mpr x.2 }
  have hconj : ComplexEmbedding.IsConj φ₀ σ := RingHom.ext fun x => (hc x φ₀).symm
  have hne : σ ≠ 1 :=
    (ComplexEmbedding.isConj_ne_one_iff hconj).mpr
      (IsTotallyComplex.complexEmbedding_not_isReal φ₀)
  have hord : orderOf σ = 2 := ComplexEmbedding.orderOf_isConj_two_of_ne_one hconj hne
  have hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.mpr
      ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩
  have hrank := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord] at hrank
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := ⟨hrank⟩
  exact ⟨⟩
