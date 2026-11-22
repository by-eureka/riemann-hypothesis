import Mathlib
open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

theorem extends_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  intro O F L _ _ _ β θ hcl hu hz
  set R : Subring F := β.range with hR
  have hk : ∀ a ∈ RingHom.ker β, θ a = 0 := fun a ha => hz a ((RingHom.mem_ker).mp ha)
  let θR : R →+* L :=
    (Ideal.Quotient.lift (RingHom.ker β) θ hk).comp (RingHom.quotientKerEquivRange β).symm.toRingHom
  have hθR : ∀ o : O, θR ⟨β o, o, rfl⟩ = θ o := by
    intro o
    have h : (RingHom.quotientKerEquivRange β).symm ⟨β o, o, rfl⟩ = Ideal.Quotient.mk _ o := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp [θR, h, Ideal.Quotient.lift_mk]
  have hunit : ∀ r : nonZeroDivisors R, IsUnit (θR r) := by
    intro r
    obtain ⟨b, hb⟩ := (r : R).2
    have hne : (r : R) ≠ 0 := nonZeroDivisors.ne_zero r.2
    have hr : (r : R) = ⟨β b, b, rfl⟩ := Subtype.ext hb.symm
    rw [hr, hθR]
    exact hu b fun h0 => hne (by rw [hr]; exact Subtype.ext h0)
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  let ι : FractionRing R →+* F := IsFractionRing.lift hinj
  have hsurj : Function.Surjective ι := by
    rw [← RingHom.fieldRange_eq_top_iff, IsFractionRing.lift_fieldRange hinj, Subring.range_subtype,
      hR, RingHom.coe_range, hcl]
  let e : FractionRing R ≃+* F := RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩
  refine ⟨(IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hunit).comp
    e.symm, ?_⟩
  ext o
  have he : e.symm (β o) = algebraMap R (FractionRing R) ⟨β o, o, rfl⟩ := by
    rw [RingEquiv.symm_apply_eq]
    show β o = ι (algebraMap R (FractionRing R) ⟨β o, o, rfl⟩)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  simp [he, IsLocalization.lift_eq, hθR]

end PositivityTheory.UnitarySelfGeneration
