import Mathlib

open TensorProduct in
theorem UpperTheory.Reformulated.B.Qf1.lam0 :
    ∀ (O B M : Type) [inst : CommRing O] [IsDomain O] [inst_2 : CommRing B] [inst_3 : Algebra O B]
    [inst_4 : AddCommGroup M] [inst_5 : _root_.Module B M] [Module.Finite B M] (x : B →ₐ[O] O),
    Module.annihilator B M ≤ RingHom.ker x →
      ∃ (lam : M →+ O) (m₀ : M),
        (∀ (a : B) (m : M), (lam : M → O) (a • m) = (x : B → O) a * (lam : M → O) m) ∧ (lam : M → O) m₀ ≠ (0 : O) := by
  intro O B M _ _ _ _ _ _ _ x hx
  classical
  set p : Ideal B := RingHom.ker x with hp
  haveI hpp : p.IsPrime := RingHom.ker_isPrime x
  have hs : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Module.support B M :=
    Module.mem_support_iff_of_finite.mpr hx
  have hnt : Nontrivial (p.ResidueField ⊗[B] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct (⟨p, hpp⟩ : PrimeSpectrum B)).mp hs
  obtain ⟨v, hv⟩ := exists_ne (0 : p.ResidueField ⊗[B] M)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero p.ResidueField hv
  let g : M →ₗ[B] p.ResidueField :=
    (f.restrictScalars B) ∘ₗ (TensorProduct.mk B p.ResidueField M 1)
  have hg : ∃ m₀, g m₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    have hzero : f.restrictScalars B = 0 := by
      refine TensorProduct.ext' fun k m => ?_
      change f (k ⊗ₜ[B] m) = 0
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul,
        show f ((1 : p.ResidueField) ⊗ₜ[B] m) = 0 from h m, smul_zero]
    exact DFunLike.congr_fun hzero v
  obtain ⟨m₀, hm₀⟩ := hg
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (B ⧸ p)) S
    (fun m => g m)
  let i : (B ⧸ p) →ₗ[B] p.ResidueField := (IsScalarTower.toAlgHom B (B ⧸ p) p.ResidueField).toLinearMap
  have hi : Function.Injective i := IsFractionRing.injective (B ⧸ p) p.ResidueField
  let c : p.ResidueField := algebraMap (B ⧸ p) p.ResidueField b
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let g' : M →ₗ[B] p.ResidueField := c • g
  have hr : ∀ m, g' m ∈ LinearMap.range i := by
    have hle : Submodule.span B (S : Set M) ≤ (LinearMap.range i).comap g' := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨z, hz⟩ := hb y hy
      refine ⟨z, ?_⟩
      change algebraMap _ _ z = c * g y
      rw [hz, Algebra.smul_def]
    intro m
    exact hle (hS ▸ Submodule.mem_top)
  let h : M →ₗ[B] (B ⧸ p) := LinearMap.codRestrictOfInjective g' i hi hr
  have hh : ∀ m, i (h m) = g' m := fun m =>
    LinearMap.codRestrictOfInjective_comp_apply g' i hi hr m
  let e : (B ⧸ p) →+* O := RingHom.kerLift (x : B →+* O)
  have he : Function.Injective e := RingHom.kerLift_injective (x : B →+* O)
  refine ⟨e.toAddMonoidHom.comp h.toAddMonoidHom, m₀, ?_, ?_⟩
  · intro a m
    change e (h (a • m)) = x a * e (h m)
    rw [map_smul, Algebra.smul_def, map_mul]
    rfl
  · change e (h m₀) ≠ 0
    intro h0
    have h1 : h m₀ = 0 := he (by rw [h0, map_zero])
    have h2 : g' m₀ = 0 := by rw [← hh m₀, h1, map_zero]
    exact mul_ne_zero hc hm₀ h2
