import Mathlib

theorem UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq :
    ∀ {O R K : Type} [inst : CommRing O]
    [inst_1 : CommRing R] [inst_2 : Algebra O R] [IsNoetherianRing R] [inst_4 : CommRing K] [inst_5 : Algebra O K]
    (y : R →ₐ[O] K),
    Module.Finite O ↥y.range →
      ∃ (s : Finset R), ∀ (a : R), ∃ b ∈ Submodule.span O (↑s : Set R), a - b ∈ RingHom.ker y ^ (2 : ℕ) := by
  intro O R K _ _ _ _ _ _ y hfin
  classical
  obtain ⟨t', ht'⟩ := hfin.fg_top
  obtain ⟨σ, hσ⟩ := y.rangeRestrict_surjective.hasRightInverse
  obtain ⟨g, hg⟩ : (RingHom.ker y).FG := IsNoetherian.noetherian _
  let t : Finset R := t'.image σ
  have h1 : ∀ a : R, ∃ b ∈ Submodule.span O (↑t : Set R), a - b ∈ RingHom.ker y := by
    intro a
    have hm : Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) = ⊤ := by
      rw [Submodule.map_span, eq_top_iff, ← ht']
      exact Submodule.span_mono fun z hz =>
        ⟨σ z, Finset.mem_coe.2 (Finset.mem_image_of_mem σ hz), hσ z⟩
    obtain ⟨b, hb, hab⟩ := (hm ▸ Submodule.mem_top : y.rangeRestrict a ∈ _)
    refine ⟨b, hb, ?_⟩
    have hab' : y b = y a := congrArg Subtype.val hab
    rw [RingHom.mem_ker, map_sub, hab', sub_self]
  let s : Finset R := t ∪ Finset.image₂ (· * ·) t g
  have h2 : Submodule.span O (↑t : Set R) * Submodule.span O (↑g : Set R)
      ≤ Submodule.span O (↑s : Set R) := by
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨b, hb, x, hx, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hb hx))
  have h3 : ∀ x ∈ Ideal.span (↑g : Set R), ∀ r : R,
      ∃ b ∈ Submodule.span O (↑s : Set R), r * x - b ∈ RingHom.ker y ^ (2 : ℕ) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      intro r
      obtain ⟨b, hb, hrb⟩ := h1 r
      refine ⟨b * z, h2 (Submodule.mul_mem_mul hb (Submodule.subset_span hz)), ?_⟩
      have hzI : z ∈ RingHom.ker y := by
        rw [← hg]; exact Ideal.subset_span hz
      rw [← sub_mul, pow_two]
      exact Ideal.mul_mem_mul hrb hzI
    | zero => intro r; exact ⟨0, zero_mem _, by simp⟩
    | add u v _ _ hu hv =>
      intro r
      obtain ⟨b, hb, hb'⟩ := hu r
      obtain ⟨c, hc, hc'⟩ := hv r
      refine ⟨b + c, add_mem hb hc, ?_⟩
      have e : r * (u + v) - (b + c) = (r * u - b) + (r * v - c) := by ring
      rw [e]; exact add_mem hb' hc'
    | smul c u _ hu =>
      intro r
      rw [smul_eq_mul, ← mul_assoc]
      exact hu (r * c)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨b, hb, hab⟩ := h1 a
  obtain ⟨c, hc, hc'⟩ := h3 (a - b) (by rwa [hg]) 1
  refine ⟨b + c, add_mem (Submodule.span_mono (Finset.coe_subset.2 Finset.subset_union_left) hb) hc, ?_⟩
  simpa [sub_add_eq_sub_sub, one_mul] using hc'
