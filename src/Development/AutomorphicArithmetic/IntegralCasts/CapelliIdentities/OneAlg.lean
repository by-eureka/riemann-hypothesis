import Mathlib

open Polynomial in
theorem UpperTheory.Reformulated.B.Ra3.one_alg :
    ∀ (R S : Type) [inst : CommRing R] [IsDomain R]
    [inst_2 : CommRing S] [IsDomain S] [inst_4 : Algebra R S],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (x : S),
        Function.Surjective (⇑(Polynomial.aeval x) : Polynomial R → S) →
          IsAlgebraic R x →
            ∀ (c : S),
              c ≠ (0 : S) →
                ∃ (b : R),
                  b ≠ (0 : R) ∧
                    ∀ (K : Type) [inst_5 : Field K] [IsAlgClosed K] (y : R →+* K),
                      (y : R → K) b ≠ (0 : K) →
                        ∃ (ξ : S →+* K), ξ.comp (Algebra.algebraMap R S) = y ∧ (ξ : S → K) c ≠ (0 : K) := by
  classical
  intro R S _ _ _ _ _ hinj x hsurj halg c hc
  have hcalg : IsAlgebraic R c := by
    obtain ⟨g, rfl⟩ := hsurj c
    exact Algebra.isAlgebraic_adjoin_singleton_iff.mpr halg _
      (Polynomial.aeval_mem_adjoin_singleton R x)
  obtain ⟨b', hb', w, hw⟩ := hcalg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)
  obtain ⟨q0, hq0, hq0x⟩ := halg
  have hex : ∃ n, ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0 ∧ p.natDegree = n :=
    ⟨_, q0, hq0, hq0x, rfl⟩
  obtain ⟨p, hp0, hpx, hpn⟩ := Nat.find_spec hex
  have hmin : ∀ f : R[X], f ≠ 0 → aeval x f = 0 → p.natDegree ≤ f.natDegree := fun f hf hfx => by
    rw [hpn]
    exact Nat.find_min' hex ⟨f, hf, hfx, rfl⟩
  have hpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [eq_C_of_natDegree_eq_zero h, aeval_C] at hpx
      refine hp0 ?_
      rw [eq_C_of_natDegree_eq_zero h, show p.coeff 0 = 0 from hinj (by simpa using hpx), C_0]
    · exact h
  refine ⟨p.leadingCoeff * b', mul_ne_zero (leadingCoeff_ne_zero.mpr hp0) hb', ?_⟩
  intro K _ _ y hy
  rw [map_mul] at hy
  have hya : y p.leadingCoeff ≠ 0 := left_ne_zero_of_mul hy
  have hyb : y b' ≠ 0 := right_ne_zero_of_mul hy
  have hdeg : (p.map y).degree ≠ 0 := by
    rw [degree_map_eq_of_leadingCoeff_ne_zero y hya]
    exact (natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (p.map y) hdeg
  have htp : eval₂ y t p = 0 := by rwa [IsRoot.def, eval_map] at ht
  have hker : ∀ f : R[X], aeval x f = 0 → eval₂ y t f = 0 := by
    intro f
    induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n ih =>
      intro hfx
      by_cases h0 : f = 0
      · simp [h0]
      have hle := hmin f h0 hfx
      have hfpos : 0 < f.natDegree := lt_of_lt_of_le hpos hle
      have hcx : aeval x (p.cancelLeads f) = 0 := by simp [cancelLeads, hpx, hfx]
      have hlt := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hle hfpos
      have h1 := ih _ (by rw [← hd]; exact hlt) _ rfl hcx
      simp [cancelLeads, htp, Nat.sub_eq_zero_of_le hle] at h1
      exact h1.resolve_left hya
  let φ : R[X] →+* S := (aeval x : R[X] →ₐ[R] S).toRingHom
  let ψ : R[X] →+* K := eval₂RingHom y t
  have hk : RingHom.ker φ ≤ RingHom.ker ψ := hker
  let ξ : S →+* K := RingHom.liftOfSurjective φ hsurj ⟨ψ, hk⟩
  have hξ : ∀ f, ξ (φ f) = ψ f := fun f =>
    RingHom.liftOfRightInverse_comp_apply φ _ _ ⟨ψ, hk⟩ f
  have halgm : ∀ r : R, ξ (Algebra.algebraMap R S r) = y r := fun r => by
    have h2 : φ (C r) = Algebra.algebraMap R S r := aeval_C x r
    rw [← h2, hξ]
    simp [ψ]
  refine ⟨ξ, RingHom.ext halgm, fun h => hyb ?_⟩
  rw [← halgm b', hw, map_mul, h, zero_mul]
