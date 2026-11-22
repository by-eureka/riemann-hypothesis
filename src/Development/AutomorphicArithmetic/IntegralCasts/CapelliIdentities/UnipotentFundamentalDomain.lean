import Mathlib

theorem UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K],
    Module.finrank ℚ K ≤ (2 : ℕ) →
      ∀ (P Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        P ≠ Q →
          Ideal.under ℤ P.asIdeal = Ideal.under ℤ Q.asIdeal →
            (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion K P → WithZero (Multiplicative ℤ))
                (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) P.asIdeal) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion K P) =
              WithZero.exp (-1 : ℤ) := by
  intro K _ _ hn P Q hPQ hunder
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have hQm : Q.asIdeal.IsMaximal := Q.isMaximal
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (IsDedekindDomain.HeightOneSpectrum.ext h)
  -- the rational prime `p` lying below both `P` and `Q`
  obtain ⟨p, hp, hpunder⟩ : ∃ p : ℕ, p.Prime ∧ Ideal.under ℤ P.asIdeal = Ideal.span {(p : ℤ)} := by
    obtain ⟨p, hp, hP⟩ :=
      (Ideal.isPrime_int_iff.1 (Ideal.IsPrime.under ℤ P.asIdeal)).resolve_left
        (Ideal.under_ne_bot ℤ P.ne_bot)
    exact ⟨p, hp, hP⟩
  have hqunder : Ideal.under ℤ Q.asIdeal = Ideal.span {(p : ℤ)} := hunder ▸ hpunder
  have hmem : ∀ (S : Ideal (NumberField.RingOfIntegers K)),
      Ideal.under ℤ S = Ideal.span {(p : ℤ)} → (p : NumberField.RingOfIntegers K) ∈ S := by
    intro S hS
    have : (p : ℤ) ∈ Ideal.under ℤ S := by rw [hS]; exact Ideal.subset_span rfl
    simpa [Ideal.under_def, Ideal.mem_comap] using this
  have hpP : (p : NumberField.RingOfIntegers K) ∈ P.asIdeal := hmem P hpunder
  have hpQ : (p : NumberField.RingOfIntegers K) ∈ Q.asIdeal := hmem Q hqunder
  -- both `P` and `Q` divide `(p)`, so their product does, and norms give the exponents
  have hspan_norm : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers K)}) =
      p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  have hdvd : P.asIdeal * Q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime (hPm.coprime_of_ne hQm hne)]
    exact le_inf ((Ideal.span_singleton_le_iff_mem _).2 hpP)
      ((Ideal.span_singleton_le_iff_mem _).2 hpQ)
  have hmul : Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal ∣ p ^ Module.finrank ℚ K := by
    rw [← hspan_norm, ← map_mul]
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.1 hdvd)
  have hPne : Ideal.absNorm P.asIdeal ≠ 1 := fun h => hPm.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hQne : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => hQm.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 (dvd_trans (dvd_mul_right _ _) hmul)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 (dvd_trans (dvd_mul_left _ _) hmul)
  have ha0 : a ≠ 0 := fun h => hPne (by rw [ha, h, pow_zero])
  have hb0 : b ≠ 0 := fun h => hQne (by rw [hb, h, pow_zero])
  have hsum : a + b ≤ Module.finrank ℚ K := by
    have h : p ^ (a + b) ∣ p ^ Module.finrank ℚ K := by rwa [pow_add, ← ha, ← hb]
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have ha1 : a = 1 := by omega
  have hb1 : b = 1 := by omega
  have hdim : Module.finrank ℚ K = 2 := by omega
  have hNP : Ideal.absNorm P.asIdeal = p := by rw [ha, ha1, pow_one]
  have hNQ : Ideal.absNorm Q.asIdeal = p := by rw [hb, hb1, pow_one]
  -- a product of ideals of norm `p ^ 2` dividing `(p)` is `(p)` itself
  obtain ⟨J, hJ⟩ := hdvd
  have hJtop : J = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff]
    have h : Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal * Ideal.absNorm J = p ^ 2 := by
      rw [← map_mul, ← map_mul, ← hJ, hspan_norm, hdim]
    rw [hNP, hNQ, pow_two] at h
    exact Nat.mul_left_cancel (Nat.mul_pos hp.pos hp.pos) (by simpa using h)
  have hspan : Ideal.span {(p : NumberField.RingOfIntegers K)} = P.asIdeal * Q.asIdeal := by
    rw [hJ, hJtop, Ideal.mul_top]
  -- so `p` is a uniformizer at `P`
  have hp0 : (p : NumberField.RingOfIntegers K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h1 : P.intValuation (p : NumberField.RingOfIntegers K) ≤
      WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_one]
    exact dvd_mul_right _ _
  have h2 : ¬ P.intValuation (p : NumberField.RingOfIntegers K) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_two]
    intro h
    refine hne ((hQm.eq_of_le hPm.ne_top ?_).symm)
    exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left P.ne_bot).1 h)
  have hval : P.intValuation (p : NumberField.RingOfIntegers K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hp0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    omega
  rw [hNP]
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) P
    (p : NumberField.RingOfIntegers K)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval] at key
  simpa using key
