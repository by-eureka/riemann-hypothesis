import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS

noncomputable section

namespace PI.VolStabSW

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) :=
  PI.VolStabW.FiniteFieldCounting.prod_bound δ t ht0 ht1 h s

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
  zify [h1, ha]
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
    have h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1) := by nlinarith
    have h3 : a ≤ M := by omega
    have h4 : 1 ≤ 2 * (M - a) := by omega
    zify [h1, h2, h3, h4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hM : q ^ M ≠ 0 := pow_ne_zero _ hq
  have e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]
  have h1 : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) =
      q ^ (2 * (M - j) - 1) *
        (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
    intro j
    have : q ^ (2 * (M - j) - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring
  rw [Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]
  have h1 : q ^ (2 * M * a - a ^ 2) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hMi : q ^ M = q ^ (i : ℕ) * q ^ (M - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hq0
  have e : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    rw [hMi, inv_pow]
    field_simp
  rw [abs_neg, e, abs_of_nonneg (by positivity)]
  exact inv_pow_le q hq _ (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hexp : q ^ (2 * (M - j) - 1) = q ^ (M - j - 1) * q ^ (M - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (M - j - 1) ≠ 0 := pow_ne_zero _ hq0
  have e : |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| = (q⁻¹) ^ (M - j) := by
    rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hexp,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), inv_pow]
    field_simp
  rw [e]
  exact inv_pow_le q hq _ (by omega)

theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} :=
  PI.VolStabW.FiniteFieldCounting.card_transport σ e he J T

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := PI.VolStabW.fFCount_of hS hI

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabSW
