import Mathlib

namespace GroundTheory.Variant₂.N1

theorem eq_one_of_forall_norm_zpow_sub_one_lt {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) :
    z = 1 := by
  have hpow : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 := fun n => by simpa using h n
  have hbound : ∀ w : ℂ, (∀ n : ℕ, ‖w ^ n - 1‖ < 1) → ‖w‖ ≤ 1 := by
    intro w hw
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hlt
    have h2 : ‖w ^ n‖ - 1 ≤ ‖w ^ n - 1‖ := by
      simpa using norm_sub_norm_le (w ^ n) 1
    rw [norm_pow] at h2
    linarith [hw n]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simpa using hpow 1
  have hge : 1 ≤ ‖z‖ := by
    have h1 : ‖z⁻¹‖ ≤ 1 := by
      refine hbound _ fun n => ?_
      simpa [zpow_neg, ← inv_pow] using h (-(n : ℤ))
    simpa [norm_inv, inv_le_one₀ (norm_pos_iff.mpr hz0)] using h1
  have hn1 : ‖z‖ = 1 := le_antisymm (hbound z hpow) hge
  have key : ∀ w : ℂ, ‖w‖ = 1 → ‖w - 1‖ < 1 → 3 * ‖w - 1‖ ^ 2 ≤ ‖w ^ 2 - 1‖ ^ 2 := by
    intro w hw hw1
    have hpar := parallelogram_law_with_norm (𝕜 := ℂ) w 1
    rw [hw, norm_one] at hpar
    have hlt : ‖w - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (w - 1)]
    rw [show w ^ 2 - 1 = (w - 1) * (w + 1) by ring, norm_mul, mul_pow]
    nlinarith
  have hk : ∀ k : ℕ, 3 ^ k * ‖z - 1‖ ^ 2 ≤ ‖z ^ (2 ^ k) - 1‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h4 := key (z ^ (2 ^ k)) (by rw [norm_pow, hn1, one_pow]) (hpow _)
      rw [pow_succ 2 k, pow_mul]
      calc (3 : ℝ) ^ (k + 1) * ‖z - 1‖ ^ 2 = 3 * (3 ^ k * ‖z - 1‖ ^ 2) := by ring
        _ ≤ 3 * ‖z ^ (2 ^ k) - 1‖ ^ 2 := by gcongr
        _ ≤ _ := h4
  by_contra hne
  have hd : 0 < ‖z - 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖ ^ 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := hk k
  have h6 := hpow (2 ^ k)
  have h7 : ‖z ^ (2 ^ k) - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (z ^ (2 ^ k) - 1)]
  have h8 : 1 < 3 ^ k * ‖z - 1‖ ^ 2 := by rwa [div_lt_iff₀ hd] at hk'
  linarith

end GroundTheory.Variant₂.N1
