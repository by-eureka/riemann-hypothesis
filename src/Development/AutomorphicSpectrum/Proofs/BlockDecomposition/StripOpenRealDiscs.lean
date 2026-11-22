import Mathlib

namespace GlobalTheory.CompanionTheory.Strip

theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  -- the admissible imaginary parts form an open subset of the real line
  have hV : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  refine ⟨?_, ?_, ?_⟩
  · rw [hS, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · simp [hS, Real.pi_pos]
  · intro z hz
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp hV _ (by simpa only [hS, abs_mul, Set.mem_ofPred_eq] using hz)
    have hρ : ∀ j, (|z.im| + ε / 2) * |X j| < Real.pi / 4 :=
      hball (show |z.im| + ε / 2 ∈ Metric.ball |z.im| ε by
        rw [Real.ball_eq_Ioo]
        constructor <;> linarith)
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball]
      simp [Complex.dist_eq, Complex.norm_def, Complex.normSq, Real.sqrt_mul_self_eq_abs, hε]
    · intro w hw j
      rw [Metric.mem_ball] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h := Complex.abs_im_le_norm (w - (z.re : ℂ))
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, dist_eq_norm] at h hw
        linarith
      calc |w.im * X j| = |w.im| * |X j| := abs_mul _ _
        _ ≤ (|z.im| + ε / 2) * |X j| := mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ j

end GlobalTheory.CompanionTheory.Strip
