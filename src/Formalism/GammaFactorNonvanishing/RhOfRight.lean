import Mathlib

open Complex

theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  unfold RiemannHypothesis
  intro s hs htriv hs1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hG : s.Gammaℝ ≠ 0 := by
      rw [Ne, Complex.Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      rcases n with _ | m
      · rw [Nat.cast_zero, mul_zero, neg_zero] at hn
        exact hs0 hn
      · apply htriv
        refine ⟨m, ?_⟩
        rw [Nat.cast_succ] at hn
        rw [hn]
        ring
    have hcz : completedRiemannZeta s = 0 := by
      have h := (riemannZeta_def_of_ne_zero hs0).symm
      rw [hs, div_eq_zero_iff] at h
      exact h.resolve_right hG
    have ht : 1 / 2 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have ht0 : (1 - s) ≠ 0 := fun h => hs1 (sub_eq_zero.mp h).symm
    have ht1 : (1 - s) ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
    have hzref : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero ht0, completedRiemannZeta_one_sub, hcz, zero_div]
    exact hz (1 - s) ht ht1 hzref
  · exact heq
  · exact absurd hs (hz s hgt hs1)
