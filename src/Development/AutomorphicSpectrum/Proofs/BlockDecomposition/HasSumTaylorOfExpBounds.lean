import Mathlib

open Filter Topology Set

namespace GlobalTheory.CompanionTheory.TaylorGlobal

theorem hasSum_taylor_of_exp_bounds (n : ℕ) (c : (Fin n → ℝ) → ℂ) (C R M : ℝ)
    (hc : ContDiff ℝ ⊤ c)
    (hb : ∀ (k : ℕ) (H v : Fin n → ℝ),
      ‖iteratedFDeriv ℝ k c H (fun _ => v)‖ ≤ M * (C * ‖v‖) ^ k * Real.exp (R * ‖H‖))
    (H h : Fin n → ℝ) :
    HasSum (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * iteratedFDeriv ℝ k c H (fun _ => h))
      (c (H + h)) := by
  set L : ℝ →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.toSpanSingleton ℝ h with hL
  have hLt : ∀ t : ℝ, L t = t • h := fun t => by simp [hL]
  have hcH : ContDiff ℝ ⊤ (fun z : Fin n → ℝ => c (H + z)) :=
    hc.comp (contDiff_const.add contDiff_id)
  set g : ℝ → ℂ := (fun z : Fin n → ℝ => c (H + z)) ∘ L with hg
  have hgs : ContDiff ℝ ⊤ g := hcH.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j g t = iteratedFDeriv ℝ j c (H + t • h) (fun _ => h) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hg,
      L.iteratedFDeriv_comp_right hcH t le_top,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_comp_add_left]
    simp [hLt]
  set A : ℝ := |C| * ‖h‖ with hA
  set E : ℝ := Real.exp (|R| * (‖H‖ + ‖h‖)) with hE
  have bnd : ∀ (k : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      ‖iteratedDeriv k g t‖ ≤ |M| * A ^ k * E := by
    intro k t ht
    rw [key]
    have hn : ‖H + t • h‖ ≤ ‖H‖ + ‖h‖ := by
      have h1 : ‖t • h‖ ≤ ‖h‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      linarith [norm_add_le H (t • h)]
    have hexp : Real.exp (R * ‖H + t • h‖) ≤ E := by
      rw [hE]
      exact Real.exp_le_exp.2 (mul_le_mul (le_abs_self R) hn (norm_nonneg _) (abs_nonneg R))
    have hpow : M * (C * ‖h‖) ^ k ≤ |M| * A ^ k := by
      calc M * (C * ‖h‖) ^ k ≤ |M * (C * ‖h‖) ^ k| := le_abs_self _
        _ = |M| * A ^ k := by
            rw [abs_mul, abs_pow, abs_mul, abs_norm]
    calc ‖iteratedFDeriv ℝ k c (H + t • h) (fun _ => h)‖
        ≤ M * (C * ‖h‖) ^ k * Real.exp (R * ‖H + t • h‖) := hb k _ _
      _ ≤ |M| * A ^ k * E := mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
  have hD : ∀ k : ℕ, iteratedFDeriv ℝ k c H (fun _ => h) = iteratedDeriv k g 0 := by
    intro k
    simpa using (key k 0).symm
  have hsum : Summable
      (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k g 0) := by
    have hs0 : Summable (fun k : ℕ => |M| * E * (A ^ k / (Nat.factorial k : ℝ))) :=
      (Real.summable_pow_div_factorial A).mul_left _
    refine Summable.of_norm_bounded hs0 ?_
    intro k
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have := bnd k 0 (by simp)
    have hf : (0 : ℝ) ≤ ((Nat.factorial k : ℝ))⁻¹ := by positivity
    calc ((Nat.factorial k : ℝ))⁻¹ * ‖iteratedDeriv k g 0‖
        ≤ ((Nat.factorial k : ℝ))⁻¹ * (|M| * A ^ k * E) := mul_le_mul_of_nonneg_left this hf
      _ = |M| * E * (A ^ k / (Nat.factorial k : ℝ)) := by ring
  have htay : ∀ m : ℕ, taylorWithinEval g m (Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (m + 1), ((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k g 0 := by
    intro m
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hgs.contDiffAt.of_le le_top) (by simp)]
    simp [Complex.real_smul]
  have hrem : ∀ m : ℕ, ‖g 1 - taylorWithinEval g m (Icc 0 1) 0 1‖ ≤
      |M| * E * A * (A ^ m / (Nat.factorial m : ℝ)) := by
    intro m
    have h1 := taylor_mean_remainder_bound (f := g) (a := 0) (b := 1) (x := 1) (n := m)
      (C := |M| * A ^ (m + 1) * E) zero_le_one
      (hgs.contDiffOn.of_le le_top) (by simp) (by
        intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
          (hgs.contDiffAt.of_le le_top) hy]
        exact bnd _ y hy)
    refine h1.trans (le_of_eq ?_)
    rw [sub_zero, one_pow, mul_one]
    ring
  have hlim : Tendsto (fun m : ℕ => taylorWithinEval g m (Icc 0 1) 0 1) atTop (𝓝 (g 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun m : ℕ => |M| * E * A * (A ^ m / (Nat.factorial m : ℝ)))
        atTop (𝓝 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop A).const_mul (|M| * E * A)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h0
    rw [norm_sub_rev]
    exact hrem m
  have hg1 : g 1 = c (H + h) := by simp [hg, hLt]
  have hmain : HasSum (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * iteratedDeriv k g 0) (g 1) := by
    rw [hsum.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
    simpa only [htay] using hlim
  simpa [hD, hg1] using hmain

end GlobalTheory.CompanionTheory.TaylorGlobal
