import Mathlib

theorem _root_.UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (eD : R), Function.Bijective (act eD) → ∀ (F : ℤ → W → Prop), (∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (β : ℕ) (h b : ι → W) (m m' : Matrix ι ι R), m' * m = 1 → (∀ i, h i = ∑ k, act (eD ^ β * m i k) (b k)) → (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k)) → ∀ w, F (β : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i) := by
  intro R W _ _ act hmul hone eD hbij F hF ι _ _ β h b m m' hm hh hF0 w
  let ψ : R →* Function.End W :=
    { toFun := fun r w => act r w, map_one' := funext hone,
      map_mul' := fun r s => funext (hmul r s) }
  have hmain : ∀ (n : ℕ) (y : W), F 0 y ↔ F n (act (eD ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; simp [hone]
    | succ n ih =>
      intro y
      simpa [Nat.cast_succ, pow_succ', hmul] using (ih y).trans (hF (act (eD ^ n) y) ↑n)
  have hbij' : Function.Bijective (act (eD ^ β)) := by
    rw [show ⇑(act (eD ^ β)) = (act eD)^[β] from map_pow ψ eD β]
    exact hbij.iterate β
  have hexp : ∀ e : ι → R,
      ∑ i, act (e i) (h i) = act (eD ^ β) (∑ k, act (Matrix.vecMul e m k) (b k)) := by
    intro e
    simp only [hh, map_sum, AddMonoidHom.finsetSum_apply, ← hmul, Matrix.vecMul_apply_eq_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨y, rfl⟩ := hbij'.2 w
  rw [← hmain β y, hF0]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨Matrix.vecMul d m', ?_⟩
    simp only [hexp, Matrix.vecMul_vecMul, hm, Matrix.vecMul_one, hd]
  · rintro ⟨e, he⟩
    exact ⟨Matrix.vecMul e m, hbij'.1 (by rw [he, hexp])⟩
