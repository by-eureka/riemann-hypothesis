import Mathlib

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem finite_le_of_posDef {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hS : ∀ x y, B x y = B y x) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (A : Submodule ℤ V) (hA : A.FG) (c : ℚ) : {v | v ∈ A ∧ B v v ≤ c}.Finite := by
  classical
  obtain ⟨S, hS'⟩ := hA
  have hnn : ∀ v, 0 ≤ B v v := fun v =>
    if hv : v = 0 then by simp [hv] else (hpos v hv).le

  have cs : ∀ v w, B v w ^ 2 ≤ B v v * B w w := by
    intro v w
    by_cases hw : w = 0
    · simp [hw]
    · have hww := hpos w hw
      have key := hnn (B w w • v - B v w • w)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hS w v] at key
      nlinarith [hww, key]
  let b := Module.finBasis ℚ V
  have hinj : ∀ v w, (∀ i, B v (b i) = B w (b i)) → v = w := by
    intro v w h
    by_contra hne
    have h1 := hpos (v - w) (sub_ne_zero.2 hne)
    rw [show B (v - w) = 0 from b.ext fun i => by simp [map_sub, h i]] at h1
    simp at h1
  let N : ℕ := ∏ s ∈ S, ∏ i, (B s (b i)).den
  have hNpos : 0 < N :=
    Finset.prod_pos fun s _ => Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (Rat.den_nz _)

  have hint : ∀ v ∈ A, ∀ i, ∃ z : ℤ, (z : ℚ) = N * B v (b i) := by
    intro v hv
    rw [← hS'] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro i
      have hd : (B x (b i)).den ∣ N :=
        (Finset.dvd_prod_of_mem (fun i => (B x (b i)).den) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun s => ∏ i, (B s (b i)).den) hx)
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * (B x (b i)).num, ?_⟩
      have e := Rat.mul_den_eq_num (B x (b i))
      rw [hk]
      push_cast
      linear_combination (-(k : ℚ)) * e
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨z1, h1⟩ := hx i
      obtain ⟨z2, h2⟩ := hy i
      refine ⟨z1 + z2, ?_⟩
      rw [map_add, LinearMap.add_apply]
      push_cast
      rw [h1, h2]
      ring
    | smul a x _ hx =>
      intro i
      obtain ⟨z, hz⟩ := hx i
      refine ⟨a * z, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [hz]
      ring
  have hbd : ∀ v, B v v ≤ c → ∀ i, |B v (b i)| ≤ 1 + |c| * B (b i) (b i) := by
    intro v hv i
    have h1 := cs v (b i)
    have h2 : B v v * B (b i) (b i) ≤ |c| * B (b i) (b i) :=
      mul_le_mul_of_nonneg_right (hv.trans (le_abs_self c)) (hnn _)
    nlinarith [h1, h2, sq_abs (B v (b i)), sq_nonneg (|B v (b i)| - 1)]
  let g : V → Fin (Module.finrank ℚ V) → ℤ := fun v i => round ((N : ℚ) * B v (b i))
  have hg : ∀ v ∈ A, ∀ i, ((g v i : ℤ) : ℚ) = N * B v (b i) := by
    intro v hv i
    obtain ⟨z, hz⟩ := hint v hv i
    simp only [g]
    rw [← hz, round_intCast]
  let K : Fin (Module.finrank ℚ V) → ℤ := fun i => ⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉
  apply Set.Finite.of_finite_image (f := g)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun i => Set.Icc (-(K i)) (K i))
      fun i => Set.finite_Icc _ _) ?_
    rintro _ ⟨v, ⟨hvA, hvc⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have hK : |((g v i : ℤ) : ℚ)| ≤ (K i : ℚ) := by
      rw [hg v hvA i, abs_mul, Nat.abs_cast]
      exact (mul_le_mul_of_nonneg_left (hbd v hvc i) (Nat.cast_nonneg _)).trans (Int.le_ceil _)
    exact_mod_cast abs_le.mp hK
  · rintro v ⟨hvA, -⟩ w ⟨hwA, -⟩ hvw
    apply hinj
    intro i
    have e : (N : ℚ) * B v (b i) = N * B w (b i) := by
      rw [← hg v hvA i, ← hg w hwA i, congrFun hvw i]
    exact mul_left_cancel₀ (by exact_mod_cast hNpos.ne') e

end PI.UnitaryGroupMassFormula.CntFormula
