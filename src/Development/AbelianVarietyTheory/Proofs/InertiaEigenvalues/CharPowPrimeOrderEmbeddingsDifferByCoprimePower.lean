import Mathlib
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charPowPrimeOrder_embeddings_differ_by_coprime_power :
    ∀ (Γ : Type) [Group Γ] (C : Type) [Field C] [CharZero C] (l n : ℕ), l.Prime →
      ∀ (ψ : Γ →* Cˣ), (∀ g, ψ g ^ (l ^ n) = 1) → ∀ e e' : C →+* ℂ,
        ∃ a : ℕ, Nat.Coprime a l ∧ ∀ g, e' ((ψ g : Cˣ) : C) = e (((ψ g ^ a : Cˣ)) : C) := by
  intro Γ _ C _ _ l n hl ψ hψ e e'
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) C)
  set u : Cˣ := (ζ : Cˣ) with hu
  set k := orderOf u with hk
  have hkd : k ∣ l ^ n := orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity _ _).mp ζ.2)
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkd (NeZero.pos (l ^ n))
  have : NeZero k := ⟨hk0.ne'⟩
  have hpu : IsPrimitiveRoot (u : C) k := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf u)
  have h1 : IsPrimitiveRoot (e (u : C)) k := hpu.map_of_injective e.injective
  have h2 : IsPrimitiveRoot (e' (u : C)) k := hpu.map_of_injective e'.injective
  obtain ⟨i, hik, hic, hi⟩ := (h1.isPrimitiveRoot_iff).mp h2
  have hc : (i + k).Coprime k := by simpa using hic
  refine ⟨i + k, ?_, ?_⟩
  · obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).mp hkd
    rcases m with _ | m
    · simp only [pow_zero] at hm
      have hi0 : i = 0 := by omega
      simp [hm, hi0]
    · have hlk : l ∣ k := by rw [hm]; exact dvd_pow_self l (Nat.succ_ne_zero m)
      exact hc.coprime_dvd_right hlk
  · have hEu : e' (u : C) = e (u : C) ^ (i + k) := by
      rw [pow_add, ← hi, h1.pow_eq_one, mul_one]
    let E : Cˣ →* ℂˣ := Units.map (e : C →* ℂ)
    let E' : Cˣ →* ℂˣ := Units.map (e' : C →* ℂ)
    have hEu' : E' u = E u ^ (i + k) := by
      ext; simp [E, E', hEu]
    intro g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨ψ g, (mem_rootsOfUnity _ _).mpr (hψ g)⟩)
    have hj' : u ^ j = ψ g := by
      simpa [hu] using congrArg Subtype.val hj
    have key : E' (ψ g) = E (ψ g ^ (i + k)) := by
      rw [← hj', map_zpow, map_pow, map_zpow, hEu', ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm]
    simpa [E, E'] using congrArg Units.val key

end GlobalTheory
