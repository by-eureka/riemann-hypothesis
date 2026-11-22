import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.StarMapTraceOfPowEqOne
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.GLatHermW

open Matrix
open scoped ComplexOrder

theorem star_trace_of_pow_eq_one {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) :
    star A.trace = (A ^ (n - 1)).trace := by
  exact PI.Dv.GLPTr.star_trace_of_pow_eq_one A n hn hA

theorem star_map_trace_of_pow_eq_one {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (σ : K →+* ℂ) (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    star (σ (LinearMap.trace K W f)) = σ (LinearMap.trace K W (f ^ (n - 1))) := by
  classical
  let b := Module.finBasis K W
  obtain ⟨A, hAdef⟩ : ∃ A, LinearMap.toMatrix b b f = A := ⟨_, rfl⟩
  have hpow : ∀ k, LinearMap.toMatrix b b (f ^ k) = A ^ k := fun k => by
    rw [← LinearMap.toMatrix_pow, hAdef]
  have hmap : ∀ B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K,
      σ B.trace = (B.map σ).trace := fun B => AddMonoidHom.map_trace σ B
  have hmp : ∀ k, (A ^ k).map σ = (A.map σ) ^ k := fun k => RingHom.map_pow σ.mapMatrix A k
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b, hAdef, hpow, hmap,
    hmap, hmp]
  refine star_trace_of_pow_eq_one (A.map σ) n hn ?_
  rw [← hmp, ← hpow, hf, LinearMap.toMatrix_one]
  exact Matrix.map_one σ (map_zero σ) (map_one σ)

theorem star_map_trace_rep {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (σ : K →+* ℂ)
    (τ : Representation K G W) (g : G) :
    star (σ (LinearMap.trace K W (τ g))) = σ (LinearMap.trace K W (τ g⁻¹)) := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  rw [star_map_trace_of_pow_eq_one σ (τ g) (Fintype.card G) hn
    (by rw [← map_pow, pow_card_eq_one, map_one])]
  congr 2
  rw [← map_pow]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hn, pow_card_eq_one]

end PI.Dv.GLatHermW
