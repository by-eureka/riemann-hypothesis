import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpFamOfDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem torsBasis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  exact GlobalTheory.ZM.NearBuild.Fibre.basis_pow hk hl y hy h z hz

variable {S : Scheme.{0}}

theorem torsBasis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact torsBasis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

theorem exists_polFam_of_grpFam : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)), N' ≠ 0 → Odd m → m ∣ N' → DenseP (objPrimes b Mat κ β v) → GrpFam b Mat κ β v m A L act Q → ∃ L' : LB A.left, PolFam b Mat κ β v A L' act Q := by
  intro hL hL2 o _ g N' J b Mat κ R _ _ _ β v m A _ L act Q hN0 hodd ⟨l, hl⟩ hD ⟨hab, hsm, hlb, hamp, hlab, hfib⟩
  have hun : IsUnit (m : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero, hl, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := hab.comm
  obtain ⟨L', l1, l2, l3, l4, l5⟩ := GlobalTheory.OddDescent.exists_descended hL hL2 R A g m L
    (fun i => (Q i ^ l : Out.baseOver (Sp R) ⟶ A)) hab hsm hodd hun hlb hamp
    (fun i => by
      have e : l * m = N' := by rw [mul_comm, ← hl]
      have : (Q i ^ l) ^ m = 1 := by rw [← pow_mul, e, hlab.2.1]
      exact this)
    (fun K _ _ x => torsBasis_pow_linComb hl hN0 _ _ hlab.2.1 (hlab.2.2 K x))
    (fun r hr => hD r fun q hq hqp => hr q (by
      obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
      exact ⟨K, inferInstance, inferInstance, x, t.pol, ψ, hx, hψ.1, hi⟩) hqp)
  refine ⟨L', hab, hsm, l1, l2, l3, l4, hlab, fun K _ _ x s t ht => ?_⟩
  obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
  exact ⟨ψ, hψ, l5 K x t.pol ψ hψ.1 hi⟩

end GlobalTheory.ZM.NearBuild
