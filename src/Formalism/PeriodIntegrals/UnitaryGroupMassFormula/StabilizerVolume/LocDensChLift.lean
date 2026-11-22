import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensChLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSAChar

noncomputable section

open NumberField Complex

namespace PI.VolStabS

namespace ChLiftW

theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  exact PI.VolStabW.ChLiftW.int_valued_zero ψ hψ hint a ha p

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  exact PI.VolStabW.ChLiftW.lift_normed χ hc hadd h0

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := fun a b => by
    apply e.injective
    rw [he]; simp
  have he0 : e.symm 0 = 0 := by
    have := hes 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous)
    (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])
  refine ⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩
  have := hℓ (e x)
  simpa using this

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  by_cases hv : v.IsReal
  · exact lift_homeo (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_add x y) χ hc hadd h0
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    exact lift_homeo (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').map_add x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW

open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x :=
  Finset.univ_sum_single (M := fun w : InfinitePlace F => w.Completion) x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := fun v =>
    lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul])
      (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓv hℓc hℓ using hloc
  let ℓ : InfiniteAdeleRing F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by
    show ∑ v, ℓv v (a v + b v) = _
    simp [map_add, Finset.sum_add_distrib])
  refine ⟨ℓ, ?_, fun x => ?_⟩
  · show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))
    exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · conv_lhs => rw [← sum_sgl x]
    rw [addChar_sum]
    show _ = exp (∑ v, ℓv v (x v))
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabS
