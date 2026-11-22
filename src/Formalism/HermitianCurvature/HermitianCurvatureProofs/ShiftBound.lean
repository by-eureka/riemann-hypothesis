import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepClaimFromStepsFull
import Formalism.HermitianCurvature.StatementLE

namespace Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

theorem mulF_one' (B : Base) {A : Type} (u : Fn B A) : mulF B (fun x => x ^ (0:ℝ)) u = u := by
  funext ω a; simp [mulF]

theorem dS_zero (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h]

theorem ds_zero {B : Base} (S : Step B) (Y : ℝ) : S.ds Y 0 = S.gX Y := dS_zero B _ _

theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) :=
  Formalism.FourierDecayAlt.P.LEx1.meas_iterDeriv F hsm hm

theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

theorem stepClaimFromSteps (hDs : DsMeas) : StepClaimFromSteps :=
  Formalism.FourierDecayAlt.P.LEx1.stepClaimFromSteps hDs

theorem en_le_esup {B : Base} (S : Step B) (ε σ : ℝ) (hb : BddAbove (S.Eset ε σ)) (hP : S.PReg) (Y : ℝ) (hY : Y ∈ S.J) :
    S.En ε σ Y ≤ S.Esup ε σ * |S.P Y| := by
  have h1 : S.En ε σ Y / |S.P Y| ≤ S.Esup ε σ := le_csSup hb ⟨Y, hY, rfl⟩
  have hpos : 0 < |S.P Y| := abs_pos.mpr (hP.2 Y hY)
  rwa [div_le_iff₀ hpos] at h1

theorem termBound : TermBound :=
  Formalism.FourierDecayAlt.P.LEx1.termBound

theorem absorb : Absorb := by
  intro B S σ ε A hL hb h
  have hne : (S.Eset ε σ).Nonempty := ⟨_, S.a, ⟨le_refl _, by linarith⟩, rfl⟩
  have : S.Esup ε σ ≤ A + S.Esup ε σ / 2 := by
    apply csSup_le hne
    rintro _ ⟨Y, hY, rfl⟩
    exact h Y hY
  linarith

theorem uniformBound : UniformBound :=
  Formalism.FourierDecayAlt.P.LEx1.uniformBound

theorem geom_sum_mul_pred (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) (R : ℕ) : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x - 2 * x ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 ≤ x ^ (R + 1) := by positivity
    have h2 : x ^ (R + 1 + 1) = x ^ (R + 1) * x := pow_succ _ _
    nlinarith

theorem geomSum : GeomSum :=
  Formalism.FourierDecayAlt.P.LEx1.geomSum

theorem termZero : TermZero := by
  intro B S ε σ Y
  unfold Step.term Step.En
  rw [ds_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  rw [← integral_complex_ofReal]
  congr 1
  funext ω
  have hG := B.G_pos ω
  simp only [ld, iteratedDeriv_zero, Real.exp_log hG, pr, LE.sq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sum_Icc_one (f : ℕ → ℝ) (R : ℕ) : ∑ p ∈ Icc 1 R, f p = ∑ i ∈ range R, f (i + 1) := by
  induction R with
  | zero => simp
  | succ R ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem th_nonneg (B : Base) (ε σ : ℝ) (hε : 0 < ε) (ω : B.Ω) : 0 ≤ th ε σ (B.G ω) :=
  Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _

theorem energyStep : EnergyStep :=
  Formalism.FourierDecayAlt.P.LEx1.energyStep

theorem eFinite : EFinite := by
  intro B S σ ε hε hP hI
  have hc : ContinuousOn (fun Y => S.En ε σ Y / |S.P Y|) S.J :=
    (hI ε hε).2.div (hP.1.abs) (fun Y hY => abs_ne_zero.mpr (hP.2 Y hY))
  exact (isCompact_Icc.image_of_continuousOn hc).bddAbove

theorem norm_add_sq_le (x y : ℂ) (c : ℝ) (hc : 0 ≤ c) : c * ‖x + y‖ ^ 2 ≤ c * (1 + c) * ‖x‖ ^ 2 + (1 + c) * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h1
  have h3 : 0 ≤ (c * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  have h4 : c * ‖x + y‖ ^ 2 ≤ c * (‖x‖ + ‖y‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hc
  nlinarith

theorem shift_pt {B : Base} (S : Step B) (CR Cd : ℝ) (hCR : 0 ≤ CR) (hCd : 0 ≤ Cd) (hW : S.WPos) (h5 : S.ShiftFormula)
    (hRes : S.Residues CR) (hWR : S.WeightRatio Cd) (Y s : ℝ) (hY : Y ∈ S.J) (hYs : Y + s ∈ S.J) (ω : B.Ω) :
    LE.sq B (S.d Y) (S.gs Y s) ω ≤ (1 + CR) ^ 2 * (Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) :=
  Formalism.FourierDecayAlt.P.LEx1.shift_pt S CR Cd hCR hCd hW h5 hRes hWR Y s hY hYs ω

theorem gs_zero {B : Base} (S : Step B) (Y : ℝ) : S.gs Y 0 = S.gX Y := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) S.X = S.X := by funext ω a; simp [mulF]
  simp [Step.gs, Step.gX, conjS, h]

theorem shiftBound : ShiftBound :=
  Formalism.FourierDecayAlt.P.LEx1.shiftBound

theorem stepClaimFromSteps_full : StepClaimFromSteps := stepClaimFromSteps dsMeas

end
end Formalism.FourierDecayAlt.P.LEx2.A
