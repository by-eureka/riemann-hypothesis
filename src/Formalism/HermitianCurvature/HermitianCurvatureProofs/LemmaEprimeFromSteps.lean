import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaLimit
import Formalism.HermitianCurvature.StatementLE

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem mulF_rpow_zero (B : Base) {A : Type} (u : Fn B A) : mulF B (fun x => x ^ (0:ℝ)) u = u := by
  funext ω a; simp [mulF]

theorem dS_zero (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h1 : mulF B (fun _ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h1]

theorem pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) (ω : B.Ω) :
    pr B wt v v ω = ((LE.sq B wt v ω : ℝ) : ℂ) := by
  simp only [pr, LE.sq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp

theorem int_pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) :
    ∫ ω, pr B wt v v ω ∂B.μ = ((∫ ω, LE.sq B wt v ω ∂B.μ : ℝ) : ℂ) := by
  simp_rw [pr_self]; exact integral_ofReal

theorem smoothLog_sc (c : Cut) (ε : ℝ) (m : ℕ) : SmoothLog (c.sc ε m) := by
  unfold SmoothLog Cut.sc
  exact (c.smooth.comp (Real.contDiff_exp.div_const ε)).pow m

theorem meas_ld (p : ℕ) (φ : ℝ → ℝ) (h : SmoothLog φ) : Measurable (ld p φ) := by
  unfold ld
  have : Continuous (iteratedDeriv p (fun u : ℝ => φ (Real.exp u))) :=
    h.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  exact this.measurable.comp Real.measurable_log

theorem measurable_apply_mulF_of_jetLocal (hLeib : Leibniz) (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (M : ℕ)
    (hJ : JetLocal B T u) (hP : PolyS B T u M) (hm : ∀ p a, Measurable fun ω => dS B T u p ω a)
    (φ : ℝ → ℝ) (hφ : SmoothLog φ) (a : A') : Measurable fun ω => T (mulF B φ u) ω a := by
  have := hLeib B A A' T u M hJ hP φ hφ
  simp_rw [this]
  refine Finset.measurable_sum _ fun p _ => ?_
  refine Measurable.div_const (Measurable.mul ?_ (hm p a)) _
  exact Complex.measurable_ofReal.comp ((meas_ld p φ hφ).comp B.G_meas)

theorem lemmaEprimeFromSteps : LemmaEprimeFromSteps := LEx2.lemmaEprimeFromSteps

theorem ld_one (q : ℕ) (x : ℝ) : ld q (fun _ => (1:ℝ)) x = if q = 0 then 1 else 0 := by
  unfold ld
  cases q with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

theorem epStep6 : EpStep6 := LEx2.epStep6

theorem epCoefInt : EpCoefInt := by
  intro h B X p N hpN hpos hMeas hNF q
  obtain ⟨n, v, C, h1, h2, h3⟩ := hNF q
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  refine h B (Fin n) _ v C p N hpN ?_ ?_ h1 h2 h3
  · unfold LE.sq
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (hmd a).mul ((hmS q a).norm.pow_const 2)
  · intro ω; unfold LE.sq
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)

open Polynomial in
theorem iterDeriv_poly (P : ℂ[X]) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => ((derivative^[p]) P).eval (s : ℂ) := by
  induction p generalizing P with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => (derivative P).eval (s : ℂ) := by
      funext s
      exact ((P.hasDerivAt (s : ℂ)).comp_ofReal).deriv
    rw [this, ih]
    simp [Function.iterate_succ]

open Polynomial in
noncomputable def mkP (m : ℕ) (c : ℕ → ℂ) : ℂ[X] := ∑ q ∈ range (m + 1), C (c q) * X ^ q

open Polynomial in
theorem mkP_eval (m : ℕ) (c : ℕ → ℂ) (z : ℂ) : (mkP m c).eval z = ∑ q ∈ range (m + 1), z ^ q * c q := by
  unfold mkP
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

open Polynomial in
theorem mkP_coeff (m : ℕ) (c : ℕ → ℂ) (k : ℕ) : (mkP m c).coeff k = if k < m + 1 then c k else 0 := by
  simp [mkP, finsetSum_coeff, coeff_C_mul, coeff_X_pow]

theorem ld_rpow (q : ℕ) (s x : ℝ) (hx : 0 < x) : ld q (fun y => y ^ s) x = s ^ q * x ^ s := by
  unfold ld
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this, iteratedDeriv_exp_const_mul]
  show s ^ q * Real.exp (s * Real.log x) = _
  rw [mul_comm s, Real.exp_mul, Real.exp_log hx]

theorem smoothLog_rpow (s : ℝ) : SmoothLog (fun y => y ^ s) := by
  unfold SmoothLog
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)

open Polynomial in
theorem leibniz : Leibniz := LEx2.leibniz

theorem thetaForm : ThetaForm := by
  intro ε σ hε v
  unfold th
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]; have := Real.exp_pos v; field_simp
  have h2 : 0 ≤ 1 + ε * Real.exp (-v) := by positivity
  rw [h1, Real.inv_rpow h2, Real.rpow_neg h2]

theorem thetaRange : ThetaRange := by
  intro ε σ x hε hσ hx
  unfold th
  have h0 : 0 < x / (x + ε) := by positivity
  have h1 : x / (x + ε) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact ⟨Real.rpow_pos_of_pos h0 σ, Real.rpow_le_one h0.le h1 hσ⟩

theorem pr_mulF (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (h u : Fn B A) (φ : ℝ → ℝ) (ω : B.Ω) :
    pr B wt h (mulF B φ u) ω = (φ (B.G ω) : ℂ) * pr B wt h u ω := by
  simp only [pr, mulF, Finset.mul_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem epStep5 : EpStep5 := LEx2.epStep5

theorem derived_energy_L2 : WeightedIntegrable := LEx2.derived_energy_L2

theorem thetaSmooth : ThetaSmooth := by
  intro ε σ hε
  unfold SmoothLog
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))
  · intro u; positivity

theorem thetaMono : ThetaMono := by
  intro σ ε ε' x hσ hε hεε hx
  unfold th
  have h1 : 0 < x + ε := by linarith
  have h2 : 0 < x + ε' := by linarith
  refine Real.rpow_le_rpow (div_nonneg hx.le h2.le) ?_ hσ
  exact div_le_div_of_nonneg_left hx.le h1 (by linarith)

theorem thetaBound : ThetaBound := by
  intro hC σ ε hσ hε p x hx
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  have h := hC σ ε hσ hε p (Real.log x)
  rwa [← thetaForm ε σ hε (Real.log x), Real.exp_log hx] at h

theorem iterDeriv_const' (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

theorem cutBound : CutBound := LEx2.cutBound

theorem sq_comb_le (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a)
    (D : ℕ → Fn B A') (M : ℕ) (k : ℕ → B.Ω → ℝ) (K : ℝ) (hK : ∀ p ∈ range (M+1), ∀ ω, |k p ω| ≤ K) (ω : B.Ω) :
    LE.sq B wt (fun ω a => ∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial) ω ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (D p) ω :=
  LEx2.sq_comb_le B wt hpos D M k K hK ω

theorem meas_sq (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (v : Fn B A')
    (h1 : ∀ a, Measurable fun ω => wt ω a) (h2 : ∀ a, Measurable fun ω => v ω a) : Measurable (LE.sq B wt v) := by
  unfold LE.sq
  exact Finset.measurable_sum _ fun a _ => (h1 a).mul ((h2 a).norm.pow_const 2)

theorem sq_nonneg' (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (v : Fn B A') (ω) :
    0 ≤ LE.sq B wt v ω := Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)

theorem limit_L2 : CutoffLimitInL2 := LEx2.limit_L2

theorem amgm (a b δ : ℝ) (hδ : 0 < δ) : a * b ≤ (a ^ 2 / δ + δ * b ^ 2) / 2 := by
  have h := sq_nonneg (a - δ * b)
  have : a ^ 2 / δ + δ * b ^ 2 - 2 * (a * b) = (a - δ * b) ^ 2 / δ := by field_simp; ring
  have h2 : 0 ≤ (a - δ * b) ^ 2 / δ := by positivity
  linarith

theorem pr_bound (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (δ : ℝ) (hδ : 0 < δ) (ω : B.Ω) : ‖pr B wt a b ω‖ ≤ (LE.sq B wt a ω / δ + δ * LE.sq B wt b ω) / 2 := by
  unfold pr LE.sq
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos ω i)]
  have := mul_le_mul_of_nonneg_left (amgm ‖a ω i‖ ‖b ω i‖ δ hδ) (hpos ω i)
  calc _ = wt ω i * (‖a ω i‖ * ‖b ω i‖) := by ring
    _ ≤ _ := this
    _ = _ := by ring

theorem meas_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i) :
    Measurable (pr B wt a b) := by
  unfold pr
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((Complex.measurable_ofReal.comp (h0 i)).mul (h1 i)).mul (Complex.continuous_conj.measurable.comp (h2 i))

theorem int_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) : Integrable (pr B wt a b) B.μ := by
  refine Integrable.mono' (((ha.div_const 1).add (hb.const_mul 1)).div_const 2)
    (meas_pr B wt a b h0 h1 h2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  exact pr_bound B wt hpos a b 1 one_pos ω

theorem norm_int_pr_le (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) (δ : ℝ) (hδ : 0 < δ) :
    ‖∫ ω, pr B wt a b ω ∂B.μ‖ ≤ ((∫ ω, LE.sq B wt a ω ∂B.μ) / δ + δ * ∫ ω, LE.sq B wt b ω ∂B.μ) / 2 := by
  refine (norm_integral_le_of_norm_le (((ha.div_const δ).add (hb.const_mul δ)).div_const 2)
    (Eventually.of_forall fun ω => pr_bound B wt hpos a b δ hδ ω)).trans (le_of_eq ?_)
  rw [integral_div, integral_add' (ha.div_const δ) (hb.const_mul δ), integral_div, integral_const_mul]

theorem pairLimit : PairLimit := LEx2.pairLimit

theorem limitB : LimitB := LEx2.limitB

theorem lemmaEprime : LemmaEprime :=
  lemmaEprimeFromSteps leibniz cutBound limit_L2 pairLimit epStep5 epStep6

theorem ld_zero' (φ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) : ld 0 φ x = φ x := by
  simp [ld, Real.exp_log hx]

theorem fatouStep : FatouStep := LEx2.fatouStep

noncomputable def Fk (k : ℕ) (s : ℝ) (t : ℝ) : ℝ := Real.exp (-(k:ℝ) * t) * (1 + Real.exp (-t)) ^ (-s)

theorem Fk_contDiff (k : ℕ) (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fk k s) := by
  unfold Fk
  refine (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul ?_
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)
  · intro u; positivity

theorem Fk_deriv (k : ℕ) (s : ℝ) : deriv (Fk k s) = fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t := by
  funext t
  have hp : 0 < 1 + Real.exp (-t) := by positivity
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(k:ℝ) * t)) (Real.exp (-(k:ℝ) * t) * (-(k:ℝ) * 1)) t :=
    ((hasDerivAt_id t).const_mul (-(k:ℝ))).exp
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
    ((hasDerivAt_id t).neg.exp).const_add 1
  have h3 := h2.rpow_const (p := -s) (Or.inl hp.ne')
  have h4 := h1.mul h3
  have h5 : deriv (Fk k s) t = _ := h4.deriv
  rw [h5]
  unfold Fk
  have e1 : Real.exp (-((k+1 : ℕ):ℝ) * t) = Real.exp (-(k:ℝ) * t) * Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have e2 : -s - 1 = -(s+1) := by ring
  rw [e1, e2]; ring

theorem Fk_lim (k : ℕ) (s : ℝ) : Tendsto (Fk k s) atTop (𝓝 (if k = 0 then 1 else 0)) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 : Tendsto (fun t : ℝ => (1 + Real.exp (-t)) ^ (-s)) atTop (𝓝 1) := by
    have := (h0.const_add 1).rpow_const (p := -s) (Or.inl (by norm_num))
    simpa using this
  unfold Fk
  split_ifs with hk
  · subst hk; simpa using h1
  · have h2 : Tendsto (fun t : ℝ => Real.exp (-(k:ℝ) * t)) atTop (𝓝 0) := by
      have hk' : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have : Tendsto (fun t : ℝ => (k:ℝ) * t) atTop atTop := tendsto_id.const_mul_atTop hk'
      have := h0.comp this
      simpa [Function.comp_def] using this
    simpa using h2.mul h1

theorem Fk_iter_lim (p : ℕ) : ∀ (k : ℕ) (s : ℝ),
    Tendsto (iteratedDeriv p (Fk k s)) atTop (𝓝 (if p = 0 ∧ k = 0 then 1 else 0)) :=
  LEx2.Fk_iter_lim p

theorem thetaLimit : ThetaLimit := LEx2.thetaLimit

end Formalism.FourierDecayAlt.P.LEx1
