import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

def CO (L : AddSubgroup V) : Prop := IsCompact (L : Set V) ∧ IsOpen (L : Set V)

def ind (a : V) (L : AddSubgroup V) : V → ℂ := Set.indicator {x | x - a ∈ L} fun _ => (1 : ℂ)

omit [TopologicalSpace V] in
theorem ind_of_mem {a x : V} {L : AddSubgroup V} (h : x - a ∈ L) : ind a L x = 1 :=
  Set.indicator_of_mem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
theorem ind_of_not {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 :=
  Set.indicator_of_notMem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
theorem ind_congr {a b x y : V} {L L' : AddSubgroup V} (h : x - a ∈ L ↔ y - b ∈ L') : ind a L x = ind b L' y := by
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (h.1 hx)]
  · rw [ind_of_not hx, ind_of_not (mt h.2 hx)]

omit [TopologicalSpace V] in
theorem ind_add {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x :=
  ind_congr (by rw [add_sub_right_comm, L.add_mem_cancel_right hl])

section top

variable [IsTopologicalAddGroup V]

theorem CO.sup {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') :=
  ⟨by rw [AddSubgroup.add_normal]; exact h.1.add h'.1, AddSubgroup.isOpen_mono le_sup_left h.2⟩

theorem CO.inf {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') :=
  ⟨h.1.inter_right (L'.isClosed_of_isOpen h'), h.2.inter h'⟩

theorem isOpen_coset (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} :=
  h.preimage (continuous_id.sub continuous_const)

theorem lc_of_inv {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f :=
  (IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{y | y - x ∈ L}, isOpen_coset x h, by simp, fun y hy => by
    have := hf x _ hy
    rwa [add_sub_cancel] at this⟩

theorem sb_ind [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by
  refine ⟨lc_of_inv h.2 fun x l hl => ?_, HasCompactSupport.intro (K := (fun y => y + a) '' L)
    (h.1.image (continuous_id.add continuous_const)) fun x hx => ind_of_not fun h' => hx ⟨_, h', by simp⟩⟩
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (by rw [add_sub_right_comm]; exact L.add_mem hx hl)]
  · rw [ind_of_not hx, ind_of_not fun h' => hx (by
      rw [add_sub_right_comm] at h'; exact (L.add_mem_cancel_right hl).1 h')]

end top

omit [AddCommGroup V] in
theorem sb_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : SB (f + g) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

omit [AddCommGroup V] in
theorem sb_mul {f g : V → ℂ} (hf : IsLocallyConstant f) (hg : SB g) : SB fun x => f x * g x :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

omit [AddCommGroup V] in
theorem sb_smul (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := sb_mul (IsLocallyConstant.const c) hg

omit [AddCommGroup V] in
theorem sb_zero : SB (0 : V → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

omit [AddCommGroup V] in
theorem sb_sum {α : Type} (s : Finset α) {f : α → V → ℂ} (h : ∀ a ∈ s, SB (f a)) : SB (∑ a ∈ s, f a) :=
  Finset.sum_induction _ SB (fun _ _ => sb_add) sb_zero h

omit [AddCommGroup V] in
theorem sb_homeo {f : V → ℂ} (hf : SB f) (e : V ≃ₜ V) : SB (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem sb_span [IsTopologicalAddGroup V] {φ : V → ℂ} (hφ : SB φ) {L : AddSubgroup V} (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) : ∃ s : Finset V, φ = ∑ a ∈ s, φ a • ind a L :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.sb_span hφ hL hinv

variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}

theorem co_cpt (h : NADual V χ μ) {K : Set V} (hK : IsCompact K) : ∃ L : AddSubgroup V, CO L ∧ K ⊆ L := by
  obtain ⟨_, -, -, -, -, -, -, hbig, -⟩ := h
  refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, CO L ∧ s ⊆ L) ?_ ?_ ?_ ?_
  · obtain ⟨L, h1, h2, -⟩ := hbig 0
    exact ⟨L, ⟨h1, h2⟩, empty_subset _⟩
  · rintro s t hst ⟨L, h1, h2⟩
    exact ⟨L, h1, hst.trans h2⟩
  · rintro s t ⟨L, h1, h2⟩ ⟨L', h1', h2'⟩
    exact ⟨L ⊔ L', h1.sup h1', union_subset (h2.trans (SetLike.coe_subset_coe.2 le_sup_left))
      (h2'.trans (SetLike.coe_subset_coe.2 le_sup_right))⟩
  · intro x _
    obtain ⟨L, h1, h2, h3⟩ := hbig x
    exact ⟨L, mem_nhdsWithin_of_mem_nhds (h2.mem_nhds h3), L, ⟨h1, h2⟩, le_rfl⟩

theorem sb_level (h : NADual V χ μ) {φ : V → ℂ} (hφ : SB φ) :
    ∃ L L' : AddSubgroup V, CO L ∧ CO L' ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.sb_level h hφ

section chi

variable (h : NADual V χ μ)
include h

theorem chi_sym (x y : V) : χ x y = χ y x := h.2.2.2.2.2.2.2.2.2.1 x y
theorem chi_norm (x y : V) : ‖χ x y‖ = 1 := h.2.2.2.2.2.2.2.2.2.2.1 x y
theorem chi_add (x x' y : V) : χ (x + x') y = χ x y * χ x' y := h.2.2.2.2.2.2.2.2.2.2.2.1 x x' y
theorem chi_cont : Continuous fun p : V × V => χ p.1 p.2 := h.2.2.2.2.2.2.2.2.1
theorem chi_ne (x y : V) : χ x y ≠ 0 := norm_ne_zero_iff.1 (by rw [chi_norm h]; exact one_ne_zero)
theorem chi_add' (x y y' : V) : χ x (y + y') = χ x y * χ x y' := by
  rw [chi_sym h, chi_add h, chi_sym h y, chi_sym h y']
theorem chi_zero (y : V) : χ 0 y = 1 :=
  mul_left_cancel₀ (chi_ne h 0 y) (by rw [← chi_add h, add_zero, mul_one])
theorem chi_neg (x y : V) : χ (-x) y = conj (χ x y) := by
  refine mul_left_cancel₀ (chi_ne h x y) ?_
  rw [← chi_add h, add_neg_cancel, chi_zero h, Complex.mul_conj', chi_norm h]; simp

def perpG (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  zero_mem' := fun x _ => by rw [chi_sym h, chi_zero h]
  add_mem' := fun ha hb x hx => by rw [chi_add' h, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {y} hy x hx => by rw [chi_sym h, chi_neg h, chi_sym h, hy x hx, map_one]

theorem co_perp {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) :=
  ⟨(h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).1, (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.1⟩

theorem perp_perp {L : AddSubgroup V} (hL : CO L) (x : V) : x ∈ perpG h (perpG h L) ↔ x ∈ L :=
  ⟨fun hx => (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.1 hx, fun hx y hy => by rw [chi_sym h]; exact hy x hx⟩

theorem meas_perp {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by
  rw [← ENNReal.toReal_mul]
  exact (congrArg ENNReal.toReal (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.2).trans ENNReal.toReal_one

theorem chi_lc (a : V) : IsLocallyConstant fun y => χ a y := by
  have := h.1
  obtain ⟨L, hL, ha⟩ := co_cpt h (isCompact_singleton (x := a))
  exact lc_of_inv (co_perp h hL).2 fun x l hl => by rw [chi_add' h, hl a (ha rfl), mul_one]

theorem sb_int {φ : V → ℂ} (hφ : SB φ) : Integrable φ μ := by
  obtain ⟨_, _, _, _, _, _, -⟩ := h
  exact hφ.1.continuous.integrable_of_hasCompactSupport hφ.2

theorem sb_chi {φ : V → ℂ} (hφ : SB φ) (y : V) : SB fun x => φ x * χ x y := by
  simpa only [mul_comm, chi_sym h y] using sb_mul (chi_lc h y) hφ

theorem fou_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : fou χ μ (f + g) = fou χ μ f + fou χ μ g := by
  funext y
  simp only [fou, Pi.add_apply, add_mul]
  exact integral_add (sb_int h (sb_chi h hf y)) (sb_int h (sb_chi h hg y))

omit h in
theorem fou_smul (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

omit h [AddCommGroup V] [MeasurableSpace V] in
theorem map_sum_sb {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) {α : Type} (s : Finset α) (c : α → ℂ) {f : α → V → ℂ}
    (hf : ∀ a, SB (f a)) : T (∑ a ∈ s, c a • f a) = ∑ a ∈ s, c a • T (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hsm 0 0 sb_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (sb_smul _ (hf a)) (sb_sum _ fun b _ => sb_smul _ (hf b)),
      hsm _ _ (hf a), ih]

theorem fou_ind {L : AddSubgroup V} (hL : CO L) (a y : V) :
    fou χ μ (ind a L) y = ((μ L).toReal : ℂ) * χ a y * ind 0 (perpG h L) y :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.fou_ind h hL a y

theorem fou_sb {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.fou_sb h hφ

theorem planch {φ : V → ℂ} (hφ : SB φ) : ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.planch h hφ

theorem schur {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hch : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) : ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ :=
  PositivityTheory.PlacePermOperatorBicommutantSpan.schur h hadd hsm hch htr

end chi

end CompanionTheory.PlacePermOperatorBicommutantSpan
