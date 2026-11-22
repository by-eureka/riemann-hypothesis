import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_isFundamentalDomain_of_relIndex_ne_zero :
    ∀ (G X : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
      (μ : Measure X) [SMulInvariantMeasure G X μ] (Γ₀ Γ : Subgroup G) [Countable Γ] (s : Set X),
      Γ₀ ≤ Γ → Γ₀.relIndex Γ ≠ 0 → IsFundamentalDomain Γ s μ →
      ∃ t : Set X, IsFundamentalDomain Γ₀ t μ ∧ μ t = (Γ₀.relIndex Γ : ℝ≥0∞) * μ s := by
  intro G X _ _ _ _ μ _ Γ₀ Γ _ s hle hidx hs
  classical
  set H : Subgroup Γ := Γ₀.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hidx⟩
  let _ : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let ρ : Γ ⧸ H → Γ := fun q => q.out
  have hout : ∀ q : Γ ⧸ H, ((ρ q : Γ) : Γ ⧸ H) = q := fun q => QuotientGroup.out_eq' q
  have hρ : ∀ γ : Γ, (ρ (γ : Γ ⧸ H))⁻¹ * γ ∈ H := fun γ => QuotientGroup.eq.mp (hout _)
  let ι : Γ₀ → Γ := fun g => ⟨g, hle g.2⟩
  have key : ∀ (g : Γ₀) (γ : Γ), g • (γ • s) = (ι g * γ) • s := fun g γ => by rw [mul_smul]; rfl
  let t : Set X := ⋃ q : Γ ⧸ H, (ρ q)⁻¹ • s
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun q : Γ ⧸ H => (ρ q)⁻¹ • s) := by
    intro q q' hqq'
    apply hs.aedisjoint
    intro heq
    exact hqq' (by rw [← hout q, ← hout q', inv_injective (G := Γ) heq])
  refine ⟨t, ⟨NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_smul _, ?_, ?_⟩, ?_⟩
  · filter_upwards [hs.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    refine ⟨⟨(((ρ (γ : Γ ⧸ H))⁻¹ * γ : Γ) : G), Subgroup.mem_subgroupOf.mp (hρ γ)⟩, ?_⟩
    refine Set.mem_iUnion.2 ⟨(γ : Γ ⧸ H), ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    simpa [Subgroup.smul_def, smul_smul] using hγ
  · intro g g' hgg'
    show AEDisjoint μ (g • t) (g' • t)
    simp only [t, Set.smul_set_iUnion]
    rw [AEDisjoint.iUnion_left_iff]
    intro q
    rw [AEDisjoint.iUnion_right_iff]
    intro q'
    rw [key, key]
    apply hs.aedisjoint
    intro heq
    apply hgg'
    have h1 : (ι g')⁻¹ * ι g = (ρ q')⁻¹ * ρ q := by
      simpa [mul_assoc] using congrArg (fun z => (ι g')⁻¹ * z * ρ q) heq
    have h2 : (ι g')⁻¹ * ι g ∈ H :=
      Subgroup.mem_subgroupOf.mpr (by simpa [ι] using Γ₀.mul_mem (Γ₀.inv_mem g'.2) g.2)
    have h3 : q' = q := by
      rw [← hout q', ← hout q]
      exact QuotientGroup.eq.mpr (h1 ▸ h2)
    subst h3
    exact Subtype.ext (congrArg (fun γ : Γ => (γ : G)) (mul_right_cancel heq))
  · rw [measure_iUnion₀ hdisj (fun q => hs.nullMeasurableSet_smul _)]
    have hm : ∀ q, μ ((ρ q)⁻¹ • s) = μ s := fun q => measure_smul μ _ _
    simp only [hm, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cmp
