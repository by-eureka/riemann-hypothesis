import Mathlib

open scoped Classical

namespace GlobalTheory

theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b)
    have hsub : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.1 hp).1,
        by simpa using congrArg Prod.fst (Finset.mem_filter.1 hp).2⟩
    have hwt : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [← Finset.sum_image (f := w) (s := F) (g := Prod.fst) (fun p hp q hq hpq =>
        hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq (by
          simpa using (congrArg Prod.snd (Finset.mem_filter.1 hp).2).trans
            (congrArg Prod.snd (Finset.mem_filter.1 hq).2).symm))]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hw a)).trans (hsum b.1)
    have hfac : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p hp => by rw [← (Finset.mem_filter.1 hp).2]
    rw [hfac]
    exact mul_le_of_le_one_left (mul_nonneg (hom _) (hom _)) hwt
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _).symm
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
        rw [Finset.sum_product, Finset.sum_mul_sum]

end GlobalTheory
