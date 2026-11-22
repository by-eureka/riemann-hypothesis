import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumPiProdEnnreal
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.VolBoxMajorant

theorem tsum_pi_prod_ennreal' : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  exact GlobalTheory.HL.tsum_pi_prod_ennreal

end GlobalTheory.VolBoxMajorant

namespace GlobalTheory.VolBoxMajorant

end GlobalTheory.VolBoxMajorant
