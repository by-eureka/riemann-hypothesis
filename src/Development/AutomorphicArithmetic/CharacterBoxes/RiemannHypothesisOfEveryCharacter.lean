import Mathlib
import Formalism.GammaFactorNonvanishing.RhOfRight
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter

theorem UpperTheory.zeta_ne_zero_of_everyCharacter (h : UpperTheory.EveryCharacter) : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := fun s hs h1 => by
  have := h 1 1 s hs (Or.inr h1)
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

theorem UpperTheory.riemannHypothesis_of_everyCharacter (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right (UpperTheory.zeta_ne_zero_of_everyCharacter h)
