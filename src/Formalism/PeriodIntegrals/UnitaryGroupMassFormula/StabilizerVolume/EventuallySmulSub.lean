import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.EventuallySmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasureEqOfCos

noncomputable section

namespace PI.VolStabS

open Topology Filter Set

section Abs

variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribMulAction.toAddMonoidHom W t)

omit [TopologicalSpace K] in
theorem mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp [smulSub, AddSubgroup.mem_map]

theorem coe_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) := by
  ext z
  simp [smulSub, AddSubgroup.coe_map]

theorem isOpen_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (ht : t ≠ 0) (P : AddSubgroup W) (hP : IsOpen (P : Set W)) :
    IsOpen (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact (Homeomorph.smulOfNeZero t ht).isOpenMap _ hP

theorem isCompact_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (P : AddSubgroup W) (hP : IsCompact (P : Set W)) :
    IsCompact (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact hP.image (continuous_const_smul t)

theorem eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hP : ∀ p ∈ S, ∀ᶠ q : K × W in 𝓝 ((0 : K), p), q.1 • q.2 ∈ N := by
    intro p _
    have h : Tendsto (fun q : K × W => q.1 • q.2) (𝓝 ((0 : K), p)) (𝓝 (0 : W)) := by
      simpa using (continuous_smul : Continuous fun q : K × W => q.1 • q.2).tendsto ((0 : K), p)
    exact h hN
  have hev := hS.eventually_forall_of_forall_eventually (P := fun (t : K) (p : W) => t • p ∈ N) hP
  exact (hs.eventually hev).exists

variable [T2Space X]

theorem reach_of_approx (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  have hπkL : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ, mul_smul]
      exact ih _ (hπL w hw)
  have hstep : ∀ k : ℕ, ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub (π ^ k) P := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact ⟨0, L.zero_mem, (mem_smulSub _ _ _).2 ⟨p, hp, by simp⟩⟩
    | succ k ih =>
      intro p hp
      obtain ⟨l, hl, hpl⟩ := ih p hp
      obtain ⟨p', hp', e1⟩ := (mem_smulSub _ _ _).1 hpl
      obtain ⟨l', hl', hpl'⟩ := hbase p' hp'
      obtain ⟨p'', hp'', e2⟩ := (mem_smulSub _ _ _).1 hpl'
      refine ⟨l + π ^ k • l', L.add_mem hl (hπkL k l' hl'), (mem_smulSub _ _ _).2 ⟨p'', hp'', ?_⟩⟩
      rw [map_add, hDs, pow_succ, mul_smul, e2, smul_sub, e1]
      abel
  set S : Set X := D '' (L : Set V) with hS
  have hSc : IsClosed S := (hLc.image hDc).isClosed
  have hb : ∀ N ∈ 𝓝 (0 : X), ∃ k, (smulSub (π ^ k) P : Set X) ⊆ N := by
    intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (P : Set X) hPc (fun k => π ^ k) hπ N hN
    refine ⟨k, ?_⟩
    rw [coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp
  intro p hp
  have hmem : p ∈ ⋂ k, thick S (smulSub (π ^ k) P) := by
    refine mem_iInter.2 fun k => ?_
    obtain ⟨l, hl, hpl⟩ := hstep k p hp
    exact ⟨D l, ⟨l, hl, rfl⟩, hpl⟩
  rw [iInter_thick S hSc (fun k => smulSub (π ^ k) P) hb] at hmem
  obtain ⟨l, hl, e⟩ := hmem
  exact ⟨l, hl, e⟩

theorem filt_abstract [ContinuousMul K] (π : K) (hπ0 : π ≠ 0) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))
    (hπL : ∀ w ∈ L, π • w ∈ L)
    (β : V → V → X) (hβc : Continuous fun q : V × V => β q.1 q.2)
    (hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (hβ2 : ∀ u w w', β u (w + w') = β u w + β u w')
    (hβs : ∀ (t : K) u w, β u (t • w) = t • β u w)
    (G : V → X) (hG : ∀ u W, G (u + W) = G u + β u W + G W)
    (hGs : ∀ (t : K) w, G (t • w) = t • t • G w)
    (x : V) (hxo : IsOpen (β x '' (L : Set V)))
    (hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N2 ∈ 𝓝 (0 : V), ∀ c : K, (∀ w ∈ L, c • w ∈ N2) →
      ∀ w ∈ L, c • G w ∈ U) :
    ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ0 : AddSubgroup V,
      (∃ c : K, c ≠ 0 ∧ Λ0 = L.map (DistribMulAction.toAddMonoidHom V c)) → (Λ0 : Set V) ⊆ N →
      ∃ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (D : V →+ X),
        Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set V)) ∧ (∀ n, IsCompact (Λ n : Set V)) ∧ Antitone Λ ∧
        (∀ n, IsOpen (H n : Set X)) ∧ (∀ n, IsCompact (H n : Set X)) ∧
        (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') ∧ (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1) := by
  exact PI.VolStabW.filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall

end Abs

end PI.VolStabS
