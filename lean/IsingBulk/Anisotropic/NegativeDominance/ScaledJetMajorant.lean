import IsingBulk.Anisotropic.NegativeDominance.ScaledPeriodJets
import IsingBulk.Anisotropic.RegularEdges.TailSummability

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set MeasureTheory
open scoped BigOperators

/-- A summable, dimension-uniform majorant for actual derivatives of the
negative periods, not merely the integral of their formal integrand jets. -/
theorem scaledNegativeShiftedPeriod_summable_jet_majorant
    {lam b : ℝ} {B S A zeta : ℂ → ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im) (j : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∃ G : ℕ → ℝ, Summable G ∧
      ∀ ε : ℝ, 0<ε → ε<δ → Complex.I*(ε : ℂ)∈U → ∀ k : ℕ,
        ‖iteratedDeriv j (negativeShiftedPeriod b B (fun v => S v/A v) (2*j+3+k))
          (Complex.I*(ε : ℂ))‖≤G k := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,_,hbound⟩ :=
    negativeShiftedFullIntegrand_integrated_jets hb hB0 hBa (hSa.div hAa0 hA0) (div_ne_zero hSzero hA0) j
  let G : ℕ → ℝ := fun k =>
    D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1 : ℕ):ℝ)^j
  have hs := particleEdgeMajorant_polynomial_summable hr hr1 hC hM j
  have hi : Function.Injective (fun k : ℕ => 2*j+3+k+1) := by
    intro a b h
    dsimp only at h
    omega
  have hg : Summable G := by
    have hh := (hs.comp_injective hi).mul_left D
    convert hh using 1
    funext k
    dsimp [G,Function.comp_def]
    ring
  refine ⟨δ,hδ,G,hg,?_⟩
  intro ε hε heδ hεU k
  rw [scaledNegativeShiftedPeriod_iteratedDeriv (2*j+3+k) j hU ha hAa hz hS0 hB hS he hup hBi hεU,
    norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one]
  have hf : ‖(((2*j+3+k+1).factorial : ℂ)⁻¹)‖≤1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (2*j+3+k+1)))
  exact (mul_le_of_le_one_left (norm_nonneg _) hf).trans (hbound ε hε heδ k)

end
end IsingBulk.Anisotropic.NegativeDominance
