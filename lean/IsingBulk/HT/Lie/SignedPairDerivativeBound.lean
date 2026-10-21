import IsingBulk.HT.Lie.SignedSingleTruncation

namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Tail IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A majorant uniform in the artificial pair puncture bounds the actual
unpunctured pair-weighted derivative. The spatial majorant is an internal
interface: its integrability and bound must be proved by the calling estimate. -/
theorem signed_pair_derivative_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ, ∀ n M : ℕ,
      ∀ p q : Fin (n+1), p ≠ q → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      ∀ g : AngularSpace n → ℝ, Integrable g →
      (∀ h : ℝ, 0 < h → ∀ᵐ u,
        ‖signedSourceTermSum (Complex.exp (Complex.I*(α:ℂ))) p q (-d.c₀*ε) d.thetaB (allBranchSingleTruncatedWeight M h p q w)
          (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j
          (radialParameter d.theta ε) u‖ ≤ g u) →
      ‖iteratedDeriv j (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
        (fun u => w u*allBranchExteriorPairWeight M p q u)) (radialParameter d.theta ε)‖ ≤ ∫ u, g u := by
  obtain ⟨r₁,hr₁,hnormal⟩ := signed_single_truncated_normal_form d hcsmall
  obtain ⟨r₂,hr₂,hlimit⟩ := signed_single_truncation_derivatives_tendsto d hcsmall
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro ε hε hεr α n M p q hpq w hw hsupp j g hg hbound
  have hs₁ : tsupport w ⊆ microcoreCube (n+1) r₁ := by
    intro u hu
    exact (mem_microcoreCube r₁ u).mpr (fun i =>
      ((mem_microcoreCube _ u).mp (hsupp hu) i).trans (min_le_left _ _))
  have hs₂ : tsupport w ⊆ microcoreCube (n+1) r₂ := by
    intro u hu
    exact (mem_microcoreCube r₂ u).mpr (fun i =>
      ((mem_microcoreCube _ u).mp (hsupp hu) i).trans (min_le_right _ _))
  apply le_of_tendsto (hlimit ε hε (hεr.trans (min_le_right _ _)) α n M p q hpq w hw hs₂ j).norm
  apply Eventually.of_forall
  intro k
  rw [hnormal ε hε (hεr.trans (min_le_left _ _)) α n M p q hpq _ (allBranchTruncationScale_pos k) w hw hs₁ j,
    norm_mul]
  have hfac : ‖((n+1).factorial:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1)))
  exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans
    (norm_integral_le_of_norm_le hg (hbound _ (allBranchTruncationScale_pos k)))

end
end IsingBulk.HT.Lie
