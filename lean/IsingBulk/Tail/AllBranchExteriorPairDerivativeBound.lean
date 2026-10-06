import IsingBulk.Tail.AllBranchExteriorTruncationIntegralLimit

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A majorant uniform in the artificial pair puncture bounds the actual
unpunctured pair-weighted derivative. The spatial majorant is an internal
interface: its integrability and bound must be proved by the calling estimate. -/
theorem allBranchExterior_pair_derivative_bound (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n M : ℕ,
      ∀ p q : Fin (n+1), p ≠ q → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      ∀ g : AngularSpace n → ℝ, Integrable g →
      (∀ h : ℝ, 0 < h → ∀ᵐ u,
        ‖sourceTermSum p q (-d.c₀*ε) d.thetaB (allBranchSingleTruncatedWeight M h p q w)
          (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j
          (radialParameter d.theta ε) u‖ ≤ g u) →
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (fun u => w u*allBranchExteriorPairWeight M p q u)) (radialParameter d.theta ε)‖ ≤ ∫ u, g u := by
  obtain ⟨r₁,hr₁,hnormal⟩ := allBranchExterior_single_truncated_normal_form d
  obtain ⟨r₂,hr₂,hlimit⟩ := allBranchExterior_single_truncation_derivatives_tendsto d
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro ε hε hεr n M p q hpq w hw hsupp j g hg hbound
  have hs₁ : tsupport w ⊆ microcoreCube (n+1) r₁ := by
    intro u hu
    exact (mem_microcoreCube r₁ u).mpr (fun i =>
      ((mem_microcoreCube _ u).mp (hsupp hu) i).trans (min_le_left _ _))
  have hs₂ : tsupport w ⊆ microcoreCube (n+1) r₂ := by
    intro u hu
    exact (mem_microcoreCube r₂ u).mpr (fun i =>
      ((mem_microcoreCube _ u).mp (hsupp hu) i).trans (min_le_right _ _))
  apply le_of_tendsto (hlimit ε hε (hεr.trans (min_le_right _ _)) n M p q hpq w hw hs₂ j).norm
  apply Eventually.of_forall
  intro k
  rw [hnormal ε hε (hεr.trans (min_le_left _ _)) n M p q hpq _ (allBranchTruncationScale_pos k) w hw hs₁ j,
    norm_mul]
  have hfac : ‖((n+1).factorial:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1)))
  exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans
    (norm_integral_le_of_norm_le hg (hbound _ (allBranchTruncationScale_pos k)))

end
end IsingBulk.Tail
