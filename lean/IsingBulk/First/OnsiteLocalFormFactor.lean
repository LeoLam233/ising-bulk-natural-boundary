import IsingBulk.First.OnsiteLocalBound

/-! Source-facing local onsite estimate, with active factors constructed
internally and the exact original factorial normalization retained. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped ContDiff

theorem onsite_radial_local_formFactor_bound {N : ℕ} (hN : 0 < N)
    (S : ℝ) (hlevel : 0 < S ∧ S < 2)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) =
      (S : ℂ))
    (u₀ : DoubleAngularVector N) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ w : DoubleAngularVector N → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => liftedLocalizedOnsiteFormFactor N (sourceRadialPair θ ε).1 s w))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  classical
  let J : Finset (SingularFactorIndex N) := Finset.univ.filter
    (fun f => isOnsiteFactor f ∧ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2) S f)
  have hJ (f) : f ∈ J ↔ isOnsiteFactor f ∧ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)
      S f := by simp [J]
  obtain ⟨γ,ε₀,hγ,he,hbound⟩ := onsite_radial_local_integral_bound hN S hlevel θ hθ hS u₀ J hJ
  refine ⟨γ,ε₀,hγ,he,?_⟩
  intro w hw hsupp j
  obtain ⟨C,hC,hb⟩ := hbound w hw hsupp j
  refine ⟨‖(N.factorial : ℂ)⁻¹‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro ε hε heps
  rw [← iteratedDeriv_eq_iterate]
  unfold liftedLocalizedOnsiteFormFactor
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb ε hε heps) (norm_nonneg _)

end
end IsingBulk.First
