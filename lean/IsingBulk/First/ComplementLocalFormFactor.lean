import IsingBulk.First.ComplementLocalBound

/-! Source-facing local complement estimate, with active factors constructed
internally and the exact original factorial normalization retained. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped ContDiff

theorem source_radial_local_formFactor_bound {N : ℕ} (hN : 0 < N) (S : ℝ)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) =
      (S : ℂ))
    (u₀ : DoubleAngularVector N)
    (hsep : ActiveSourceSeparated (angleTuple 1 u₀.1) (angleTuple 1 u₀.2) S) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ w : DoubleAngularVector N → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => liftedLocalizedDoubleFormFactor N (sourceRadialPair θ ε).1 s w))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  classical
  let J : Finset (SingularFactorIndex N) := Finset.univ.filter
    (singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2) (S))
  have hJ (f) : f ∈ J ↔ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)
      (S) f := by simp [J]
  obtain ⟨γ,ε₀,hγ,he,hbound⟩ := source_radial_local_integral_bound hN S θ hθ hS u₀ hsep J hJ
  refine ⟨γ,ε₀,hγ,he,?_⟩
  intro w hw hsupp j
  obtain ⟨C,hC,hb⟩ := hbound w hw hsupp j
  refine ⟨‖(N.factorial : ℂ)⁻¹‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro ε hε heps
  rw [← iteratedDeriv_eq_iterate]
  unfold liftedLocalizedDoubleFormFactor
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb ε hε heps) (norm_nonneg _)

/-- Compatibility wrapper for the frozen selected first-order charts. -/
theorem selected_radial_local_formFactor_bound {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b : ℝ) : ℂ))
    (u₀ : DoubleAngularVector (2*p))
    (hgood : ¬ selectedBadConfiguration a b (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ w : DoubleAngularVector (2*p) → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => liftedLocalizedDoubleFormFactor (2*p) (sourceRadialPair θ ε).1 s w))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  exact source_radial_local_formFactor_bound (Nat.mul_pos (by omega) hp.pos) (2*PrimeFamily.cosineAverage p a b) θ hθ hS u₀ (selected_active_separating_functional hp hp11 ha hb
      (fun _ => anglePoint_norm (by norm_num) _)
      (fun _ => anglePoint_norm (by norm_num) _) hgood)


end
end IsingBulk.First
