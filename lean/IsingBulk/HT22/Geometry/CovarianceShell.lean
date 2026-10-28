import IsingBulk.HT22.Geometry.CovarianceSource

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators
open Set IsingBulk.Preferred22

theorem angular_pair_square_le_double_sum {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) :
    (θ i-θ j)^2 ≤ ∑ a,∑ b,(θ a-θ b)^2 := by
  calc
    _ ≤ ∑ b,(θ i-θ b)^2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a,∑ b,(θ a-θ b)^2 := Finset.single_le_sum
      (f := fun a : Fin N => ∑ b : Fin N,(θ a-θ b)^2)
      (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (θ a-θ b))) (Finset.mem_univ i)

/-- The shell form of the protected covariance, with a named actual extreme
pair. The factor sqrt(T) Δ² is precisely r²/sqrt(T). -/
theorem actual_mixed_covariance_shell (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c ε₀ τ₀ δB : ℝ, 0<c ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r →
      ∀ θ : Fin N → ℝ, (∀ a, θ a∈Icc (-d.b-δB) B.delta) →
      (∀ a, μ-2*r≤θ a+d.b ∧ θ a+d.b≤μ+2*r) → ∀ i j : Fin N,
      (∀ a, θ i≤θ a ∧ θ a≤θ j) → r≤θ j-θ i →
      c*r^2/Real.sqrt (|μ|+r+ε) ≤
        (covarianceDirection*sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε)
          (actualRegularCoordinates d B ε τ θ)).re ∧
      c*r^2/Real.sqrt (|μ|+r+ε) ≤
        ‖sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε) (actualRegularCoordinates d B ε τ θ)‖ ∧
      sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε) (actualRegularCoordinates d B ε τ θ)≠0 := by
  obtain ⟨c,e,t,δ,hc,he,ht,hδ,hδB,hbound⟩ := actual_mixed_covariance_lower d B
  refine ⟨c/2,e,t,δ,by positivity,he,ht,hδ,hδB,?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr θ hθ hwin i j hext hdiam
  have h := hbound N hN ε τ μ r (θ i) (θ j) hε hεr hτ hτr hr
    (hθ i).1 (hθ j).2 (hwin i).1 (hwin j).2 θ hext
  have hT : 0 < |μ|+r+ε := by positivity
  have hs : 0<Real.sqrt (|μ|+r+ε) := Real.sqrt_pos.mpr hT
  have hsq : r^2≤∑ a,∑ b,(θ a-θ b)^2 :=
    (pow_le_pow_left₀ hr.le hdiam 2).trans (angular_pair_square_le_double_sum θ j i)
  have hfactor : 0≤c/Real.sqrt (|μ|+r+ε) := by positivity
  have hp : (c/2)*r^2/Real.sqrt (|μ|+r+ε) ≤
      (covarianceDirection*sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε)
        (actualRegularCoordinates d B ε τ θ)).re := by
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by norm_num : (0:ℝ)≤2)) hfactor
    calc
      _ = (c/Real.sqrt (|μ|+r+ε))*(r^2/2) := by ring
      _ ≤ _ := hh
      _ ≤ _ := h
  have hn := Complex.re_le_norm (covarianceDirection*sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε)
    (actualRegularCoordinates d B ε τ θ))
  rw [norm_mul,covarianceDirection_norm,one_mul] at hn
  refine ⟨hp,hp.trans hn,?_⟩
  intro hz
  rw [hz,mul_zero,Complex.zero_re] at hp
  have hpos : 0<(c/2)*r^2/Real.sqrt (|μ|+r+ε) := by positivity
  linarith

end
end IsingBulk.HT22.Geometry
