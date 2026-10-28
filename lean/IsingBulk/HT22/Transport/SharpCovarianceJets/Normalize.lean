import IsingBulk.HT22.Transport.SharpCovarianceJets.ActualScale
namespace IsingBulk.HT22.SharpCovarianceJets
noncomputable section
open IsingBulk.Preferred22

theorem scaled_positive_envelope_le (A X H Δ K : ℝ) (q m : ℕ)
    (hA : 0≤A) (hX : 0≤X) (hH : 0≤H) (hΔ : 0<Δ) (hK : 1≤K) :
    A*X*(K*H)*(K*Δ)^q/(K*Δ)^m≤(A*K^(q+1))*X*H*Δ^q/Δ^m := by
  have hKn : K≠0 := ne_of_gt (zero_lt_one.trans_le hK)
  calc
    _ = ((A*K^(q+1))*X*H*Δ^q/Δ^m)/K^m := by
      simp only [mul_pow,pow_succ]
      field_simp
    _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hK)

theorem scaled_inverse_envelope_le (A X H Δ K : ℝ) (m : ℕ)
    (hA : 0≤A) (hX : 0≤X) (hH : 0<H) (hΔ : 0<Δ) (hK : 1≤K) :
    A*X/((K*H)*(K*Δ)^(m+2))≤A*X/(H*Δ^(m+2)) := by
  have hKK : 0<K := zero_lt_one.trans_le hK
  apply div_le_div_of_nonneg_left (mul_nonneg hA hX) (by positivity)
  exact mul_le_mul (le_mul_of_one_le_left hH.le hK)
    (pow_le_pow_left₀ hΔ.le (le_mul_of_one_le_left hΔ.le hK) _) (by positivity) (by positivity)

end
end IsingBulk.HT22.SharpCovarianceJets
