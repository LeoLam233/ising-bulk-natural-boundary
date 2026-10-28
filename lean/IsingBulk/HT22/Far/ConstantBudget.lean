import IsingBulk.HT22.Tail.FarScalar

/-! Fixed far-diameter floors absorb the true total mixed-order losses.
No shell cutoff is differentiated and no particle-dependent floor is used. -/
namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22

theorem reciprocal_scale_far_bound {T M r d₀ : ℝ}
    (hT : 0<T) (hTM : T≤M) (hd : 0<d₀) (hr : d₀≤r) :
    (r/Real.sqrt T)⁻¹≤max 1 (Real.sqrt M/d₀) := by
  have hr0 : 0<r := hd.trans_le hr
  have hsr : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  calc
    _ = Real.sqrt T/r := by rw [inv_div]
    _ ≤ Real.sqrt M/d₀ := div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hTM) hd hr
    _ ≤ _ := le_max_right _ _

theorem far_field_total_jet_bound {A T M r d₀ : ℝ} (hA : 0≤A)
    (hT : 0<T) (hTM : T≤M) (hd : 0<d₀) (hr : d₀≤r)
    (N L j m : ℕ) (hm : m≤j) :
    A*(N:ℝ)^L/(r/Real.sqrt T)^(1+m)≤
      (A*(max 1 (Real.sqrt M/d₀))^(j+1))*(N:ℝ)^L := by
  let E := max 1 (Real.sqrt M/d₀)
  have hE : 1≤E := le_max_left _ _
  have hscale : 0<r/Real.sqrt T := div_pos (hd.trans_le hr) (Real.sqrt_pos.mpr hT)
  have hp : ((r/Real.sqrt T)⁻¹)^(1+m)≤E^(j+1) :=
    (pow_le_pow_left₀ (by positivity) (reciprocal_scale_far_bound hT hTM hd hr) _).trans
      (pow_le_pow_right₀ hE (by omega))
  calc
    _ = (A*(N:ℝ)^L)*((r/Real.sqrt T)⁻¹)^(1+m) := by rw [div_eq_mul_inv,inv_pow]
    _ ≤ (A*(N:ℝ)^L)*E^(j+1) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem farOrderEnvelope_absorb_factor {A B : ℝ} (hA : 0≤A) (hB : 1≤B)
    {N : ℕ} (hN : 0<N) (L : ℕ) :
    B*farOrderEnvelope A L N≤farOrderEnvelope (B*A) L N := by
  have hBn : B≤B^N := by
    simpa only [pow_one] using pow_le_pow_right₀ hB hN
  unfold farOrderEnvelope shellOrderEnvelope
  calc
    _ ≤ B^N*((N:ℝ)^L*(A/Real.sqrt N)^N) :=
      mul_le_mul_of_nonneg_right hBn (by positivity)
    _ = _ := by rw [mul_div_assoc,mul_pow];ring

end
end IsingBulk.HT22.Far
