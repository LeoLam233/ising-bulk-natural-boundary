import IsingBulk.Anisotropic.NegativeCycles.ActualCentralTransport
import IsingBulk.Anisotropic.NegativeCycles.CenteredInnerVolume
import IsingBulk.Anisotropic.NegativeDominance.InnerGaussian
import IsingBulk.Anisotropic.NegativeDominance.CycleEntropy

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles

/-- Cancellation of N in the annular residue prefactor preserves the sharp
coefficient one on the Taylor-order logarithm. -/
theorem annularErrorEnvelope_factor (M c L a : ℝ) (hc : 0<c) (ha : 0<a) (m j : ℕ) :
    annularErrorEnvelope M c L a m j=
      (16/(c*a))*(2*L)^(2*m)*remainderGaussianEnvelope M m*((2*m+1:ℕ)/(a/8))^j := by
  have hn : ((2*m+1:ℕ):ℝ)≠0 := by positivity
  have he : (8*(2*m+1:ℕ):ℝ)/a=((2*m+1:ℕ):ℝ)/(a/8) := by ring
  have hcst : (2/(c*(2*m+1:ℕ)))*(8*(2*m+1:ℕ)/a)=16/(c*a) := by
    field_simp
    norm_num
  unfold annularErrorEnvelope
  rw [pow_succ]
  calc
    _ = ((2/(c*(2*m+1:ℕ)))*(8*(2*m+1:ℕ)/a))*(2*L)^(2*m)*
        remainderGaussianEnvelope M m*(8*(2*m+1:ℕ)/a)^j := by
      unfold remainderGaussianEnvelope
      ring
    _ = _ := by rw [hcst,he]

/-- The actual real-annular envelope has a genuine Gaussian particle factor. -/
theorem annularErrorEnvelope_gaussian_bound (M c L a : ℝ)
    (hM : 1≤M) (hc : 0<c) (hL : 0<L) (ha : 0<a) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      annularErrorEnvelope M c L a m j≤
        Real.exp (-g*(2*m+1:ℕ)^2+((j:ℝ)+1)*Real.log (2*m+1:ℕ)+D*((j:ℝ)+1)) := by
  obtain ⟨g,D,hg,hD,hb⟩ := inner_cauchy_gaussian_bound
    hM (show 1≤1+2*L by linarith) (show 0<16/(c*a) by positivity) (show 0<a/8 by positivity)
  refine ⟨g,D,hg,hD,fun m j=>?_⟩
  apply le_trans _ (hb m j)
  rw [annularErrorEnvelope_factor M c L a hc ha]
  have hG : 0≤remainderGaussianEnvelope M m := by
    have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
    unfold remainderGaussianEnvelope
    positivity
  gcongr
  linarith

/-- The literal moving-domain volume is bounded before the particle index;
the SAME-R0 remainder therefore has a common Gaussian Cauchy envelope. -/
theorem centeredRemainderEnvelope_gaussian_bound (K M c sigma : ℝ)
    (hK : 0<K) (hM : 1≤M) (hc : 0<c) (hsigma : 0<sigma) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ, ∀d s : ℝ,s≤sigma →
      centeredRemainderEnvelope K M c m j d s≤
        Real.exp (-g*(2*m+1:ℕ)^2+((j:ℝ)+1)*Real.log (2*m+1:ℕ)+D*((j:ℝ)+1)) := by
  obtain ⟨g,D,hg,hD,hb⟩ := inner_cauchy_gaussian_bound
    hM (show 1≤2*(sigma+1) by linarith) hK (show 0<c/2 by positivity)
  refine ⟨g,D,hg,hD,fun m j d s hs=>?_⟩
  apply le_trans _ (hb m j)
  have hv := centeredInnerSet_volume_bound (2*m) d s (sigma+1)
    (by positivity) (show s≤(sigma+1)^2 by nlinarith)
  have he : ((c/(2*m+1:ℕ))/2)⁻¹=((2*m+1:ℕ):ℝ)/(c/2) := by
    field_simp
  have hG : 0≤remainderGaussianEnvelope M m := by
    have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
    unfold remainderGaussianEnvelope
    positivity
  unfold centeredRemainderEnvelope
  rw [div_eq_mul_inv,←inv_pow,he]
  have hh := mul_le_mul_of_nonneg_right hv (mul_nonneg hK.le hG)
  have hh' := mul_le_mul_of_nonneg_right hh
    (show 0≤(((2*m+1:ℕ):ℝ)/(c/2))^j by positivity)
  convert hh' using 1
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
