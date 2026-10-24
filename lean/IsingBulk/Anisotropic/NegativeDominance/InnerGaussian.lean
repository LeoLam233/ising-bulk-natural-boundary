import IsingBulk.Anisotropic.NegativeCycles.ActualInnerRemainder
import IsingBulk.Anisotropic.NegativeDominance.ParticleCauchyGaussian

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges NegativeCycles

/-- The literal inner-remainder Gaussian, including exponential volume,
is bounded by the already derived all-index matched majorant. -/
theorem remainderGaussianEnvelope_le_particle {M V : ℝ} (hM : 1≤M) (hV : 1≤V) (m : ℕ) :
    V^(2*m)*remainderGaussianEnvelope M m≤
      M*particleEdgeMajorant (1/2) M (M*V) (2*m+1) := by
  have hM0 : 0≤M := by linarith
  have hV0 : 0≤V := by linarith
  have hc (n : ℕ) : 1≤matchingCount n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [matchingCount]; nlinarith
  have hcR : (1 : ℝ)≤matchingCount (m+1) := by exact_mod_cast hc (m+1)
  have hchoose : (2*m+1).choose 2=2*m*m+m := by
    rw [Nat.choose_two_right,Nat.add_sub_cancel]
    rw [show (2*m+1)*(2*m)=(2*m*m+m)*2 by ring,Nat.mul_div_cancel]
    norm_num
  have hp : (1/2 : ℝ)^((2*m+1).choose 2)≤(1/2 : ℝ)^(2*m*m) := by
    rw [hchoose,pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hVp : V^(2*m)≤V^(2*m+1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) hV
  rw [particleEdgeMajorant_odd]
  unfold remainderGaussianEnvelope oddEdgeMajorant
  calc
    _≤V^(2*m+1)*((M*M^m)*M^(2*m+1)*(1/2 : ℝ)^(2*m*m)) := by gcongr
    _≤V^(2*m+1)*((M*M^m)*M^(2*m+1)*((matchingCount (m+1) : ℝ)*(1/2 : ℝ)^(2*m*m))) := by
      gcongr
      exact le_mul_of_one_le_left (by positivity) hcR
    _=_ := by rw [mul_pow]; ring

/-- Direct all-order Gaussian bound for root's actual inner remainder and
its explicit c/N Cauchy factor. -/
theorem inner_cauchy_gaussian_bound {M V K δ : ℝ}
    (hM : 1≤M) (hV : 1≤V) (hK : 0<K) (hδ : 0<δ) :
    ∃a L : ℝ,0<a ∧ 0<L ∧ ∀m j : ℕ,
      K*V^(2*m)*remainderGaussianEnvelope M m*(((2*m+1 : ℕ) : ℝ)/δ)^j≤
        Real.exp (-a*((2*m+1 : ℕ) : ℝ)^2+
          ((j : ℝ)+1)*Real.log ((2*m+1 : ℕ) : ℝ)+L*((j : ℝ)+1)) := by
  have hMp : 0<M := by linarith
  have hVp : 0<V := by linarith
  obtain ⟨a,L,ha,hL,hb⟩ := particle_cauchy_gaussian_bound
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)<1) hMp (mul_pos hMp hVp) hδ (mul_pos hK hMp)
  refine ⟨a,L,ha,hL,fun m j => ?_⟩
  apply le_trans _ (hb (2*m+1) (by omega) j)
  have hh := mul_le_mul_of_nonneg_left (remainderGaussianEnvelope_le_particle hM hV m) hK.le
  have hh' := mul_le_mul_of_nonneg_right hh (show 0≤(((2*m+1 : ℕ) : ℝ)/δ)^j by positivity)
  convert hh' using 1 <;> ring

end
end IsingBulk.Anisotropic.NegativeDominance
