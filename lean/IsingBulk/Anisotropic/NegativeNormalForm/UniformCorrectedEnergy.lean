import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectionInverse

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric
open scoped BigOperators

 theorem UniformCorrectionWitness.mean_factorization {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (hRr : R≤r/2)
    (w : Config n) (hw : ‖w‖≤R) (hm : ZeroMean w) :
    pairing w (actualMeanField B phi hphi d P.T P.V w)=
      mean (phaseSeparableMap B phi hphi d (P.T (P.V w)) (P.V w)) := by
  let S := inverseRootField B phi hphi d P.T P.V w
  have hSb : ‖S-1‖≤1/4 := (J.root_bound w hw).trans (by norm_num)
  have hSi (i : Fin n) : ‖S i-1‖≤1/4 := (norm_le_pi_norm (S-1) i).trans hSb
  have hSn (i : Fin n) : S i≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (scalar_norm_lower_of_near_one (S i) ((hSi i).trans (by norm_num))))
  have hSinv (i : Fin n) : ‖1-(S i)⁻¹‖≤1/2 := by
    have hh := scalar_reciprocal_error (S i) ((hSi i).trans (by norm_num))
    linarith [hSi i]
  have hden : (∑ i, (S i)⁻¹)≠0 := by
    have hh := reciprocal_sum_norm_lower S (1/2) hSinv
    have hnp : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact norm_pos_iff.mp (by nlinarith)
  have hp := (P.v_inverse w (hw.trans hRr)).2.2.2 hm
  exact meanCoefficients_factorization (P.V w) w S hp.1 hm hSn hden hp.2

/-- Exact energy of the full constructed inverse, now on the whole common ball,
including coincidences and the quadratic null cone. -/
theorem UniformCorrectionWitness.exact_energy {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R)
    (hr : 0<r) (hRr : R≤r/2) (y : Config n) (hy : ‖y‖≤R/2) (hm : ZeroMean y)
    (hh : centralHessian B phi d≠0)
    (ha : phaseParameterQuotient B phi hphi d (P.T (P.V (J.W y)))≠0) :
    ZeroMean (P.V (J.W y)) ∧
      P.T (P.V (J.W y))=1-Complex.cos d+centralHessian B phi d/(2*n)*quadratic y := by
  obtain ⟨hw,hwn,hcorr,hmw⟩ := J.w_inverse y hy
  have hm' := hmw hm
  have hp := P.v_inverse (J.W y) (hw.trans hRr)
  have hmv := (hp.2.2.2 hm').1
  have hproj := (hp.2.2.2 hm').2
  have hpair := J.mean_factorization hn B phi hphi d r C R P hRr (J.W y) hw hm'
  have hrec := meanCorrection_recovers_energy hn
    (phaseSeparableMap B phi hphi d (P.T (P.V (J.W y))) (P.V (J.W y)))
    (actualMeanField B phi hphi d P.T P.V (J.W y)) (by rw [hproj]; exact hpair)
  rw [hproj,hcorr] at hrec
  have hpol := (P.t_pole (P.V (J.W y)) (by linarith [hp.1])).1
  have henergy := phaseSeparableMap_exact hn B phi hphi d (P.T (P.V (J.W y))) (P.V (J.W y)) hmv hh ha hpol
  rw [← hrec] at henergy
  exact ⟨hmv,by linear_combination henergy⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
