import IsingBulk.Anisotropic.NegativeNormalForm.CorrectionEnergyControl
import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectionInverse

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

theorem UniformCorrectionWitness.corrected_energy_bounds {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (hRr : R≤r/2)
    (y : Config n) (hy : ‖y‖≤R/2) (hmy : ZeroMean y) :
    absoluteEnergy (J.W y)≤4*absoluteEnergy y ∧
      absoluteEnergy (P.V (J.W y)-y)≤absoluteEnergy y/64 := by
  have hw := J.w_inverse y hy
  have hwm := hw.2.2.2 hmy
  have hv := P.v_inverse (J.W y) (hw.1.trans hRr)
  obtain ⟨hvm,hproj⟩ := hv.2.2.2 hwm
  apply corrected_inverse_energy_control hn
    (inverseRootField B phi hphi d P.T P.V (J.W y)) (P.V (J.W y)) (J.W y) y
    (actualMeanField B phi hphi d P.T P.V (J.W y)) hvm
  · exact hproj
  · intro i
    exact (norm_le_pi_norm (inverseRootField B phi hphi d P.T P.V (J.W y)-1) i).trans
      (J.root_bound (J.W y) hw.1)
  · exact hw.2.2.1
  · exact J.normalized_mean_bound (J.W y) hw.1

end
end IsingBulk.Anisotropic.NegativeNormalForm
