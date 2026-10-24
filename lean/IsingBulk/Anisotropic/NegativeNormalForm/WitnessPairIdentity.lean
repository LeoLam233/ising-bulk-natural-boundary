import IsingBulk.Anisotropic.NegativeNormalForm.MeanPairAlgebra
import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectedEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.ReciprocalFieldBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem UniformCorrectionWitness.forward_pair_identity {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (hRr : R≤r/2)
    (y : Config n) (hy : ‖y‖≤R/2) (hmy : ZeroMean y) (i j : Fin n)
    (hroot : rootScalar B phi hphi (P.T (P.V (J.W y)),(d,P.V (J.W y) i))-
        rootScalar B phi hphi (P.T (P.V (J.W y)),(d,P.V (J.W y) j))=
      (P.V (J.W y) i-P.V (J.W y) j)*rootPairSlope B phi hphi (P.T (P.V (J.W y))) d (P.V (J.W y) i) (P.V (J.W y) j))
    (hsep : P.V (J.W y) i*rootScalar B phi hphi (P.T (P.V (J.W y)),(d,P.V (J.W y) i))-
        P.V (J.W y) j*rootScalar B phi hphi (P.T (P.V (J.W y)),(d,P.V (J.W y) j))=
      (P.V (J.W y) i-P.V (J.W y) j)*separablePairFactor B phi hphi (P.T (P.V (J.W y))) d (P.V (J.W y) i) (P.V (J.W y) j)) :
    (P.V (J.W y) i-P.V (J.W y) j)*
      correctedSeparablePairFactor B phi hphi (P.T (P.V (J.W y))) d (P.V (J.W y)) i j=y i-y j := by
  have hw := J.w_inverse y hy
  have hwm := hw.2.2.2 hmy
  have hv := P.v_inverse (J.W y) (hw.1.trans hRr)
  obtain ⟨hvm,hproj⟩ := hv.2.2.2 hwm
  let S : Config n := inverseRootField B phi hphi d P.T P.V (J.W y)
  have hS (k : Fin n) : ‖S k-1‖≤1/64 :=
    (norm_le_pi_norm (S-1) k).trans (J.root_bound (J.W y) hw.1)
  have hSn (k : Fin n) : S k≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (scalar_norm_lower_of_near_one (S k) ((hS k).trans (by norm_num))))
  have hrec (k : Fin n) : ‖1-(S k)⁻¹‖≤1/2 := by
    have h := scalar_reciprocal_error (S k) ((hS k).trans (by norm_num))
    linarith [hS k]
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hden : (∑ k,(S k)⁻¹)≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by positivity : (0:ℝ)<(n:ℝ)*(1-1/2)) (reciprocal_sum_norm_lower S (1/2) hrec))
  have h := correctedSeparablePairFactor_identity hn B phi hphi (P.T (P.V (J.W y))) d
    (P.V (J.W y)) hvm i j hSn hden hroot hsep
  change project (fun k => P.V (J.W y) k*S k)=J.W y at hproj
  change meanCorrection (meanCoefficients S) (project (fun k => P.V (J.W y) k*S k)) i-
    meanCorrection (meanCoefficients S) (project (fun k => P.V (J.W y) k*S k)) j=_ at h
  rw [hproj] at h
  change meanCorrection (actualMeanField B phi hphi d P.T P.V (J.W y)) (J.W y) i-
    meanCorrection (actualMeanField B phi hphi d P.T P.V (J.W y)) (J.W y) j=_ at h
  rw [hw.2.2.1] at h
  exact h.symm

end
end IsingBulk.Anisotropic.NegativeNormalForm
