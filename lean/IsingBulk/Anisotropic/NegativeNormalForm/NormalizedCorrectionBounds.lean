import IsingBulk.Anisotropic.NegativeNormalForm.NormalizedCorrection

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

 theorem normalizedRankCoefficient_field_difference {n : ℕ} (hn : n≠0)
    (e f : Config n) (A L K r D : ℝ)
    (hA : 0≤A) (_hL : 0≤L) (hK : 0≤K) (_hD : 0≤D)
    (he : ‖e‖≤A) (hf : ‖f‖≤A) (hef : ‖e-f‖≤L*D) (hAr : A^2<r)
    (hLip : ∀ z w : ℂ, ‖z‖<r → ‖w‖<r →
      ‖normalizedRankCoefficient z-normalizedRankCoefficient w‖≤K*‖z-w‖) :
    ‖normalizedRankCoefficient (mean (e*e))-normalizedRankCoefficient (mean (f*f))‖≤2*K*A*L*D := by
  have heq : ‖mean (e*e)‖<r := (mean_product_norm_le hn e e).trans_lt
    ((mul_le_mul he he (norm_nonneg _) hA).trans_lt (by simpa only [pow_two] using hAr))
  have hfq : ‖mean (f*f)‖<r := (mean_product_norm_le hn f f).trans_lt
    ((mul_le_mul hf hf (norm_nonneg _) hA).trans_lt (by simpa only [pow_two] using hAr))
  calc
    _ ≤ K*‖mean (e*e)-mean (f*f)‖ := hLip _ _ heq hfq
    _ ≤ K*((‖e‖+‖f‖)*‖e-f‖) := mul_le_mul_of_nonneg_left (mean_square_difference_le hn e f) hK
    _ ≤ K*((A+A)*(L*D)) := by gcongr
    _ = _ := by ring

/-- Dimension-free Lipschitz estimate for the actual no-nullcone-division correction. -/
 theorem normalizedMeanCorrection_error_bound {n : ℕ} (hn : n≠0)
    (e f w z : Config n) (A R L K : ℝ)
    (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hK : 0≤K)
    (he : ‖e‖≤A) (hf : ‖f‖≤A) (hz : ‖z‖≤R) (hef : ‖e-f‖≤L*‖w-z‖)
    (hc : ‖normalizedRankCoefficient (mean (e*e))-normalizedRankCoefficient (mean (f*f))‖≤2*K*A*L*‖w-z‖) :
    ‖(normalizedMeanCorrection e w-w)-(normalizedMeanCorrection f z-z)‖≤
      (A^2+2*R*A*L+2*K*R*A^3*L)*‖w-z‖ := by
  let a := normalizedRankCoefficient (mean (e*e))
  let b := normalizedRankCoefficient (mean (f*f))
  let μ := mean (w*e)
  let ν := mean (z*f)
  have ha : ‖a‖≤1 := normalizedRankCoefficient_norm_le _
  have hν : ‖ν‖≤R*A := (mean_product_norm_le hn z f).trans (mul_le_mul hz hf (norm_nonneg _) hR)
  have hμν : ‖μ-ν‖≤(A+R*L)*‖w-z‖ := by
    calc
      _ ≤ ‖w-z‖*‖e‖+‖z‖*‖e-f‖ := mean_product_difference_le hn w z e f
      _ ≤ ‖w-z‖*A+R*(L*‖w-z‖) := by gcongr
      _ = _ := by ring
  have hidentity : (normalizedMeanCorrection e w-w)-(normalizedMeanCorrection f z-z)=
      (a*(μ-ν)) • e+(a*ν) • (e-f)+((a-b)*ν) • f := by
    ext i
    simp only [normalizedMeanCorrection,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    dsimp only [a,b,μ,ν]
    ring
  rw [hidentity]
  calc
    _ ≤ ‖(a*(μ-ν)) • e+(a*ν) • (e-f)‖+‖((a-b)*ν) • f‖ := norm_add_le _ _
    _ ≤ (‖(a*(μ-ν)) • e‖+‖(a*ν) • (e-f)‖)+‖((a-b)*ν) • f‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = (‖a‖*‖μ-ν‖*‖e‖+‖a‖*‖ν‖*‖e-f‖)+‖a-b‖*‖ν‖*‖f‖ := by simp only [norm_smul,norm_mul]
    _ ≤ (1*((A+R*L)*‖w-z‖)*A+1*(R*A)*(L*‖w-z‖))+(2*K*A*L*‖w-z‖)*(R*A)*A := by
      gcongr
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
