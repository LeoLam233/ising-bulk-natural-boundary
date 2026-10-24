import IsingBulk.Anisotropic.NegativeDominance.ContinuationDensity
import IsingBulk.Anisotropic.RegularEdges.AngularWrapping
import IsingBulk.Anisotropic.RegularEdges.IntegrandJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem transferW_eq_negative_edgeParamW {lam b : ℝ} {B : ℂ → ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (q : ℝ) :
    transferW lam z (q : ℂ)=edgeParamW b B u (q-Real.pi) := by
  unfold edgeParamW
  rw [hB, ← he]
  unfold transferW edgeMapV
  rw [Real.cos_sub_pi]
  simp only [Complex.ofReal_cos, Complex.ofReal_neg,
    div_eq_mul_inv]
  ring

theorem continuedTransferRoot_eq_negative_edgeParamRoot {lam b : ℝ}
    {B : ℂ → ℂ} {z u : ℂ} (hB : B u= -spectralT lam z/spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (q : ℝ) :
    continuedTransferRoot lam z (q : ℂ)=edgeParamRoot b B u (q-Real.pi) := by
  unfold continuedTransferRoot edgeParamRoot
  rw [transferW_eq_negative_edgeParamW hB he]

theorem transferRoot_eq_negative_edgeParamRoot {lam b : ℝ}
    {B : ℂ → ℂ} {z u : ℂ} (hB : B u= -spectralT lam z/spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : ℝ) :
    transferRoot lam z (q : ℂ)=edgeParamRoot b B u (q-Real.pi) := by
  unfold transferRoot edgeParamRoot
  rw [transferW_eq_negative_edgeParamW hB he]
  apply smallRoot_eq_continuedRoot
  have hc : 0≤1-Real.cos (q-Real.pi) := sub_nonneg.mpr (Real.cos_le_one _)
  have hm := mul_nonneg hBi.le hc
  simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im,
    sub_zero,mul_zero]
  linarith

theorem angularRootPair_shift_pi (r s : ℂ) (q t : ℝ) :
    angularRootPair r s ((q-Real.pi : ℝ) : ℂ) ((t-Real.pi : ℝ) : ℂ)=
      angularRootPair r s (q : ℂ) (t : ℂ) := by
  unfold angularRootPair
  rw [Complex.ofReal_sub, Complex.ofReal_sub, sub_sub_sub_cancel_right]

/-- Exact negative-chart numerator identity; the only extra phase is the
constant sign from T/S = -B. No phase alignment across particle numbers is used. -/
theorem continuedAngularWeight_eq_negative_edgeNumerator {N : ℕ}
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (q : Fin N → ℝ) :
    continuedAngularWeight lam z (fun i => (q i : ℂ))=
      (-1 : ℂ)^(N.choose 2)*edgeNumerator b B S u (List.ofFn (fun i => q i-Real.pi)) := by
  rw [edgeNumerator_eq_indexed]
  unfold continuedAngularWeight
  simp_rw [continuedTransferRoot_eq_negative_edgeParamRoot hB he, angularRootPair_shift_pi]
  rw [hS]
  have hcoef : (spectralT lam z/spectralS z)^(N.choose 2)=(-1 : ℂ)^(N.choose 2)*(B u)^(N.choose 2) := by
    rw [← mul_pow, hB]
    congr 1
    ring
  rw [hcoef]
  ring

theorem continuedAngularDensity_eq_negative_edgeFullIntegrand {N : ℕ}
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (q : Fin N → ℝ)
    (hZ : 1-∏ i, continuedTransferRoot lam z (q i : ℂ)≠0) :
    continuedAngularDensity lam z (fun i => (q i : ℂ))=
      (-1 : ℂ)^(N.choose 2)*edgeFullIntegrand b B S u (fun i => q i-Real.pi) := by
  unfold continuedAngularDensity
  rw [continuedAngularWeight_eq_negative_edgeNumerator hB hS he]
  simp_rw [continuedTransferRoot_eq_negative_edgeParamRoot hB he] at hZ ⊢
  unfold edgeFullIntegrand edgeRootProduct
  field_simp [hZ]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
