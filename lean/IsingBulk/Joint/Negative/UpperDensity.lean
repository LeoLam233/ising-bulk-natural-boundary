import IsingBulk.Joint.Negative.AngularDensity
import IsingBulk.Anisotropic.NegativeDominance.NegativeNumeratorBridge
import IsingBulk.Anisotropic.RegularEdges.AngularWrapping
import IsingBulk.Anisotropic.RegularEdges.IntegrandJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem transferW_eq_negative_edgeParamW {b : ℝ} {B : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hB : B u= -T K/IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (q : ℝ) :
    transferW K (q : ℂ)=edgeParamW b B u (q-Real.pi) := by
  unfold edgeParamW
  rw [hB, ← he]
  unfold transferW transferC transferB
  rw [Real.cos_sub_pi]
  simp only [Complex.ofReal_cos, Complex.ofReal_neg,
    div_eq_mul_inv]
  ring

theorem continuedTransferRoot_eq_negative_edgeParamRoot {b : ℝ}
    {B : ℂ → ℂ} {K : Coupling} {u : ℂ} (hB : B u= -T K/IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (q : ℝ) :
    continuedTransferRoot K (q : ℂ)=edgeParamRoot b B u (q-Real.pi) := by
  unfold continuedTransferRoot edgeParamRoot
  rw [transferW_eq_negative_edgeParamW hB he]

theorem transferRoot_eq_negative_edgeParamRoot {b : ℝ}
    {B : ℂ → ℂ} {K : Coupling} {u : ℂ} (hB : B u= -T K/IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : ℝ) :
    transferRoot K (q : ℂ)=edgeParamRoot b B u (q-Real.pi) := by
  unfold transferRoot edgeParamRoot
  rw [transferW_eq_negative_edgeParamW hB he]
  apply smallRoot_eq_continuedRoot
  have hc : 0≤1-Real.cos (q-Real.pi) := sub_nonneg.mpr (Real.cos_le_one _)
  have hm := mul_nonneg hBi.le hc
  simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im,
    sub_zero,mul_zero]
  linarith

/-- Exact negative-chart numerator identity; the only extra phase is the
constant sign from T/S = -B. No phase alignment across particle numbers is used. -/
theorem continuedAngularWeight_eq_negative_edgeNumerator {N : ℕ}
    {b : ℝ} {B S : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hB : B u= -T K/IsingBulk.Joint.S K) (hS : S u=IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (q : Fin N → ℝ) :
    continuedAngularWeight K (fun i => (q i : ℂ))=
      (-1 : ℂ)^(N.choose 2)*edgeNumerator b B S u (List.ofFn (fun i => q i-Real.pi)) := by
  rw [edgeNumerator_eq_indexed]
  unfold continuedAngularWeight
  simp_rw [continuedTransferRoot_eq_negative_edgeParamRoot hB he, angularRootPair_shift_pi]
  rw [hS]
  have hcoef : (T K/IsingBulk.Joint.S K)^(N.choose 2)=(-1 : ℂ)^(N.choose 2)*(B u)^(N.choose 2) := by
    rw [← mul_pow, hB]
    congr 1
    ring
  rw [hcoef]
  ring

theorem continuedAngularDensity_eq_negative_edgeFullIntegrand {N : ℕ}
    {b : ℝ} {B S : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hB : B u= -T K/IsingBulk.Joint.S K) (hS : S u=IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (q : Fin N → ℝ)
    (hZ : 1-∏ i, continuedTransferRoot K (q i : ℂ)≠0) :
    continuedAngularDensity K (fun i => (q i : ℂ))=
      (-1 : ℂ)^(N.choose 2)*edgeFullIntegrand b B S u (fun i => q i-Real.pi) := by
  unfold continuedAngularDensity
  rw [continuedAngularWeight_eq_negative_edgeNumerator hB hS he]
  simp_rw [continuedTransferRoot_eq_negative_edgeParamRoot hB he] at hZ ⊢
  unfold edgeFullIntegrand edgeRootProduct
  field_simp [hZ]
  ring

end
end IsingBulk.Joint.Negative
