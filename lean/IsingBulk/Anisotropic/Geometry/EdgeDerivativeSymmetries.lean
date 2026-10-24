import IsingBulk.Anisotropic.Geometry.RegularFrontierChart
import IsingBulk.Anisotropic.Geometry.CoordinateSymmetries

namespace IsingBulk.Anisotropic
noncomputable section

theorem deriv_conjugate_of_reflection {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (he : ∀ w, f (star w)=star (f w)) :
    deriv f (star z)=star (deriv f z) := by
  have hfun : (star ∘ f ∘ starRingEnd ℂ)=f := by
    funext w
    change star (f (star w))=f w
    rw [he,star_star]
  have h := hf.differentiableAt.hasDerivAt.star_conj
  change HasDerivAt (star ∘ f ∘ starRingEnd ℂ) (star (deriv f z)) (star z) at h
  rw [hfun] at h
  exact h.deriv

theorem edgeMapU_deriv_conj {lam : ℝ} (e : ℝ) {z : ℂ} (hd : spectralDet lam z≠0) :
    deriv (edgeMapU lam (e:ℂ)) (star z)=star (deriv (edgeMapU lam (e:ℂ)) z) :=
  deriv_conjugate_of_reflection (edgeMapU_analyticAt (e := (e:ℂ))
    (spectralT_ne_zero_of_det_ne_zero hd)) (edgeMapU_conj lam e)

theorem edgeMapV_deriv_conj {lam : ℝ} (e : ℝ) {z : ℂ} (hd : spectralDet lam z≠0) :
    deriv (edgeMapV lam (e:ℂ)) (star z)=star (deriv (edgeMapV lam (e:ℂ)) z) :=
  deriv_conjugate_of_reflection (edgeMapV_analyticAt (e := (e:ℂ))
    (spectralS_ne_zero_of_det_ne_zero hd)) (edgeMapV_conj lam e)

theorem edgeMapV_deriv_axis_nonzero {lam : ℝ} (hlam : lam≠0) (e : ℂ) {z : ℂ}
    (hd : spectralDet lam z≠0) (hder : deriv (edgeMapU lam e) z≠0) :
    deriv (edgeMapV (lam⁻¹) e) ((lam:ℂ)*z)≠0 := by
  have ha : AnalyticAt ℂ (edgeMapV (lam⁻¹) e) ((lam:ℂ)*z) :=
    edgeMapV_analyticAt (e := e) (by
      rw [spectralS_axis_exchange]
      exact spectralT_ne_zero_of_det_ne_zero hd)
  have h := ha.differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).const_mul (lam:ℂ))
  have he : (fun w => edgeMapV (lam⁻¹) e ((lam:ℂ)*w))=edgeMapU lam e :=
    funext (edgeMapV_axis_exchange hlam e)
  change HasDerivAt (fun w => edgeMapV (lam⁻¹) e ((lam:ℂ)*w))
    (deriv (edgeMapV (lam⁻¹) e) ((lam:ℂ)*z)*((lam:ℂ)*1)) z at h
  rw [he] at h
  intro hn
  have hh := h.deriv
  rw [hn,zero_mul] at hh
  exact hder hh

theorem edgeMapU_deriv_axis_nonzero {lam : ℝ} (hlam : lam≠0) (e : ℂ) {z : ℂ}
    (hd : spectralDet lam z≠0) (hder : deriv (edgeMapV lam e) z≠0) :
    deriv (edgeMapU (lam⁻¹) e) ((lam:ℂ)*z)≠0 := by
  have ha : AnalyticAt ℂ (edgeMapU (lam⁻¹) e) ((lam:ℂ)*z) :=
    edgeMapU_analyticAt (e := e) (by
      rw [spectralT_axis_exchange hlam]
      exact spectralS_ne_zero_of_det_ne_zero hd)
  have h := ha.differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).const_mul (lam:ℂ))
  have he : (fun w => edgeMapU (lam⁻¹) e ((lam:ℂ)*w))=edgeMapV lam e :=
    funext (edgeMapU_axis_exchange hlam e)
  change HasDerivAt (fun w => edgeMapU (lam⁻¹) e ((lam:ℂ)*w))
    (deriv (edgeMapU (lam⁻¹) e) ((lam:ℂ)*z)*((lam:ℂ)*1)) z at h
  rw [he] at h
  intro hn
  have hh := h.deriv
  rw [hn,zero_mul] at hh
  exact hder hh

end
end IsingBulk.Anisotropic
