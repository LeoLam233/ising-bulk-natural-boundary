import IsingBulk.Anisotropic.Geometry.BoundarySpectral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

theorem sliceP_deriv_pos {lam : ℝ} (hlam : 0<lam) (x : ℝ) : 0<deriv (sliceP lam) x := by
  rw [(sliceP_hasDerivAt lam x).deriv]
  have ht : 0≤Real.sinh x*Real.tanh (lam*x) := by
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg (Real.sinh_nonneg_iff.mpr hx) (tanh_nonneg (mul_nonneg hlam.le hx))
    · have h1 : Real.sinh x≤0 := Real.sinh_nonpos_iff.mpr hx
      have h2 : Real.tanh (lam*x)≤0 := by
        simpa only [Real.tanh_zero] using tanh_strictMono.monotone (mul_nonpos_of_nonneg_of_nonpos hlam.le hx)
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hp : 0<Real.cosh x*(lam/Real.cosh (lam*x)^2) := by positivity
  linarith

theorem sliceP_analyticAt (lam x : ℝ) : AnalyticAt ℝ (sliceP lam) x := by
  have hh : AnalyticAt ℝ (fun t:ℝ => Real.sinh (lam*t)/Real.cosh (lam*t)) x :=
    (Real.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_id)).div
      (Real.analyticAt_cosh.comp (analyticAt_const.mul analyticAt_id)) (Real.cosh_pos _).ne'
  convert Real.analyticAt_cosh.mul hh using 1
  ext t
  simp [sliceP,Real.tanh_eq_sinh_div_cosh]

/-- The signed inverse is analytic on the whole real line, including zero. -/
theorem slicePInv_analyticAt {lam : ℝ} (hlam : 0<lam) (y : ℝ) : AnalyticAt ℝ (slicePInv lam) y := by
  have hf := sliceP_analyticAt lam (slicePInv lam y)
  have hd := (sliceP_deriv_pos hlam (slicePInv lam y)).ne'
  have hcomp : (slicePInv lam) ∘ (sliceP lam)=id := by
    funext x
    exact sliceP_inv_apply hlam x
  have hi : AnalyticAt ℝ ((slicePInv lam) ∘ (sliceP lam)) (slicePInv lam y) := by
    rw [hcomp]
    exact analyticAt_id
  have ho := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).mp hi
  simpa only [sliceP_apply_inv hlam] using ho

def edgeIntersectionProfile (lam y : ℝ) : ℝ := geometryF2 lam (slicePInv lam (Real.cos y)) y

theorem edgeIntersectionProfile_analyticAt {lam : ℝ} (hlam : 0<lam) (y : ℝ) :
    AnalyticAt ℝ (edgeIntersectionProfile lam) y := by
  have hp := (slicePInv_analyticAt hlam (Real.cos y)).comp Real.analyticAt_cos
  unfold edgeIntersectionProfile geometryF2
  exact ((Real.analyticAt_cosh.comp hp).pow 2 |>.mul
    ((Real.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id)).pow 2)).sub
    (((Real.analyticAt_sinh.comp hp).pow 2).mul
      ((Real.analyticAt_cosh.comp (analyticAt_const.mul hp)).pow 2))

/-- The two edge curves cannot coincide when the anisotropy is strict. -/
theorem edgeIntersectionProfile_not_identically_zero {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) :
    ∃ y, edgeIntersectionProfile lam y ≠ 0 := by
  rcases lt_or_gt_of_ne hne with hl | hl
  · refine ⟨Real.pi/2,?_⟩
    have hp : 0<Real.cos (lam*(Real.pi/2)) := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],by nlinarith [Real.pi_pos]⟩
    simpa [edgeIntersectionProfile,geometryF2,slicePInv_zero hlam] using (sq_pos_of_pos hp).ne'
  · let y := Real.pi/(2*lam)
    have hy : 0<y := by dsimp [y]; positivity
    have hylt : y<Real.pi/2 := by
      dsimp [y]
      apply (div_lt_iff₀ (by positivity : 0<2*lam)).mpr
      nlinarith [Real.pi_pos]
    have hc : 0<Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hylt⟩
    have hx : 0<slicePInv lam (Real.cos y) := by
      simpa only [slicePInv_zero hlam] using (slicePInv_strictMono hlam hc)
    have he : lam*y=Real.pi/2 := by dsimp [y]; field_simp
    refine ⟨y,?_⟩
    have hp := mul_pos (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx))
      (sq_pos_of_pos (Real.cosh_pos (lam*slicePInv lam (Real.cos y))))
    simpa [edgeIntersectionProfile,geometryF2,he] using neg_ne_zero.mpr hp.ne'

theorem edgeIntersectionProfile_locally_nonzero {lam : ℝ} (hlam : 0<lam) (hne : lam≠1) (y : ℝ) :
    ∀ᶠ t in 𝓝[≠] y, edgeIntersectionProfile lam t≠0 := by
  rcases (edgeIntersectionProfile_analyticAt hlam y).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have ha : AnalyticOnNhd ℝ (edgeIntersectionProfile lam) Set.univ := fun t _ => edgeIntersectionProfile_analyticAt hlam t
    have he := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ y) h
    rcases edgeIntersectionProfile_not_identically_zero hlam hne with ⟨t,ht⟩
    exact False.elim (ht (he (Set.mem_univ t)))
  · exact h

end
end IsingBulk.Anisotropic
