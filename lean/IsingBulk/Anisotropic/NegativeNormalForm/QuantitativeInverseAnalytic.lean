import IsingBulk.Anisotropic.NegativeNormalForm.InverseGermAgreement
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecificLimits.Normed

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem perturbation_derivative_equiv {F : E → E} {r : ℝ} {c : NNReal}
    (hc : (c:ℝ)<1) (hLip : LipschitzOnWith c (fun x => F x-x) (closedBall 0 r))
    {x : E} (hx : ‖x‖<r) (hF : AnalyticAt ℂ F x) :
    ∃ e : E ≃L[ℂ] E, (e : E →L[ℂ] E)=fderiv ℂ F x := by
  have hnb : closedBall (0:E) r∈𝓝 x :=
    mem_of_superset (isOpen_ball.mem_nhds (by simpa using hx)) ball_subset_closedBall
  have hh := norm_fderiv_le_of_lipschitzOn ℂ hnb hLip
  change ‖fderiv ℂ (F-id) x‖≤(c:ℝ) at hh
  rw [fderiv_sub hF.differentiableAt differentiableAt_id,fderiv_id] at hh
  have hn : ‖(1:E →L[ℂ] E)-fderiv ℂ F x‖<1 := by
    rw [norm_sub_rev]
    exact hh.trans_lt hc
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one hn
  refine ⟨ContinuousLinearEquiv.ofUnit u,?_⟩
  have hu' : (u : E →L[ℂ] E)=fderiv ℂ F x := by simpa only [sub_sub_cancel] using hu
  ext v
  exact congrArg (fun A : E →L[ℂ] E => A v) hu'

theorem quantitative_inverse_analyticOnNhd (F V : E → E) (r : ℝ) (_hr : 0<r)
    (c : NNReal) (hc : (c:ℝ)<1)
    (hLip : LipschitzOnWith c (fun x => F x-x) (closedBall 0 r))
    (hF : AnalyticOnNhd ℂ F (ball 0 r))
    (hV : ∀ y, ‖y‖≤(1-(c:ℝ))*r → V y∈closedBall 0 r ∧ F (V y)=y ∧
      ‖V y‖≤‖y‖/(1-(c:ℝ))) :
    AnalyticOnNhd ℂ V (ball 0 ((1-(c:ℝ))*r)) := by
  intro y hy
  have hp : 0<1-(c:ℝ) := sub_pos.mpr hc
  have hy' : ‖y‖<(1-(c:ℝ))*r := by simpa using hy
  have hv := hV y hy'.le
  have hx : ‖V y‖<r := hv.2.2.trans_lt ((div_lt_iff₀ hp).mpr (by simpa [mul_comm] using hy'))
  have ha := hF (V y) (by simpa using hx)
  obtain ⟨e,he⟩ := perturbation_derivative_equiv hc hLip hx ha
  have hd : HasFDerivAt F (e : E →L[ℂ] E) (V y) := he.symm ▸ ha.differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℂ ω F (V y) := ha.contDiffAt
  let W := hcd.localInverse hd (by simp)
  have hW : AnalyticAt ℂ W y := by
    simpa only [hv.2.1] using (hcd.to_localInverse hd (by simp)).analyticAt
  have hWy : W y=V y := by
    simpa only [hv.2.1,W] using hcd.localInverse_apply_image hd (by simp)
  have hs := hcd.hasStrictFDerivAt' hd (by simp)
  have hright : ∀ᶠ w in 𝓝 y, F (W w)=w := by
    simpa only [hv.2.1,W,ContDiffAt.localInverse] using hs.eventually_right_inverse
  have hsmall : ∀ᶠ w in 𝓝 y, ‖W w‖<r :=
    hW.continuousAt.norm.eventually_lt continuousAt_const (by simpa only [hWy] using hx)
  have htarget : ∀ᶠ w in 𝓝 y, ‖w‖<(1-(c:ℝ))*r :=
    continuousAt_id.norm.eventually_lt continuousAt_const hy'
  apply hW.congr
  filter_upwards [hright,hsmall,htarget] with w hw hs ht
  exact perturbation_injOn F _ c hc hLip
    (by simpa only [mem_closedBall,dist_zero_right] using hs.le) (hV w ht.le).1
    (hw.trans (hV w ht.le).2.1.symm)

end
end IsingBulk.Anisotropic.NegativeNormalForm
