import IsingBulk.Anisotropic.NegativeNormalForm.QuantitativeInverse
import Mathlib.Analysis.Analytic.Basic

/-! A quantitative contraction representative agrees with the previously
constructed analytic inverse germ. No uniform radius is asserted for an
arbitrary total extension of that germ. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E]

 theorem quantitative_inverse_eq_germ (F V W : E → E) (r : ℝ) (hr : 0<r)
    (c : NNReal) (hc : (c:ℝ)<1)
    (hLip : LipschitzOnWith c (fun x => F x-x) (closedBall 0 r))
    (hV : ∀ y, ‖y‖≤(1-(c:ℝ))*r → V y ∈ closedBall 0 r ∧ F (V y)=y)
    (hW : ContinuousAt W 0) (hW0 : W 0=0) (hWinv : ∀ᶠ y in 𝓝 0, F (W y)=y) :
    V =ᶠ[𝓝 0] W := by
  have hR : 0<(1-(c:ℝ))*r := mul_pos (sub_pos.mpr hc) hr
  have hY : ∀ᶠ y : E in 𝓝 0, ‖y‖≤(1-(c:ℝ))*r := by
    filter_upwards [closedBall_mem_nhds (0:E) hR] with y hy
    simpa only [mem_closedBall,dist_zero_right] using hy
  have ht : Tendsto W (𝓝 0) (𝓝 0) := by simpa only [hW0] using hW.tendsto
  have hsmall : ∀ᶠ y in 𝓝 (0:E), W y ∈ closedBall 0 r :=
    ht.eventually (closedBall_mem_nhds (0:E) hr)
  filter_upwards [hY,hsmall,hWinv] with y hy hw hi
  exact perturbation_injOn F _ c hc hLip (hV y hy).1 hw ((hV y hy).2.trans hi.symm)

 theorem quantitative_inverse_analyticAt [NormedSpace ℂ E] [CompleteSpace E]
    (F V W : E → E) (r : ℝ) (hr : 0<r) (c : NNReal) (hc : (c:ℝ)<1)
    (hLip : LipschitzOnWith c (fun x => F x-x) (closedBall 0 r))
    (hV : ∀ y, ‖y‖≤(1-(c:ℝ))*r → V y ∈ closedBall 0 r ∧ F (V y)=y)
    (hW : AnalyticAt ℂ W 0) (hW0 : W 0=0) (hWinv : ∀ᶠ y in 𝓝 0, F (W y)=y) :
    AnalyticAt ℂ V 0 := by
  exact hW.congr (quantitative_inverse_eq_germ F V W r hr c hc hLip hV
    hW.continuousAt hW0 hWinv).symm

end IsingBulk.Anisotropic.NegativeNormalForm
