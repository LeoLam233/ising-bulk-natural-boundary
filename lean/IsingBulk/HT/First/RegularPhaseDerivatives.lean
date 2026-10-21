import IsingBulk.HT.First.UpperPhase
import IsingBulk.HT.First.RegularChartData
import IsingBulk.First.MeanRegularDerivatives

/-! Derivatives of the existing literal regularMeanPhase on the entire upper
W half-plane. The source function is reused, with no replacement local model. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.Branch IsingBulk.First
open scoped Topology

theorem lowerArccos_sin_ne_zero_of_upper (W : ℂ) (hi : 0 < W.im) :
    Complex.sin (lowerArccos W) ≠ 0 := by
  have hh := ((lowerArccos_analytic_of_upper hi).differentiableAt.hasDerivAt).ccos
  rw [show (fun z => Complex.cos (lowerArccos z)) = id from funext cos_lowerArccos] at hh
  have hv := hh.unique (hasDerivAt_id W)
  intro hz
  simp [hz] at hv

theorem regularMeanPhase_hasDerivAt_upper (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    HasDerivAt (regularMeanPhase T alpha)
      (-Complex.sin (u-(alpha:ℂ))/Complex.sin (regularMeanPhase T alpha u)) u := by
  have hW := (((hasDerivAt_id u).sub_const (alpha:ℂ)).ccos).const_sub T
  have hp := lowerArccos_hasDerivAt_regular _ (lowerArccos_analytic_of_upper hi)
  have hh := hp.comp u hW
  convert! hh using 1
  simp only [id_eq, mul_one, neg_neg, regularMeanPhase]
  ring

theorem regularMeanPhase_upper_near (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    ∀ᶠ v in 𝓝 u, 0 < (T-Complex.cos (v-(alpha:ℂ))).im := by
  have hc : ContinuousAt (fun v : ℂ => T-Complex.cos (v-(alpha:ℂ))) u := by fun_prop
  exact continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hc) hi

theorem regularMeanPhase_second_hasDerivAt_upper (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    HasDerivAt (deriv (regularMeanPhase T alpha)) (regularMeanSecond T alpha u) u := by
  have hp := regularMeanPhase_hasDerivAt_upper T alpha u hi
  have hsin := hp.csin
  have hn := lowerArccos_sin_ne_zero_of_upper _ hi
  change Complex.sin (regularMeanPhase T alpha u) ≠ 0 at hn
  have hcos : Complex.cos (regularMeanPhase T alpha u) = T-Complex.cos (u-(alpha:ℂ)) :=
    cos_lowerArccos _
  rw [hcos] at hsin
  have hnum := (((hasDerivAt_id u).sub_const (alpha:ℂ)).csin).neg
  have hh := hnum.div hsin hn
  have he : deriv (regularMeanPhase T alpha) =ᶠ[𝓝 u]
      (fun v => -Complex.sin (v-(alpha:ℂ))/Complex.sin (regularMeanPhase T alpha v)) := by
    filter_upwards [regularMeanPhase_upper_near T alpha u hi] with v hv
    exact (regularMeanPhase_hasDerivAt_upper T alpha v hv).deriv
  convert! hh.congr_of_eventuallyEq he using 1
  dsimp [regularMeanSecond]
  field_simp


end
end IsingBulk.HT.First
