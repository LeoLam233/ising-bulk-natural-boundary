import IsingBulk.First.MeanRadialPhase

/-! Exact regular-chart derivatives with an arbitrary fixed temperature
trace. This supports uniform concavity at the physical mean residue. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

def regularMeanPhase (T : ℂ) (alpha : ℝ) (u : ℂ) : ℂ :=
  lowerArccos (T-Complex.cos (u-(alpha:ℂ)))

def regularMeanSecond (T : ℂ) (alpha : ℝ) (u : ℂ) : ℂ :=
  -Complex.cos (u-(alpha:ℂ))/Complex.sin (regularMeanPhase T alpha u) -
    Complex.sin (u-(alpha:ℂ))^2*(T-Complex.cos (u-(alpha:ℂ))) /
      Complex.sin (regularMeanPhase T alpha u)^3

theorem lowerArccos_sin_ne_zero (W : ℂ) (hr : 0 < W.re) (hi : 0 < W.im) :
    Complex.sin (lowerArccos W) ≠ 0 := by
  have hh := ((lowerArccos_differentiable W hr hi).hasDerivAt).ccos
  rw [show (fun z => Complex.cos (lowerArccos z)) = id from funext cos_lowerArccos] at hh
  have hv := hh.unique (hasDerivAt_id W)
  intro hz
  simp [hz] at hv

theorem regularMeanPhase_hasDerivAt (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hr : 0 < (T-Complex.cos (u-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    HasDerivAt (regularMeanPhase T alpha)
      (-Complex.sin (u-(alpha:ℂ))/Complex.sin (regularMeanPhase T alpha u)) u := by
  have hW := (((hasDerivAt_id u).sub_const (alpha:ℂ)).ccos).const_sub T
  have hp := (lowerArccos_differentiable _ hr hi).hasDerivAt
  rw [lowerArccos_deriv _ hr hi] at hp
  have hh := hp.comp u hW
  convert! hh using 1
  simp only [id_eq, mul_one, neg_neg, regularMeanPhase]
  ring

theorem regularMeanPhase_quadrant_near (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hr : 0 < (T-Complex.cos (u-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    ∀ᶠ v in 𝓝 u, 0 < (T-Complex.cos (v-(alpha:ℂ))).re ∧
      0 < (T-Complex.cos (v-(alpha:ℂ))).im := by
  have hc : ContinuousAt (fun v : ℂ => T-Complex.cos (v-(alpha:ℂ))) u := by fun_prop
  exact (continuousAt_const.eventually_lt (Complex.continuous_re.continuousAt.comp hc) hr).and
    (continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hc) hi)

theorem regularMeanPhase_second_hasDerivAt (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hr : 0 < (T-Complex.cos (u-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    HasDerivAt (deriv (regularMeanPhase T alpha)) (regularMeanSecond T alpha u) u := by
  have hp := regularMeanPhase_hasDerivAt T alpha u hr hi
  have hsin := hp.csin
  have hn := lowerArccos_sin_ne_zero _ hr hi
  change Complex.sin (regularMeanPhase T alpha u) ≠ 0 at hn
  have hcos : Complex.cos (regularMeanPhase T alpha u) = T-Complex.cos (u-(alpha:ℂ)) :=
    cos_lowerArccos _
  rw [hcos] at hsin
  have hnum := (((hasDerivAt_id u).sub_const (alpha:ℂ)).csin).neg
  have hh := hnum.div hsin hn
  have he : deriv (regularMeanPhase T alpha) =ᶠ[𝓝 u]
      (fun v => -Complex.sin (v-(alpha:ℂ))/Complex.sin (regularMeanPhase T alpha v)) := by
    filter_upwards [regularMeanPhase_quadrant_near T alpha u hr hi] with v hv
    exact (regularMeanPhase_hasDerivAt T alpha v hv.1 hv.2).deriv
  convert! hh.congr_of_eventuallyEq he using 1
  dsimp [regularMeanSecond]
  field_simp

/-- The explicit second derivative has the source negative value at the
regular undamped center, which is also in its domain of continuity. -/
theorem regularMeanSecond_at_selected (a : OrderedChartData) :
    regularMeanSecond ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ) a.alpha 0 = ((-2*a.d:ℝ):ℂ) := by
  have hp : regularMeanPhase ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ) a.alpha 0 = (a.beta:ℂ) :=
    centralChartPhase_zero a
  unfold regularMeanSecond
  rw [hp]
  simp only [zero_sub, Complex.cos_neg, Complex.sin_neg, neg_sq, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.ofReal_add, add_sub_cancel_left]
  have hh := a.curvature_identity
  unfold OrderedChartData.b at hh
  have he : -(Real.cos a.alpha)/Real.sin a.beta -
      (Real.sin a.alpha)^2*Real.cos a.beta/(Real.sin a.beta)^3 = -2*a.d := by
    rw [← hh]
    field_simp [ne_of_gt a.sin_beta_pos]
    ring
  exact_mod_cast he

end
end IsingBulk.First
