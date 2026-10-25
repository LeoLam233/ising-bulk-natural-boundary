import IsingBulk.Joint.Geometry.SpectralGap
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.MeanValue

namespace IsingBulk.Joint
noncomputable section
open Set Metric InnerProductSpace Real

/-- The standard continuous line-submean definition of plurisubharmonicity. -/
def IsPlurisubharmonicOn (φ : Coupling → ℝ) (D : Set Coupling) : Prop :=
  ContinuousOn φ D ∧ ∀ K V : Coupling, ∀ R : ℝ,
    (∀ z ∈ closedBall (0 : ℂ) |R|, K + z • V ∈ D) →
    φ K ≤ circleAverage (fun z : ℂ => φ (K + z • V)) 0 R

def spectralBarrier (K : Coupling) : ℝ := max 0 (-Real.log (spectralGap K))

def spectralExhaustion (K : Coupling) : ℝ :=
  ‖K.1‖^2 + ‖K.2‖^2 + spectralBarrier K

theorem spectralLinear_ne_zero {K : Coupling} (hK : K ∉ spectralSet)
    {ab : ℝ × ℝ} (hab : ab ∈ spectralSquare) : spectralLinear K ab ≠ 0 := by
  intro he
  apply hK
  exact ⟨ab.1,hab.1,ab.2,hab.2,by dsimp [spectralLinear] at he; linear_combination he⟩

theorem spectralBarrier_continuousOn : ContinuousOn spectralBarrier spectralSetᶜ := by
  intro K hK
  have h : ContinuousAt spectralBarrier K := continuousAt_const.max ((Real.continuousAt_log
    ((spectralGap_pos_iff K).mpr hK).ne').comp spectralGap_continuous.continuousAt).neg
  exact h.continuousWithinAt

theorem spectralExhaustion_continuousOn : ContinuousOn spectralExhaustion spectralSetᶜ := by
  exact ((by fun_prop : Continuous (fun K : Coupling => ‖K.1‖^2 + ‖K.2‖^2)).continuousOn).add
    spectralBarrier_continuousOn

theorem norm_sq_submean (a b : ℂ) (R : ℝ) :
    ‖a‖^2 ≤ circleAverage (fun z : ℂ => ‖a + z*b‖^2) 0 R := by
  let h : ℂ → ℝ := fun z => ((2 : ℂ)*star a*(a+z*b) - (‖a‖^2 : ℝ)).re
  have hh : HarmonicOnNhd h (closedBall 0 |R|) := by
    intro z _
    exact (show AnalyticAt ℂ (fun z : ℂ => (2 : ℂ)*star a*(a+z*b) - (‖a‖^2 : ℝ)) z by fun_prop).harmonicAt_re
  have hzero : h 0 = ‖a‖^2 := by
    simp [h,Complex.mul_re,Complex.mul_im,Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [← hzero,← hh.circleAverage_eq]
  apply circleAverage_mono (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
    (show ContinuousOn (fun z : ℂ => ‖a+z*b‖^2) (sphere 0 |R|) by fun_prop).circleIntegrable'
  intro z _
  simp only [h,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.add_re,Complex.add_im,Complex.sq_norm,Complex.normSq_apply]
  norm_num
  nlinarith [sq_nonneg (z.re*b.re-z.im*b.im),sq_nonneg (z.re*b.im+z.im*b.re)]

theorem spectralBarrier_submean (K V : Coupling) (R : ℝ)
    (hD : ∀ z ∈ closedBall (0 : ℂ) |R|, K + z • V ∉ spectralSet) :
    spectralBarrier K ≤ circleAverage (fun z : ℂ => spectralBarrier (K+z•V)) 0 R := by
  have hc : ContinuousOn (fun z : ℂ => spectralBarrier (K+z•V)) (closedBall 0 |R|) :=
    spectralBarrier_continuousOn.comp (by fun_prop) hD
  have hi := (hc.mono sphere_subset_closedBall).circleIntegrable'
  by_cases hlog : 0 ≤ -Real.log (spectralGap K)
  · rw [spectralBarrier,max_eq_right hlog]
    let ab := spectralMinimizer K
    let g : ℂ → ℂ := fun z => spectralLinear (K+z•V) ab
    have hh : HarmonicOnNhd (fun z => -Real.log ‖g z‖) (closedBall 0 |R|) := by
      intro z hz
      exact ((show AnalyticAt ℂ g z by dsimp [g,spectralLinear,A,S,T]; fun_prop).harmonicAt_log_norm
        (spectralLinear_ne_zero (hD z hz) (spectralMinimizer_mem K))).neg
    have hz : -Real.log (spectralGap K) = -Real.log ‖g 0‖ := by simp [g,ab,spectralGap]
    rw [hz,← hh.circleAverage_eq]
    apply circleAverage_mono (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable' hi
    intro z hz
    have hp := (spectralGap_pos_iff (K+z•V)).mpr (hD z (sphere_subset_closedBall hz))
    exact (neg_le_neg (Real.log_le_log hp (spectralGap_le _ (spectralMinimizer_mem K)))).trans
      (le_max_right _ _)
  · rw [spectralBarrier,max_eq_left (le_of_not_ge hlog)]
    exact circleAverage_nonneg_of_nonneg (fun z _ => le_max_left _ _)

theorem spectralExhaustion_isPlurisubharmonic :
    IsPlurisubharmonicOn spectralExhaustion spectralSetᶜ := by
  refine ⟨spectralExhaustion_continuousOn,?_⟩
  intro K V R hD
  have h₁ := norm_sq_submean K.1 V.1 R
  have h₂ := norm_sq_submean K.2 V.2 R
  have h₃ := spectralBarrier_submean K V R hD
  have hi₁ : CircleIntegrable (fun z : ℂ => ‖K.1+z*V.1‖^2) 0 R :=
    (show ContinuousOn (fun z : ℂ => ‖K.1+z*V.1‖^2) (sphere 0 |R|) by fun_prop).circleIntegrable'
  have hi₂ : CircleIntegrable (fun z : ℂ => ‖K.2+z*V.2‖^2) 0 R :=
    (show ContinuousOn (fun z : ℂ => ‖K.2+z*V.2‖^2) (sphere 0 |R|) by fun_prop).circleIntegrable'
  have hi₃ : CircleIntegrable (fun z : ℂ => spectralBarrier (K+z•V)) 0 R :=
    (spectralBarrier_continuousOn.comp (by fun_prop) (fun z hz => hD z (sphere_subset_closedBall hz))).circleIntegrable'
  simp only [spectralExhaustion,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  have hh := circleAverage_fun_add (hi₁.add hi₂) hi₃
  simp only [Pi.add_apply] at hh
  rw [hh,circleAverage_add hi₁ hi₂]
  linarith

end
end IsingBulk.Joint
