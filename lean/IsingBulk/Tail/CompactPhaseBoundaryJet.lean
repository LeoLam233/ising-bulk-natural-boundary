import IsingBulk.Tail.CompactRealPhaseJets
import IsingBulk.Tail.CompactSecondDerivative
import Mathlib.Analysis.Complex.RealDeriv

namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology ContDiff

lemma compactPhaseModel_boundary_second_unit (S theta : ℝ) (h : |S-Real.cos theta|<1) :
    iteratedFDeriv ℝ 2 compactPhaseModel ((S:ℂ),0,(theta:ℂ))
      (fun _ => ((0:ℂ),0,1)) = ((deriv (deriv (compactRightPhase S)) theta : ℝ) : ℂ) := by
  let p : ℝ → ℂ × ℂ × ℂ := fun t => ((S:ℂ),0,(t:ℂ))
  have hp : ContDiff ℝ ∞ p :=
    contDiff_const.prodMk (contDiff_const.prodMk Complex.ofRealCLM.contDiff)
  have hpd : deriv p = (fun _ => ((0:ℂ),0,1)) := by
    funext t
    exact (((hasDerivAt_const t (S:ℂ)).prodMk
      ((hasDerivAt_const t (0:ℂ)).prodMk Complex.ofRealCLM.hasDerivAt)).deriv)
  have hpdd : deriv (deriv p) = (fun _ => 0) := by rw [hpd]; funext t; simp
  have hf : ContDiffAt ℝ 2 compactPhaseModel (p theta) :=
    ((compactPhaseModel_analyticAt S theta h).contDiffAt :
      ContDiffAt ℂ 2 compactPhaseModel (p theta)).restrict_scalars ℝ
  have hc := second_derivative_comp_curve hf ((hp.of_le (by simp)).contDiffAt)
  rw [hpdd,hpd] at hc
  simp only [map_zero,add_zero] at hc
  have hnear : ∀ᶠ t in 𝓝 theta, |S-Real.cos t|<1 :=
    (show Continuous (fun t : ℝ => |S-Real.cos t|) by fun_prop).continuousAt.eventually
      (gt_mem_nhds h)
  have he : (fun t => compactPhaseModel (p t)) =ᶠ[𝓝 theta]
      (fun t => (compactRightPhase S t : ℂ)) := by
    filter_upwards [hnear] with t ht
    exact compactPhaseModel_limiting S t ht
  have hd : deriv (fun t => (compactRightPhase S t : ℂ)) =ᶠ[𝓝 theta]
      (fun t => ((deriv (compactRightPhase S) t : ℝ) : ℂ)) := by
    filter_upwards [hnear] with t ht
    have hh := (compactRightPhase_hasDerivAt S t ht).ofReal_comp.deriv
    rw [← (compactRightPhase_hasDerivAt S t ht).deriv] at hh
    exact hh
  have hs := (compactRightPhase_second_hasDerivAt S theta h).ofReal_comp.deriv
  rw [← (compactRightPhase_second_hasDerivAt S theta h).deriv] at hs
  exact hc.symm.trans ((he.deriv.deriv_eq).trans (hd.deriv_eq.trans hs))

lemma compactPhaseModel_boundary_second (S theta w : ℝ) (h : |S-Real.cos theta|<1) :
    iteratedFDeriv ℝ 2 compactPhaseModel ((S:ℂ),0,(theta:ℂ))
      (fun _ => ((0:ℂ),0,(w:ℂ))) =
      (deriv (deriv (compactRightPhase S)) theta * w^2 : ℝ) := by
  have hm := (iteratedFDeriv ℝ 2 compactPhaseModel ((S:ℂ),0,(theta:ℂ))).map_smul_univ
    (fun _ : Fin 2 => w) (fun _ : Fin 2 => ((0:ℂ),0,1))
  have he : (fun _ : Fin 2 => w • (((0:ℂ),0,1) : ℂ × ℂ × ℂ)) =
      (fun _ => ((0:ℂ),0,(w:ℂ))) := by ext i <;> simp [Complex.real_smul]
  rw [he,compactPhaseModel_boundary_second_unit S theta h] at hm
  simpa [Complex.real_smul,mul_comm] using hm

end
end IsingBulk.Tail
