import IsingBulk.Tail.CompactLimitingGeometry
import IsingBulk.Tail.CompactRightCurvature
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The actual continued compact-right phase, before composition with real
coupled deformation bumps. Its real boundary value is exactly the arccos
phase whose strict curvature has already been proved. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def continuedPhase (W : ℂ) : ℂ := Complex.I*Complex.log (continuedRoot W)

def continuedPhaseDomain : Set ℂ :=
  continuedRootDomain ∩ continuedRoot ⁻¹' Complex.slitPlane

theorem continuedPhase_analyticAt {W : ℂ} (hW : W ∈ continuedPhaseDomain) :
    AnalyticAt ℂ continuedPhase W :=
  analyticAt_const.mul ((continuedRoot_analyticAt hW.1).clog hW.2)

theorem continuedRoot_compactRight_real (w : ℝ) (hw : |w|<1) :
    continuedRoot (w:ℂ)=interiorRoot (w:ℂ) := by
  unfold continuedRoot
  simp only [Complex.ofReal_re,not_lt.mpr (abs_lt.mp hw).2.le,ite_false]

theorem continuedPhase_real_value (w : ℝ) (hw : |w|<1) :
    continuedPhase (w:ℂ)=(Real.arccos w:ℂ) := by
  obtain ⟨hn,hi⟩ := compactRight_real_norm_im w hw
  have hre : (interiorRoot (w:ℂ)).re=w := by rw [compactRight_real_formula w hw]; simp
  have harg := Complex.arg_of_im_neg hi
  rw [hn,div_one,hre] at harg
  unfold continuedPhase
  rw [continuedRoot_compactRight_real w hw,Complex.log,hn,Real.log_one,harg]
  ring_nf
  simp

theorem compactRight_real_mem_phaseDomain (w : ℝ) (hw : |w|<1) :
    (w:ℂ) ∈ continuedPhaseDomain := by
  refine ⟨Or.inr ?_,?_⟩
  · simpa using hw
  · change continuedRoot (w:ℂ) ∈ Complex.slitPlane
    rw [continuedRoot_compactRight_real w hw]
    exact Or.inr (compactRight_real_norm_im w hw).2.ne

def compactPhaseModel (p : ℂ × ℂ × ℂ) : ℂ :=
  continuedPhase (p.1-Complex.cosh (p.2.1+p.2.2*Complex.I))

theorem compactPhaseModel_analyticAt (S θ : ℝ) (h : |S-Real.cos θ|<1) :
    AnalyticAt ℂ compactPhaseModel ((S:ℂ),0,(θ:ℂ)) := by
  have he : (S:ℂ)-Complex.cosh ((0:ℂ)+(θ:ℂ)*Complex.I)=((S-Real.cos θ:ℝ):ℂ) := by
    simp [Complex.cosh_mul_I,← Complex.ofReal_cos]
  have hh := continuedPhase_analyticAt (compactRight_real_mem_phaseDomain (S-Real.cos θ) h)
  rw [← he] at hh
  exact hh.comp (f := fun p : ℂ × ℂ × ℂ => p.1-Complex.cosh (p.2.1+p.2.2*Complex.I))
    (by fun_prop)

theorem compactPhaseModel_limiting (S θ : ℝ) (h : |S-Real.cos θ|<1) :
    compactPhaseModel ((S:ℂ),0,(θ:ℂ))=(compactRightPhase S θ:ℂ) := by
  unfold compactPhaseModel compactRightPhase
  rw [show (S:ℂ)-Complex.cosh ((0:ℂ)+(θ:ℂ)*Complex.I)=((S-Real.cos θ:ℝ):ℂ) by
    simp [Complex.cosh_mul_I,← Complex.ofReal_cos]]
  exact continuedPhase_real_value _ h

end
end IsingBulk.Tail
