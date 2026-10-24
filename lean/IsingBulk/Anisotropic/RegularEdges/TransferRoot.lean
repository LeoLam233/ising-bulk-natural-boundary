import IsingBulk.Anisotropic.RegularEdges.SmallRootAnalytic
import IsingBulk.Anisotropic.Geometry.Definitions
import IsingBulk.Anisotropic.FormFactors.RealDispersion
import IsingBulk.Anisotropic.FormFactors.JointAnalytic

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First FormFactors Set

def transferW (lam : ℝ) (z q : ℂ) : ℂ :=
  (spectralA lam z-spectralT lam z*Complex.cos q)/spectralS z

def transferRoot (lam : ℝ) (z q : ℂ) : ℂ := smallRoot (transferW lam z q)

theorem transferW_mem_smallRootDomain {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) (q : ℝ) :
    transferW lam z (q:ℂ)∈SmallRootDomain := by
  by_contra hh
  simp only [SmallRootDomain,mem_ofPred_eq,not_or,not_ne_iff,not_lt] at hh
  have he : transferW lam z (q:ℂ)=((transferW lam z (q:ℂ)).re:ℂ) := by
    apply Complex.ext <;> simp [hh.1]
  apply hz
  refine ⟨(transferW lam z (q:ℂ)).re,⟨hh.2.2,hh.2.1⟩,Real.cos q,
    ⟨Real.neg_one_le_cos q,Real.cos_le_one q⟩,?_⟩
  unfold transferW at he
  rw [← Complex.ofReal_cos] at he
  have hm := (div_eq_iff hS).mp he
  change spectralA lam z = spectralS z * ((transferW lam z (q:ℂ)).re:ℂ) + spectralT lam z*(Real.cos q:ℂ)
  unfold transferW
  rw [← Complex.ofReal_cos]
  linear_combination hm

theorem transferRoot_bounds {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) (q : ℝ) :
    transferRoot lam z (q:ℂ)≠0 ∧ ‖transferRoot lam z (q:ℂ)‖<1 :=
  ⟨smallRoot_ne_zero (transferW_mem_smallRootDomain hz hS q),
    (smallRoot_spec (transferW_mem_smallRootDomain hz hS q)).2⟩

set_option maxHeartbeats 300000 in
theorem transferRoot_joint_analyticAt {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) (q : ℝ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => transferRoot lam p.1 p.2) (z,(q:ℂ)) := by
  unfold transferRoot
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ => transferW lam p.1 p.2) (z,(q:ℂ)) := by
    unfold transferW spectralA spectralS spectralT
    have hs : Complex.sinh z≠0 := hS
    have dz : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (z,(q:ℂ)) := analyticAt_fst
    have dq : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (z,(q:ℂ)) := analyticAt_snd
    exact (((Complex.analyticAt_cosh.comp dz).mul (Complex.analyticAt_cosh.comp (analyticAt_const.mul dz))).sub
      ((Complex.analyticAt_sinh.comp (analyticAt_const.mul dz)).mul (Complex.analyticAt_cos.comp dq))).div
      (Complex.analyticAt_sinh.comp dz) hs
  exact AnalyticAt.fun_comp_of_eq
    (f := fun p : ℂ × ℂ => transferW lam p.1 p.2) (g := smallRoot)
    (smallRoot_analyticAt (transferW_mem_smallRootDomain hz hS q)) hA rfl

end
end IsingBulk.Anisotropic.RegularEdges
