import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianLinear
import Mathlib.Analysis.Complex.Schwarz

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

/-- A second-order Carathéodory estimate proved by the Cayley transform and
Schwarz's lemma. Only a one-sided real-part bound is needed. -/
theorem analytic_re_bound_quadratic {f : ℂ→ℂ} {R M : ℝ} (hR : 0<R) (hM : 0<M)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hf0 : f 0=0) (hd0 : deriv f 0=0)
    (hRe : ∀w∈ball 0 R,(f w).re≤M) {z : ℂ} (hz : ‖z‖≤R/2) :
    ‖f z‖≤4*M*(‖z‖/R)^2 := by
  let g : ℂ→ℂ := fun w => f w/((2*M:ℝ)-f w)
  have hn (w : ℂ) (hw : w∈ball 0 R) : (2*M:ℂ)-f w≠0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [Complex.sub_re] at hh
    linarith [hRe w hw]
  have hg : AnalyticOnNhd ℂ g (ball 0 R) := fun w hw =>
    (hf w hw).div (analyticAt_const.sub (hf w hw)) (by simpa using hn w hw)
  have hg0 : g 0=0 := by simp [g,hf0]
  have hnorm (w : ℂ) (hw : w∈ball 0 R) : ‖g w‖≤1 := by
    have hs : ‖f w‖≤‖(2*M:ℂ)-f w‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply]
      nlinarith [hRe w hw]
    dsimp [g]
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr (by simpa using hn w hw))).mpr (by simpa using hs)
  have h0 : (0:ℂ)∈ball 0 R := mem_ball_self hR
  have hdf : HasDerivAt f 0 0 := by simpa only [hd0] using (hf 0 h0).differentiableAt.hasDerivAt
  have hdg : HasDerivAt g 0 0 := by
    have hh := hdf.div ((hasDerivAt_const (0:ℂ) ((2*M:ℝ):ℂ)).sub hdf) (by simpa using hn 0 h0)
    simpa [g,hf0] using! hh
  have ho : (fun w => g w-g 0)=o[𝓝 (0:ℂ)] (fun w => (w-0)^1) := by
    simpa using hdg.isLittleO
  have hzR : z∈ball (0:ℂ) R := by simpa using (hz.trans_lt (by linarith : R/2<R))
  have ho' : (fun w => g w-g 0)=o[𝓝 (0:ℂ)] (fun w => ‖w-0‖^1) := by
    simpa using ho.norm_right
  have hgs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hg.differentiableOn
    (fun w hw => by simpa only [mem_closedBall,dist_eq_norm,hg0,sub_zero] using hnorm w hw) ho' hzR
  simp only [dist_eq_norm,hg0,sub_zero,one_mul] at hgs
  have hratio : 0≤‖z‖/R := div_nonneg (norm_nonneg _) hR.le
  have hratio2 : ‖z‖/R≤1/2 := (div_le_iff₀ hR).mpr (by linarith)
  have hhalf : ‖g z‖≤1/2 := by nlinarith
  have hid : f z=(2*M:ℂ)*g z-g z*f z := by
    dsimp [g]
    field_simp [hn z hzR]
    push_cast
    ring
  have ht := norm_sub_le ((2*M:ℂ)*g z) (g z*f z)
  rw [←hid] at ht
  norm_num [norm_mul,abs_of_pos hM] at ht
  nlinarith [norm_nonneg (f z),norm_nonneg (g z)]

end
end IsingBulk.Anisotropic.NegativeNormalForm
