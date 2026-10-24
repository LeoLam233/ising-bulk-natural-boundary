import IsingBulk.Anisotropic.RegularEdges.RootGap
import IsingBulk.Tail.CompactRightPhaseJets
import IsingBulk.First.AnalyticQuadraticLimit

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set Filter
open scoped Topology

/-- The genuine continued lower root at an interior real edge value. -/
theorem continuedRoot_real_formula {b : ℝ} (hb : |b|<1) :
    continuedRoot (b:ℂ)=(b:ℂ)-Complex.I*(Real.sqrt (1-b^2):ℂ) := by
  rw [continuedRoot_compactRight_real b hb]
  exact compactRight_real_formula b hb

/-- Differentiate the actual quadratic equation on its analytic sheet. -/
theorem continuedRoot_quadratic_derivative {w : ℂ} (hw : w∈continuedRootDomain) :
    2*(continuedRoot w-w)*deriv continuedRoot w=2*continuedRoot w := by
  have hr := (continuedRoot_analyticAt hw).differentiableAt.hasDerivAt
  have hh := ((hr.pow 2).sub (((hasDerivAt_id w).const_mul 2).mul hr)).add_const 1
  have he : (fun z => continuedRoot z^2-2*z*continuedRoot z+1)=(fun _ : ℂ => 0) :=
    funext continuedRoot_quadratic
  have hd := hh.deriv
  change deriv (fun z => continuedRoot z^2-2*z*continuedRoot z+1) w = _ at hd
  rw [he,deriv_const] at hd
  simp only [id_eq] at hd
  linear_combination -hd

theorem continuedRoot_hasDerivAt_real {b : ℝ} (hb : |b|<1) :
    HasDerivAt continuedRoot (Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ)) (b:ℂ) := by
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hs0 : (Real.sqrt (1-b^2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hw : (b:ℂ)∈continuedRootDomain := Or.inr (by simpa using hb)
  have hd := continuedRoot_quadratic_derivative hw
  have hv := continuedRoot_real_formula hb
  have he : deriv continuedRoot (b:ℂ)=Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ) := by
    apply (eq_div_iff hs0).mpr
    rw [hv] at hd
    rw [hv]
    linear_combination (norm := skip) Complex.I/2*hd
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [←he]
  exact (continuedRoot_analyticAt hw).differentiableAt.hasDerivAt

/-- The full parameter derivative of the actual local root at the collision. -/
theorem edgeParamRoot_parameter_hasDerivAt {b : ℝ} (hb : |b|<1) (B : ℂ→ℂ) :
    HasDerivAt (fun u => edgeParamRoot b B u 0)
      (Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ)) 0 := by
  have he : (fun u => edgeParamRoot b B u 0)=(fun u => continuedRoot ((b:ℂ)+u)) := by
    funext u
    simp [edgeParamRoot,edgeParamW]
  rw [he]
  have hr : HasDerivAt continuedRoot
      (Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ)) ((b:ℂ)+0) := by
    simpa using continuedRoot_hasDerivAt_real hb
  simpa using! hr.comp 0 ((hasDerivAt_id (0:ℂ)).const_add (b:ℂ))

/-- The angular cosine contributes its true quadratic coefficient, not a formal series. -/
theorem angular_cosine_quadratic_limit (q : ℝ) :
    Tendsto (fun t : ℝ => (1-Complex.cos ((t:ℂ)*(q:ℂ)))/(t:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((q:ℂ)^2/2)) := by
  apply analytic_quadratic_quotient_limit_real (f := fun t : ℂ => 1-Complex.cos (t*(q:ℂ)))
  · exact analyticAt_const.sub (Complex.analyticAt_cos.comp (analyticAt_id.mul analyticAt_const))
  · simp
  · have hd := (((hasDerivAt_id (0:ℂ)).mul_const (q:ℂ)).ccos).const_sub 1
    simpa only [id_eq,zero_mul,Complex.sin_zero,neg_zero] using hd.deriv
  · have he : deriv (fun t : ℂ => 1-Complex.cos (t*(q:ℂ)))=
        (fun t => Complex.sin (t*(q:ℂ))*(q:ℂ)) := by
      funext t
      have hd := (((hasDerivAt_id t).mul_const (q:ℂ)).ccos).const_sub 1
      simpa only [id_eq,one_mul,neg_mul,neg_neg] using hd.deriv
    rw [he]
    have hd := ((((hasDerivAt_id (0:ℂ)).mul_const (q:ℂ)).csin).mul_const (q:ℂ)).deriv
    calc
      _ = (q:ℂ)*(q:ℂ) := by simpa only [id_eq,zero_mul,Complex.cos_zero,one_mul] using hd
      _ = _ := by ring

end
end IsingBulk.Anisotropic.RegularEdges
