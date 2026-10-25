import IsingBulk.Joint.RegularEdges.PhysicalIdentity
import IsingBulk.Joint.FormFactors.NormalConvergence
import IsingBulk.Joint.Geometry.Root

/-! Exact removable coordinate-axis restriction of the same complete joint
function. This is not inferred from ambient boundary behavior. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter
open scoped Topology BigOperators

@[simp] theorem p_axis (z : ℂ) : p (z,0) = 0 := by simp [p,T]

@[simp] theorem highPrefactor_axis (z : ℂ) : highPrefactor (z,0)=1 := by
  simp [highPrefactor,fourthRoot]

theorem highNormalizedBulk_axis_eq_oneParticle (z : ℂ) :
    highNormalizedBulk (z,0)=unscaledFullCoefficient 1 (z,0) := by
  unfold highNormalizedBulk
  rw [highPrefactor_axis,one_mul,tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem physicalAngular_zero (K : Coupling) :
    Negative.unscaledAngularCoefficient 0 K =
      (S K)⁻¹ * (2*Negative.transferRoot K 0/(1-Negative.transferRoot K 0^2)) *
      ((1+Negative.transferRoot K 0)/(1-Negative.transferRoot K 0)) := by
  simp [Negative.unscaledAngularCoefficient,First.multiAngleIntegral,
    Negative.complexAngularDensity,Negative.complexAngularWeight,
    HT.Contour.physicalDependentAngles,Fin.snoc_zero]
  simp [Finset.filter_singleton]

theorem oneParticle_formula {K : Coupling} (hK : K∈highDomain) (hS : S K≠0) :
    unscaledFullCoefficient 1 K = (A K-S K-T K)⁻¹ := by
  have hc := highDomain_subset_spectralComplement hK
  rw [show 1=0+1 by rfl,RegularEdges.fullCoefficient_eq_physicalAngular_high 0 hK hS,
    physicalAngular_zero]
  let r := Negative.transferRoot K 0
  have hr : ‖r‖<1 := by simpa [r] using (Negative.transferRoot_bounds hc hS 0).2
  have h1 : 1-r ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne norm (by simpa using ne_of_lt hr)).symm
  have h2 : 1-r^2 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    rw [norm_one,norm_pow] at hn
    have hh := pow_lt_one₀ (norm_nonneg r) hr (by decide : 2 ≠ 0)
    linarith
  have hd : A K-S K-T K ≠ 0 := by
    intro he
    apply hc
    refine ⟨1,by norm_num,1,by norm_num,?_⟩
    push_cast
    linear_combination he
  have he : S K*r^2-2*(A K-T K)*r+S K=0 := by
    have hh := (canonicalRoot_spec hc 0).1
    simpa only [canonicalRoot,ite_eq_right hS,rootPolynomial,Complex.ofReal_zero,
      Complex.cos_zero,mul_one,r,Negative.transferRoot,Negative.transferW] using hh
  change (S K)⁻¹*(2*r/(1-r^2))*((1+r)/(1-r))=(A K-S K-T K)⁻¹
  field_simp [hS,h1,h2,hd]
  linear_combination (-(1+r))*he

theorem highNormalizedBulk_axis_nonzero {z : ℂ} (hz : |z.im| < Real.pi/2) (hz0 : z≠0) :
    highNormalizedBulk (z,0)=Complex.exp z := by
  have hK := axis_mem_highDomain hz
  rw [highNormalizedBulk_axis_eq_oneParticle,oneParticle_formula hK
    (fun hs => hz0 ((S_eq_zero_iff_fst_eq_zero hK).mp hs))]
  simp only [A,S,T,Complex.cosh_zero,Complex.sinh_zero,mul_one,sub_zero,
    Complex.cosh_sub_sinh,Complex.exp_neg,inv_inv]

/-- The entire chain response is the restriction of the actual joint germ,
including at the doubly decoupled origin. -/
theorem highNormalizedBulk_axis {z : ℂ} (hz : |z.im| < Real.pi/2) :
    highNormalizedBulk (z,0)=Complex.exp z := by
  let U : Set ℂ := {z | |z.im| < Real.pi/2}
  have hU : IsOpen U := isOpen_lt (Complex.continuous_im.abs) continuous_const
  have hUc : IsPreconnected U := by
    have he : U = {z : ℂ | -(Real.pi/2)<z.im} ∩ {z : ℂ | z.im<Real.pi/2} := by
      ext z; simp [U,abs_lt]
    rw [he]
    exact ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => highNormalizedBulk (z,0)) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((highNormalizedBulk_contDiffAt 1 (axis_mem_highDomain hz)).differentiableAt_one.comp z
      (show DifferentiableAt ℂ (fun z : ℂ => (z,(0:ℂ))) z from
        differentiableAt_id.prodMk (differentiableAt_const (0:ℂ)))).differentiableWithinAt
  have he := Anisotropic.analytic_eqOn_of_real_interval hf
    (fun _ _ => analyticAt_cexp) hUc (by norm_num : (0:ℝ)<1)
    (fun x _ => by change |(x:ℂ).im| < Real.pi/2; simp; positivity)
    (fun x hx => highNormalizedBulk_axis_nonzero
      (by simp; positivity) (Complex.ofReal_ne_zero.mpr hx.1.ne'))
  exact he hz

@[simp] theorem highNormalizedBulk_zero : highNormalizedBulk (0,0)=1 := by
  simpa using highNormalizedBulk_axis (z := 0) (by simp; positivity)

end
end IsingBulk.Joint.FormFactors
