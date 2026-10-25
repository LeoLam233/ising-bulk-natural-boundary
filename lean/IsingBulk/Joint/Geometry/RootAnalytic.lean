import IsingBulk.Joint.Geometry.Root
import IsingBulk.Anisotropic.RegularEdges.SmallRootAnalytic

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Filter
open scoped Topology

private theorem mem_smallRootDomain_of_quadratic {W rho : ℂ}
    (he : rho^2-2*W*rho+1=0) (hn : ‖rho‖<1) : W∈SmallRootDomain := by
  by_contra hw
  simp only [SmallRootDomain,Set.mem_ofPred_eq,not_or,not_not,not_lt] at hw
  have hW : star W=W := by apply Complex.ext <;> simp [hw.1]
  have hec := congrArg (starRingEnd ℂ) he
  simp only [map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,map_zero,starRingEnd_apply,hW] at hec
  have hr := IsingBulk.First.quadratic_root_unique he hec hn (by simpa using hn)
  have hi : rho.im=0 := by
    have hh := congrArg Complex.im hr
    simp only [Complex.star_def,Complex.conj_im] at hh
    linarith
  have hn' : |rho.re|<1 := lt_of_le_of_lt (Complex.abs_re_le_norm rho) hn
  have hreal := congrArg Complex.re he
  simp [Complex.mul_re,Complex.mul_im,hi,hw.1,pow_two] at hreal
  rcases le_or_gt 0 rho.re with hp|hp
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hw.2.1),sq_pos_of_ne_zero (by linarith [abs_lt.mp hn'] : rho.re-1≠0)]
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hp.le (show 0≤W.re+1 by linarith [hw.2.2]),
      sq_pos_of_ne_zero (by linarith [abs_lt.mp hn'] : rho.re+1≠0)]

theorem canonicalRoot_eq_of_root {K : Coupling} {q rho : ℂ}
    (hg : A K-T K*Complex.cos q≠0)
    (he : rootPolynomial K q rho=0) (hn : ‖rho‖<1) : canonicalRoot K q=rho := by
  by_cases hS : S K=0
  · simp only [canonicalRoot,ite_eq_left hS]
    have he' : 2*(A K-T K*Complex.cos q)*rho=0 := by simpa [rootPolynomial,hS] using he
    exact ((mul_eq_zero.mp he').resolve_left (mul_ne_zero (by norm_num : (2:ℂ)≠0) hg)).symm
  · have hquad : rho^2-2*((A K-T K*Complex.cos q)/S K)*rho+1=0 := by
      dsimp [rootPolynomial] at he
      field_simp
      linear_combination he
    simp only [canonicalRoot,ite_eq_right hS]
    exact smallRoot_eq_of_quadratic (mem_smallRootDomain_of_quadratic hquad hn) hquad hn

def angularGap (v : Coupling × ℂ) : ℂ := A v.1-T v.1*Complex.cos v.2

theorem angularGap_analyticAt (v : Coupling × ℂ) : AnalyticAt ℂ angularGap v := by
  have hz : AnalyticAt ℂ (fun v : Coupling × ℂ => v.1.1) v := analyticAt_fst.comp analyticAt_fst
  have hw : AnalyticAt ℂ (fun v : Coupling × ℂ => v.1.2) v := analyticAt_snd.comp analyticAt_fst
  exact ((Complex.analyticAt_cosh.comp hz).mul (Complex.analyticAt_cosh.comp hw)).sub
    ((Complex.analyticAt_sinh.comp hw).mul (Complex.analyticAt_cos.comp analyticAt_snd))

private def axisRoot (v : Coupling × ℂ) : ℂ :=
  S v.1 / (angularGap v*(1+Complex.sqrt (1-(S v.1/angularGap v)^2)))

private theorem root_from_sqrt (s g d : ℂ) (hg : g≠0) (hd : 1+d≠0)
    (hs : d^2=1-(s/g)^2) : s*(s/(g*(1+d)))^2-2*g*(s/(g*(1+d)))+s=0 := by
  have hs' : g^2*d^2=g^2-s^2 := by
    field_simp at hs
    simpa only [mul_comm] using hs
  field_simp [hg,hd]
  linear_combination s*hs'

private theorem axisRoot_polynomial (v : Coupling × ℂ) (hg : angularGap v≠0)
    (hd : 1+Complex.sqrt (1-(S v.1/angularGap v)^2)≠0) :
    rootPolynomial v.1 v.2 (axisRoot v)=0 :=
  root_from_sqrt (S v.1) (angularGap v) _ hg hd (IsingBulk.Branch.sqrt_sq _)

theorem canonicalRoot_joint_analyticAt {K : Coupling} (hK : K∉spectralSet) (q : ℝ) :
    AnalyticAt ℂ (fun v : Coupling × ℂ => canonicalRoot v.1 v.2) (K,(q:ℂ)) := by
  let v : Coupling × ℂ := (K,(q:ℂ))
  have hsa : AnalyticAt ℂ (fun w : Coupling × ℂ => S w.1) v :=
    Complex.analyticAt_sinh.comp (analyticAt_fst.comp analyticAt_fst)
  have hga : AnalyticAt ℂ angularGap v := angularGap_analyticAt v
  have hg : angularGap v≠0 := transferGap_ne_zero hK q
  by_cases hS : S K=0
  · have hsqrt : AnalyticAt ℂ Complex.sqrt (1-(S K/angularGap v)^2) := by
      rw [hS]
      simp only [zero_div,zero_pow (by decide : 2≠0),sub_zero]
      exact Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane 1 Complex.one_mem_slitPlane
    have hra : AnalyticAt ℂ (fun w : Coupling × ℂ => 1-(S w.1/angularGap w)^2) v :=
      analyticAt_const.sub ((hsa.div hga hg).pow 2)
    have hca : AnalyticAt ℂ (fun w : Coupling × ℂ => Complex.sqrt (1-(S w.1/angularGap w)^2)) v :=
      AnalyticAt.fun_comp_of_eq (f := fun w : Coupling × ℂ => 1-(S w.1/angularGap w)^2)
        (g := Complex.sqrt) hsqrt hra rfl
    have hda : AnalyticAt ℂ (fun w : Coupling × ℂ => 1+Complex.sqrt (1-(S w.1/angularGap w)^2)) v :=
      analyticAt_const.add hca
    have hd : 1+Complex.sqrt (1-(S K/angularGap v)^2)≠0 := by simp [hS]
    have ha : AnalyticAt ℂ axisRoot v := hsa.div (hga.mul hda) (mul_ne_zero hg hd)
    have hv : axisRoot v=0 := by simp [axisRoot,v,hS]
    apply ha.congr
    have hge := hga.continuousAt.eventually_ne hg
    have hde := hda.continuousAt.eventually_ne hd
    have hne := ha.continuousAt.norm.eventually_lt_const (show ‖axisRoot v‖<1 by simp [hv])
    filter_upwards [hge,hde,hne] with w hwg hwd hwn
    exact (canonicalRoot_eq_of_root hwg (axisRoot_polynomial w hwg hwd) hwn).symm
  · have hwa := (hga.div hsa hS)
    have ha : AnalyticAt ℂ (fun w : Coupling × ℂ => smallRoot (angularGap w/S w.1)) v :=
      AnalyticAt.fun_comp_of_eq (f := fun w : Coupling × ℂ => angularGap w/S w.1)
        (g := smallRoot) (smallRoot_analyticAt (transfer_mem_smallRootDomain hK hS q)) hwa rfl
    apply ha.congr
    filter_upwards [hsa.continuousAt.eventually_ne hS] with w hw
    simp only [canonicalRoot,ite_eq_right hw,angularGap]

end
end IsingBulk.Joint
