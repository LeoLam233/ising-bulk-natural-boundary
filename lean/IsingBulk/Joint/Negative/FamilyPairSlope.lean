import IsingBulk.Joint.Negative.FamilyAngularDerivative
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarPairSlope
import IsingBulk.Anisotropic.NegativeNormalForm.HadamardFullDomain

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1000000

theorem compact_family_pair_slope (S : ScalarTriple × E→ℂ)
    {P : Set E} (hP : IsCompact P) (hS : ∀eta∈P,AnalyticAt ℂ S (0,eta))
    (heven : ∀eta∈P,∀t v : ℂ,S ((t,(0,-v)),eta)=S ((t,(0,v)),eta)) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈P,∀t d x y : ℂ,
      ‖t‖<r → ‖d‖<r → ‖x‖<r → ‖y‖<r →
      S ((t,(d,x)),eta)-S ((t,(d,y)),eta)=
        (x-y)*scalarPairSlope (fun p=>S (p,eta)) ((t,(d,y)),x-y) ∧
      ‖scalarPairSlope (fun p=>S (p,eta)) ((t,(d,y)),x-y)‖≤L*(‖d‖+‖x‖+‖y‖) := by
  obtain ⟨r0,L,hr0,hL,hder⟩ := compact_family_angular_derivative S hP hS heven
  obtain ⟨r1,M,hr1,_hM,ha⟩ := compact_analytic_uniform_bound S hP hS
  let r := min r0 r1/4
  have hr : 0<r := div_pos (lt_min hr0 hr1) (by norm_num)
  have hr0' : 4*r≤r0 := by dsimp [r]; linarith [min_le_left r0 r1]
  have hr1' : 4*r≤r1 := by dsimp [r]; linarith [min_le_right r0 r1]
  refine ⟨r,2*L,hr,by positivity,?_⟩
  intro eta heta t d x y ht hd hx hy
  let f : ScalarTriple × ℂ→ℂ := fun q=>S ((q.1.1,(q.1.2.1,q.1.2.2+q.2)),eta)
  have hsegment (s : ℝ) (hs : s∈Icc 0 1) : ‖y+(s:ℂ)*(x-y)‖≤‖x‖+2*‖y‖ := by
    have hsm : ‖(s:ℂ)*(x-y)‖≤‖x-y‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    linarith [norm_add_le y ((s:ℂ)*(x-y)),norm_sub_le x y]
  have hinput (s : ℝ) (hs : s∈Icc 0 1) : ‖(t,(d,y+(s:ℂ)*(x-y)))‖<min r0 r1 := by
    change max ‖t‖ (max ‖d‖ ‖y+(s:ℂ)*(x-y)‖)<min r0 r1
    have hmin : 4*r=min r0 r1 := by dsimp [r]; ring
    rw [←hmin]
    exact max_lt (by linarith) (max_lt (by linarith) (by linarith [hsegment s hs]))
  have hlocal (s : ℝ) (hs : s∈Icc 0 1) : AnalyticAt ℂ f ((t,(d,y)),(s:ℂ)*(x-y)) :=
    ((ha eta heta (t,(d,y+(s:ℂ)*(x-y))) ((hinput s hs).trans_le (min_le_right _ _))).1).comp
      (f:=fun q : ScalarTriple × ℂ=>((q.1.1,(q.1.2.1,q.1.2.2+q.2)),eta))
      (((analyticAt_fst.comp analyticAt_fst).prod
        ((analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)).prod
          ((analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)).add analyticAt_snd))).prod analyticAt_const)
  constructor
  · have hh := coordinateHadamard_identity_on_segment (f:=f) ((t,(d,y)),x-y)
      (fun s hs=>by simpa only [coordinateContraction_apply] using hlocal s hs)
    simpa only [f,add_zero,show y+(x-y)=x by ring,scalarPairSlope] using hh
  · change ‖∫s : ℝ in Icc 0 1,fderiv ℂ f (coordinateContraction s ((t,(d,y)),x-y)) (0,1)‖≤_
    have hb (s : ℝ) (hs : s∈Icc 0 1) :
        ‖fderiv ℂ f (coordinateContraction s ((t,(d,y)),x-y)) (0,1)‖≤2*L*(‖d‖+‖x‖+‖y‖) := by
      have hfull := (hlocal s hs).differentiableAt.hasFDerivAt.comp_hasDerivAt ((s:ℂ)*(x-y))
        ((hasDerivAt_const ((s:ℂ)*(x-y)) (t,(d,y))).prodMk (hasDerivAt_id ((s:ℂ)*(x-y))))
      have hpart : AnalyticAt ℂ (fun v=>S ((t,(d,v)),eta)) (y+(s:ℂ)*(x-y)) :=
        ((ha eta heta _ ((hinput s hs).trans_le (min_le_right _ _))).1).comp
          (f:=fun v : ℂ=>((t,(d,v)),eta))
          ((analyticAt_const.prod (analyticAt_const.prod analyticAt_id)).prod analyticAt_const)
      have hshift := hpart.differentiableAt.hasDerivAt.comp ((s:ℂ)*(x-y))
        ((hasDerivAt_const ((s:ℂ)*(x-y)) y).add (hasDerivAt_id ((s:ℂ)*(x-y))))
      have heval := hfull.unique hshift
      simp only [zero_add,mul_one] at heval
      simp only [coordinateContraction_apply]
      rw [heval]
      have hh := hder eta heta (t,(d,y+(s:ℂ)*(x-y))) ((hinput s hs).trans_le (min_le_left _ _))
      apply hh.trans
      have hm := mul_le_mul_of_nonneg_left (hsegment s hs) hL.le
      nlinarith [mul_nonneg hL.le (norm_nonneg d),mul_nonneg hL.le (norm_nonneg x)]
    simpa only [Real.volume_real_Icc_of_le zero_le_one,sub_zero,mul_one] using
      norm_setIntegral_le_of_norm_le_const (μ:=(volume:Measure ℝ)) isCompact_Icc.measure_lt_top hb

end
end IsingBulk.Joint.Negative
