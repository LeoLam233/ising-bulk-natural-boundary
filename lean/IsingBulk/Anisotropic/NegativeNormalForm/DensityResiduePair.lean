import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueScalar

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 800000

theorem halfSineSlope_even (z : ℂ) : halfSineSlope (-z)=halfSineSlope z := by
  by_cases hz : z=0
  · simp [hz]
  apply mul_left_cancel₀ (neg_ne_zero.mpr hz)
  rw [halfSineSlope_mul,neg_div,Complex.sin_neg,←halfSineSlope_mul]
  ring

theorem halfSineSlope_relative_quadratic :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ z : ℂ, ‖z‖<r →
      ‖2*halfSineSlope z‖≤2 ∧ ‖2*halfSineSlope z-1‖≤L*‖z‖^2 := by
  have ha : AnalyticAt ℂ (fun p : ScalarTriple => 2*halfSineSlope p.2.2) 0 :=
    analyticAt_const.mul (halfSineSlope_analyticAt.fun_comp_of_eq
      (analyticAt_snd.comp analyticAt_snd) rfl)
  obtain ⟨r,L,hr,hL,hquad⟩ := analytic_even_axis_quadratic_control _ ha
    (fun _ v => by rw [halfSineSlope_even])
  have he : ∀ᶠ z : ℂ in 𝓝 0, ‖2*halfSineSlope z‖<2 := by
    apply (continuousAt_const.mul halfSineSlope_analyticAt.continuousAt).norm.eventually_lt continuousAt_const
    norm_num
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,L,lt_min hr hs,hL,?_⟩
  intro z hz
  refine ⟨(hball (by simpa using hz.trans_le (min_le_right _ _))).le,?_⟩
  have hh := hquad ((0:ℂ),(0,z)) (by simpa using hz.trans_le (min_le_left _ _))
  simpa [pow_two,mul_assoc] using hh

def residuePairDenominatorRatio (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (t d x y : ℂ) : ℂ :=
  ((Real.sin phi:ℂ)*Complex.I)/pairDenominator B phi hphi d t x y

theorem sinh_pair_relative_control (phi : ℝ) (hphi : Real.sin phi≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ a b : ℂ,
      ‖a-(phi:ℂ)*Complex.I‖<r → ‖b-(phi:ℂ)*Complex.I‖<r →
      ‖((Real.sin phi:ℂ)*Complex.I)/Complex.sinh ((a+b)/2)‖≤2 ∧
      ‖((Real.sin phi:ℂ)*Complex.I)/Complex.sinh ((a+b)/2)-1‖≤
        L*(‖a-(phi:ℂ)*Complex.I‖+‖b-(phi:ℂ)*Complex.I‖) := by
  let c : ℂ := (phi:ℂ)*Complex.I
  let f : ℂ × ℂ → ℂ := fun p => ((Real.sin phi:ℂ)*Complex.I)/Complex.sinh (c+(p.1+p.2)/2)
  have hs : Complex.sinh c=(Real.sin phi:ℂ)*Complex.I := by simp [c,Complex.sinh_mul_I,←Complex.ofReal_sin]
  have hn : (Real.sin phi:ℂ)*Complex.I≠0 := mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  have hf0 : f 0=1 := by
    change ((Real.sin phi:ℂ)*Complex.I)/Complex.sinh (c+(0+0)/2)=1
    simp only [add_zero,zero_div,hs,div_self hn]
  have hf : AnalyticAt ℂ f 0 := analyticAt_const.div
    (Complex.analyticAt_sinh.comp (analyticAt_const.add ((analyticAt_fst.add analyticAt_snd).div_const))) (by simpa [hs] using hn)
  obtain ⟨r,L,hr,hL,_ha,hLip⟩ := analytic_uniform_lipschitz hf
  have he : ∀ᶠ p in 𝓝 (0:ℂ × ℂ), ‖f p‖<2 := by
    apply hf.continuousAt.norm.eventually_lt continuousAt_const
    simp [hf0]
  obtain ⟨s,hs₀,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,L,lt_min hr hs₀,hL,?_⟩
  intro a b ha hb
  have hp : ‖(a-c,b-c)‖<min r s := max_lt ha hb
  have hid : c+((a-c)+(b-c))/2=(a+b)/2 := by ring
  have hnorm : ‖f (a-c,b-c)‖≤2 := (hball (by simpa using hp.trans_le (min_le_right _ _))).le
  have h := hLip (a-c,b-c) 0 (hp.trans_le (min_le_left _ _)) (by simpa using hr)
  rw [hf0,sub_zero] at h
  have hh : ‖(a-c,b-c)‖≤‖a-c‖+‖b-c‖ :=
    max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  exact ⟨by simpa [f,hid] using hnorm,by simpa [f,hid] using h.trans (mul_le_mul_of_nonneg_left hh hL.le)⟩


/-- The exact normalized squared pair factor, including the sine slope. -/
def residuePairRatio (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (t d x y : ℂ) : ℂ :=
  (2*halfSineSlope (x-y)*residuePairDenominatorRatio B phi hphi t d x y)^2

theorem square_product_relative_error (a b : ℂ) (ha : ‖a‖≤2) (hb : ‖b‖≤2) :
    ‖(a*b)^2-1‖≤5*(2*‖b-1‖+‖a-1‖) := by
  have hmul : ‖a*b-1‖≤2*‖b-1‖+‖a-1‖ := by
    rw [show a*b-1=a*(b-1)+(a-1) by ring]
    exact (norm_add_le _ _).trans (by rw [norm_mul]; gcongr)
  have hplus : ‖a*b+1‖≤5 := by
    have h := norm_add_le (a*b) (1:ℂ)
    rw [norm_mul,norm_one] at h
    have hab : ‖a‖*‖b‖≤4 := by nlinarith [norm_nonneg a,norm_nonneg b]
    linarith
  rw [show (a*b)^2-1=(a*b-1)*(a*b+1) by ring,norm_mul]
  have h := mul_le_mul hmul hplus (norm_nonneg _) (by positivity : 0≤2*‖b-1‖+‖a-1‖)
  nlinarith

/-- Complete actual pair-factor estimate, uniform before the particle number,
valid at coincidences as well as off every diagonal. -/
theorem residuePairRatio_control (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t d x y : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r → ‖y‖<r →
      ‖residuePairRatio B phi hphi t d x y-1‖ ≤
        L*(‖t-(1-Complex.cos d)‖+‖d‖*(‖x‖+‖y‖)+‖x‖^2+‖y‖^2) := by
  obtain ⟨rp,P,hrp,hP,hphase⟩ := negativePhase_moving_center_control B phi hphi hB
  obtain ⟨rs,M,hrs,hM,hsinh⟩ := sinh_pair_relative_control phi hphi
  obtain ⟨rh,H,hrh,hH,hhalf⟩ := halfSineSlope_relative_quadratic
  have hzero : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_center B phi hphi 0
  have he : ∀ᶠ p : ScalarTriple in 𝓝 0,
      ‖negativePhase B phi hphi p.1 (p.2.1+p.2.2)-(phi:ℂ)*Complex.I‖<rs := by
    apply ((negativePhase_moving_analyticAt B phi hphi hB).continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
    simpa [hzero] using hrs
  obtain ⟨rg,hrg,hgamma⟩ := Metric.mem_nhds_iff.mp he
  let r := min rp (min rg (rh/4))
  have hr : 0<r := lt_min hrp (lt_min hrg (by positivity))
  refine ⟨r,20*M*P+10*H,hr,by positivity,?_⟩
  intro t d x y ht ht₀ hd hx hy
  have hrp' : r≤rp := min_le_left _ _
  have hrg' : r≤rg := (min_le_right _ _).trans (min_le_left _ _)
  have hrh' : r≤rh/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hpx := hphase t d x (ht.trans_le hrp') (ht₀.trans_le hrp') (hd.trans_le hrp') (hx.trans_le hrp')
  have hpy := hphase t d y (ht.trans_le hrp') (ht₀.trans_le hrp') (hd.trans_le hrp') (hy.trans_le hrp')
  have hgx := hgamma (show (t,(d,x))∈ball (0:ScalarTriple) rg by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def] using (max_lt ht (max_lt hd hx)).trans_le hrg')
  have hgy := hgamma (show (t,(d,y))∈ball (0:ScalarTriple) rg by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def] using (max_lt ht (max_lt hd hy)).trans_le hrg')
  obtain ⟨hbn,hbe⟩ := hsinh _ _ hgx hgy
  change ‖residuePairDenominatorRatio B phi hphi t d x y‖≤2 at hbn
  change ‖residuePairDenominatorRatio B phi hphi t d x y-1‖≤_ at hbe
  have hxy : ‖x-y‖<rh := by
    have hh := norm_sub_le x y
    have hx' := hx.trans_le hrh'
    have hy' := hy.trans_le hrh'
    linarith
  obtain ⟨han,hae⟩ := hhalf (x-y) hxy
  let E := ‖t-(1-Complex.cos d)‖+‖d‖*(‖x‖+‖y‖)+‖x‖^2+‖y‖^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hsum : ‖negativePhase B phi hphi t (d+x)-(phi:ℂ)*Complex.I‖+
      ‖negativePhase B phi hphi t (d+y)-(phi:ℂ)*Complex.I‖≤2*P*E := by
    dsimp [E]
    nlinarith [mul_nonneg hP.le (norm_nonneg (t-(1-Complex.cos d))),
      mul_nonneg hP.le (mul_nonneg (norm_nonneg d) (add_nonneg (norm_nonneg x) (norm_nonneg y))),
      mul_nonneg hP.le (sq_nonneg ‖x‖),mul_nonneg hP.le (sq_nonneg ‖y‖)]
  have hbe' : ‖residuePairDenominatorRatio B phi hphi t d x y-1‖≤2*M*P*E := by
    have hh := hbe.trans (mul_le_mul_of_nonneg_left hsum hM.le)
    nlinarith
  have hxy2 : ‖x-y‖^2≤2*(‖x‖^2+‖y‖^2) := by
    have h := norm_sub_le x y
    nlinarith [sq_nonneg (‖x‖-‖y‖),norm_nonneg (x-y),norm_nonneg x,norm_nonneg y]
  have hae' : ‖2*halfSineSlope (x-y)-1‖≤2*H*E := by
    have hh := hae.trans (mul_le_mul_of_nonneg_left hxy2 hH.le)
    have he : ‖x‖^2+‖y‖^2≤E := by
      dsimp [E]
      nlinarith [norm_nonneg (t-(1-Complex.cos d)),mul_nonneg (norm_nonneg d) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
    nlinarith [mul_le_mul_of_nonneg_left he hH.le]
  have hfinal := square_product_relative_error _ _ han hbn
  change ‖residuePairRatio B phi hphi t d x y-1‖≤_ at hfinal
  nlinarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
