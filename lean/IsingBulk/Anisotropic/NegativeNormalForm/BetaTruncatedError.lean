import IsingBulk.Anisotropic.NegativeNormalForm.BetaUniformScale

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

theorem mul_exp_le_exp_two_sub_one (x : ℝ) (hx : 0≤x) :
    x*Real.exp x≤Real.exp (2*x)-1 := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos x).le
  rw [show 2*x=x+x by ring,Real.exp_add]
  nlinarith [Real.one_le_exp_iff.mpr hx]

/-- Both central and truncated-tail beta errors, with no fixed-order
asymptotic replacement of either growing integer parameter. -/
theorem beta_exponential_truncated (a j K : ℕ) (ha : 0<a) (hj : 4*a+4≤j)
    (hKj : K≤j-j/2) (C L : ℝ) (hC : 0≤C) (hL : 1≤L)
    (hK : C*(Real.sqrt L+L)≤(K:ℝ)*Real.log 2) :
    (∫ x in Ioo (0:ℝ) L,
      (Real.exp (C*(Real.sqrt x+x))-1)*(x^(a-1)/(1+x)^(j+1)))/betaMass a j≤
        expErrorConstant C 1*(Real.sqrt ((a:ℝ)/((j:ℝ)-a))+(a:ℝ)/((j:ℝ)-a))+
          (2:ℝ)^(-((j-K-j/2:ℕ):ℤ))*4^a := by
  let f : ℝ → ℝ := fun x => x^(a-1)/(1+x)^(j+1)
  let g : ℝ → ℝ := fun x => (Real.exp (C*(Real.sqrt x+x))-1)*f x
  let g' : ℝ → ℝ := fun x => Real.exp (C*(Real.sqrt x+x))*f x
  have hf : ContinuousOn f (Ici 0) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero _ (ne_of_gt (by have hx0 : 0≤x := hx; linarith))
  have hg : ContinuousOn g (Ici 0) := ContinuousOn.mul (by fun_prop) hf
  have hg' : ContinuousOn g' (Ici 0) := ContinuousOn.mul (by fun_prop) hf
  have h01 : IntervalIntegrable g volume 0 1 :=
    (hg.mono (fun x hx => hx.1)).intervalIntegrable_of_Icc zero_le_one
  have h1L : IntervalIntegrable g volume 1 L :=
    (hg.mono (fun x hx => le_trans zero_le_one hx.1)).intervalIntegrable_of_Icc hL
  have hsplit : (∫ x in Ioo (0:ℝ) L,g x)=
      (∫ x in Ioo (0:ℝ) 1,g x)+(∫ x in Ioo (1:ℝ) L,g x) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals h01 h1L
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le hL,
      intervalIntegral.integral_of_le (zero_le_one.trans hL)] at hh
    simpa only [integral_Ioc_eq_integral_Ioo] using hh.symm
  have hgi : IntegrableOn g (Ioo 1 L) :=
    ((hg.mono (fun x (hx : x∈Icc 1 L) => le_trans zero_le_one hx.1)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hg'i : IntegrableOn g' (Ioo 1 L) :=
    ((hg'.mono (fun x (hx : x∈Icc 1 L) => le_trans zero_le_one hx.1)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have htaille : (∫ x in Ioo (1:ℝ) L,g x)≤∫ x in Ioo (1:ℝ) L,g' x := by
    apply integral_mono_ae hgi hg'i
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    dsimp [g,g',f]
    have hx0 : 0<x := lt_trans zero_lt_one hx.1
    gcongr
    linarith
  have hin := beta_exponential_inner a j ha (by omega) C 1 hC
  have hout := beta_exponential_tail a j K ha hj hKj C 1 L hC zero_le_one (by norm_num; exact hK)
  change (∫ x in Ioo (0:ℝ) L,g x)/betaMass a j≤_
  rw [hsplit,add_div]
  apply add_le_add hin
  exact (div_le_div_of_nonneg_right htaille (betaMass_pos a j ha (by omega)).le).trans (by simpa only [show (1:ℝ)+1=2 by norm_num] using hout)

end
end IsingBulk.Anisotropic.NegativeNormalForm
