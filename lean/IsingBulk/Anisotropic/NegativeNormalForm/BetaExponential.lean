import IsingBulk.Anisotropic.NegativeNormalForm.BetaTail

/-! Quantitative estimates of the explicit exponential density majorant in
actual beta measure. The density estimate itself is not assumed as a theorem. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

 def expErrorConstant (C delta : ℝ) : ℝ := C*Real.exp (C*(Real.sqrt delta+delta))

theorem exp_sub_one_le_mul_exp (y : ℝ) : Real.exp y-1≤y*Real.exp y := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-y)) (Real.exp_pos y).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

theorem exponential_error_inner_bound {C delta x : ℝ} (hC : 0≤C) (hx : 0≤x) (hxd : x≤delta) :
    Real.exp (C*(Real.sqrt x+x))-1 ≤ expErrorConstant C delta*(Real.sqrt x+x) := by
  have hy : 0≤C*(Real.sqrt x+x) := by positivity
  have he : C*(Real.sqrt x+x)≤C*(Real.sqrt delta+delta) :=
    mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hxd) hxd) hC
  calc
    _ ≤ C*(Real.sqrt x+x)*Real.exp (C*(Real.sqrt x+x)) := exp_sub_one_le_mul_exp _
    _ ≤ C*(Real.sqrt x+x)*Real.exp (C*(Real.sqrt delta+delta)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hy
    _ = _ := by unfold expErrorConstant; ring

theorem beta_first_moment_order (a j : ℕ) (ha : 0<a) (haj : a<j) :
    (∫ x in Ioi (0 : ℝ), x*(x^(a-1)/(1+x)^(j+1))) / betaMass a j =
      (a : ℝ)/((j : ℝ)-a) := by
  have he : a-1+(j-a-1)+3=j+1 := by omega
  have h1 : ((a-1 : ℕ) : ℝ)+1=(a : ℝ) := by exact_mod_cast (show a-1+1=a by omega)
  have h2 : ((j-a-1 : ℕ) : ℝ)+1=(j : ℝ)-a := by
    have h : ((j-a-1 : ℕ) : ℝ)+1+(a : ℝ)=(j : ℝ) := by
      exact_mod_cast (show j-a-1+1+a=j by omega)
    linarith
  simpa only [he,h1,h2,betaMass] using betaPrime_first_moment_ratio (a-1) (j-a-1)

theorem beta_first_moment_integrable (a j : ℕ) (ha : 0<a) (haj : a<j) :
    IntegrableOn (fun x : ℝ => x*(x^(a-1)/(1+x)^(j+1))) (Ioi 0) := by
  have h := beta_integrable_order (a+1) j (by omega) (by omega)
  convert h using 1
  ext x
  simp only [Nat.add_sub_cancel]
  rw [← mul_div_assoc, ← pow_succ']
  congr 2
  omega

theorem beta_sqrt_moment_integrable (a j : ℕ) (ha : 0<a) (haj : a<j) :
    IntegrableOn (fun x : ℝ => Real.sqrt x*(x^(a-1)/(1+x)^(j+1))) (Ioi 0) := by
  have hf := beta_integrable_order a j ha haj.le
  have hxf := beta_first_moment_integrable a j ha haj
  apply ((hxf.add hf).div_const 2).mono'
  · exact (by fun_prop : Measurable (fun x : ℝ => Real.sqrt x*(x^(a-1)/(1+x)^(j+1)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := mul_le_mul_of_nonneg_right (sqrt_le_tangent hx0.le zero_lt_one)
      (show 0≤x^(a-1)/(1+x)^(j+1) by positivity)
    norm_num only [Real.sqrt_one, mul_one] at h
    convert h using 1
    simp only [Pi.add_apply]
    ring

/-- The actual small-x contribution of exp(C√x+Cx)−1, bounded by exact first
and square-root beta moments, with a constant independent of α and j. -/
theorem beta_exponential_inner (a j : ℕ) (ha : 0<a) (haj : a<j)
    (C delta : ℝ) (hC : 0≤C) :
    (∫ x in Ioo (0 : ℝ) delta,
      (Real.exp (C*(Real.sqrt x+x))-1)*(x^(a-1)/(1+x)^(j+1))) / betaMass a j ≤
      expErrorConstant C delta *
        (Real.sqrt ((a : ℝ)/((j : ℝ)-a))+(a : ℝ)/((j : ℝ)-a)) := by
  let f : ℝ → ℝ := fun x => x^(a-1)/(1+x)^(j+1)
  let A : ℝ := expErrorConstant C delta
  have hA : 0≤A := mul_nonneg hC (Real.exp_pos _).le
  have hsf := beta_sqrt_moment_integrable a j ha haj
  have hxf := beta_first_moment_integrable a j ha haj
  have hmajor : IntegrableOn (fun x => A*(Real.sqrt x*f x+x*f x)) (Ioi 0) :=
    (hsf.add hxf).const_mul A
  have hsub : Ioo (0 : ℝ) delta ⊆ Ioi 0 := fun _ hx => hx.1
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) delta,
      (Real.exp (C*(Real.sqrt x+x))-1)*f x ≤ A*(Real.sqrt x*f x+x*f x) := by
    intro x hx
    have hx0 : 0<x := hx.1
    have h := mul_le_mul_of_nonneg_right (exponential_error_inner_bound hC hx.1.le hx.2.le)
      (show 0≤f x by dsimp [f]; positivity)
    convert h using 1
    ring
  have herr : IntegrableOn (fun x => (Real.exp (C*(Real.sqrt x+x))-1)*f x) (Ioo 0 delta) := by
    apply (hmajor.mono_set hsub).mono'
    · exact (by fun_prop : Measurable (fun x => (Real.exp (C*(Real.sqrt x+x))-1)*f x)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx0 : 0<x := hx.1
      have he : 0≤Real.exp (C*(Real.sqrt x+x))-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg he (by dsimp [f]; positivity))]
      exact hpoint x hx
  have hle := integral_mono_ae herr (hmajor.mono_set hsub) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hpoint x hx)
  have hwhole : (∫ x in Ioo (0 : ℝ) delta, A*(Real.sqrt x*f x+x*f x)) ≤
      ∫ x in Ioi (0 : ℝ), A*(Real.sqrt x*f x+x*f x) := by
    apply setIntegral_mono_set hmajor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0<x := hx
      dsimp [f]
      positivity
    · exact Filter.Eventually.of_forall (fun x hx => hsub hx)
  have h := div_le_div_of_nonneg_right (hle.trans hwhole) (betaMass_pos a j ha haj.le).le
  rw [integral_const_mul, integral_add hsf hxf, mul_div_assoc, add_div,
    beta_first_moment_order a j ha haj] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (betaPrime_sqrt_order a j ha haj) le_rfl) hA)


/-- Explicit absorption of the exponential density factor on a truncated tail. -/
theorem exponential_tail_absorption {C delta L x : ℝ} (K : ℕ) (hC : 0≤C)
    (hd : 0≤delta) (hx : delta≤x) (hxL : x≤L)
    (hK : C*(Real.sqrt L+L)≤(K : ℝ)*Real.log (1+delta)) :
    Real.exp (C*(Real.sqrt x+x))≤(1+x)^K := by
  have hx0 : 0≤x := hd.trans hx
  have hlog : Real.log (1+delta)≤Real.log (1+x) :=
    Real.log_le_log (by positivity) (by linarith)
  have h : C*(Real.sqrt x+x)≤(K : ℝ)*Real.log (1+x) :=
    (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hxL) hxL) hC).trans
      (hK.trans (mul_le_mul_of_nonneg_left hlog (by positivity)))
  have he := Real.exp_le_exp.mpr h
  simpa only [Real.exp_nat_mul, Real.exp_log (by positivity : 0<1+x)] using he

/-- Actual weighted tail estimate. The only extra condition is the explicit
scalar absorption inequality, which can be checked in the n²/j→0 regime. -/
theorem beta_exponential_tail (a j K : ℕ) (ha : 0<a) (hj : 4*a+4≤j)
    (hKj : K≤j-j/2) (C delta L : ℝ) (hC : 0≤C) (hd : 0≤delta)
    (hK : C*(Real.sqrt L+L)≤(K : ℝ)*Real.log (1+delta)) :
    (∫ x in Ioo delta L, Real.exp (C*(Real.sqrt x+x))*(x^(a-1)/(1+x)^(j+1))) /
      betaMass a j ≤ (1+delta)^(-((j-K-j/2 : ℕ) : ℤ))*4^a := by
  let b : ℝ := (1+delta)^(-((j-K-j/2 : ℕ) : ℤ))
  have hb : 0≤b := by dsimp [b]; positivity
  have hJ : a≤j/2 := by omega
  have hJK : j/2≤j-K := by omega
  have hKj' : K≤j := by omega
  have hfJ := beta_integrable_order a (j/2) ha hJ
  have hsub : Ioo delta L ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt hd hx.1
  have hpoint : ∀ x ∈ Ioo delta L,
      Real.exp (C*(Real.sqrt x+x))*(x^(a-1)/(1+x)^(j+1)) ≤
        b*(x^(a-1)/(1+x)^(j/2+1)) := by
    intro x hx
    have hx0 : 0<x := lt_of_le_of_lt hd hx.1
    have habs := exponential_tail_absorption K hC hd hx.1.le hx.2.le hK
    have hbase : Real.exp (C*(Real.sqrt x+x))*(x^(a-1)/(1+x)^(j+1)) ≤
        x^(a-1)/(1+x)^(j-K+1) := by
      calc
        _ ≤ (1+x)^K*(x^(a-1)/(1+x)^(j+1)) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
        _ = _ := by
          have he : j+1=K+(j-K+1) := by omega
          rw [he,pow_add]
          have hn : 1+x ≠ 0 := ne_of_gt (by linarith)
          field_simp
    exact hbase.trans (beta_tail_pointwise a (j/2) (j-K) hJK hd hx.1.le)
  have hmajor := (hfJ.mono_set hsub).const_mul b
  have hweight : IntegrableOn (fun x => Real.exp (C*(Real.sqrt x+x))*(x^(a-1)/(1+x)^(j+1))) (Ioo delta L) := by
    apply hmajor.mono'
    · exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (C*(Real.sqrt x+x))*(x^(a-1)/(1+x)^(j+1)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx0 : 0<x := lt_of_le_of_lt hd hx.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint x hx
  have hle := integral_mono_ae hweight hmajor (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hpoint x hx)
  have hmass : (∫ x in Ioo delta L, b*(x^(a-1)/(1+x)^(j/2+1))) ≤ b*betaMass a (j/2) := by
    unfold betaMass
    rw [← integral_const_mul]
    apply setIntegral_mono_set (hfJ.const_mul b)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0<x := hx
      positivity
    · exact Filter.Eventually.of_forall (fun x hx => hsub hx)
  have h := div_le_div_of_nonneg_right (hle.trans hmass) (betaMass_pos a j ha (by omega)).le
  rw [mul_div_assoc] at h
  exact h.trans (mul_le_mul_of_nonneg_left (betaMass_half_order_ratio a j ha hj) hb)

end
end IsingBulk.Anisotropic.NegativeNormalForm
