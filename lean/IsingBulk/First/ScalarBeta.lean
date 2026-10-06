import IsingBulk.First.ShapeRadialLimit

/-! Positive-real radial beta evaluation by an integration-by-parts recurrence. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def scalarUnitRadialIntegral (k : ℕ) : ℝ :=
  ∫ r : ℝ in Ioi 0, shapeRadialMajorant k r

theorem scalarUnitRadialIntegral_zero : scalarUnitRadialIntegral 0 = Real.pi / 2 := by
  simp [scalarUnitRadialIntegral, shapeRadialMajorant]

def scalarRadialPrimitive (k : ℕ) (r : ℝ) : ℝ :=
  r ^ (2*k+1) / (1+r^2)^(k+1)

theorem scalarRadialPrimitive_derivative (k : ℕ) (r : ℝ) :
    HasDerivAt (scalarRadialPrimitive k)
      ((2*(k:ℝ)+1)*shapeRadialMajorant k r -
        (2*(k:ℝ)+2)*shapeRadialMajorant (k+1) r) r := by
  have hn : (1+r^2)^(k+1) ≠ 0 := by positivity
  convert ((hasDerivAt_id r).pow (2*k+1)).div
    ((((hasDerivAt_id r).pow 2).const_add 1).pow (k+1)) hn using 1
  · rfl
  · simp only [shapeRadialMajorant, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.add_sub_cancel, Nat.cast_one, Pi.pow_apply, id_eq, mul_one]
    simp only [Nat.mul_add, pow_mul, pow_succ]
    field_simp

theorem scalarRadialPrimitive_le_inv (k : ℕ) {r : ℝ} (hr : 0 < r) :
    scalarRadialPrimitive k r ≤ r⁻¹ := by
  have hd : 0 < (1+r^2)^(k+1) := by positivity
  rw [scalarRadialPrimitive, div_le_iff₀ hd]
  apply (mul_le_mul_iff_left₀ hr).mp
  have hpow : (r^2)^(k+1) ≤ (1+r^2)^(k+1) :=
    pow_le_pow_left₀ (sq_nonneg r) (by linarith) _
  calc
    r^(2*k+1)*r = (r^2)^(k+1) := by rw [← pow_succ, ← pow_mul]; congr 1
    _ ≤ (1+r^2)^(k+1) := hpow
    _ = (r⁻¹*(1+r^2)^(k+1))*r := by field_simp

theorem scalarRadialPrimitive_tendsto (k : ℕ) :
    Tendsto (scalarRadialPrimitive k) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    unfold scalarRadialPrimitive
    positivity
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact scalarRadialPrimitive_le_inv k hr

theorem scalarUnitRadialIntegral_recurrence (k : ℕ) :
    (2*(k:ℝ)+2)*scalarUnitRadialIntegral (k+1) =
      (2*(k:ℝ)+1)*scalarUnitRadialIntegral k := by
  have hi0 := ((shapeRadialMajorant_integrable k).const_mul (2*(k:ℝ)+1)).integrableOn (s := Ioi 0)
  have hi1 := ((shapeRadialMajorant_integrable (k+1)).const_mul (2*(k:ℝ)+2)).integrableOn (s := Ioi 0)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0:ℝ)) (fun r _ => scalarRadialPrimitive_derivative k r)
    (hi0.sub hi1) (scalarRadialPrimitive_tendsto k)
  rw [integral_sub hi0 hi1, integral_const_mul, integral_const_mul] at h
  have hz : scalarRadialPrimitive k 0 = 0 := by simp [scalarRadialPrimitive]
  rw [hz, sub_zero] at h
  exact (sub_eq_zero.mp h).symm


theorem scalarBetaHalf_zero : Complex.betaIntegral (1/2) (1/2) = (Real.pi:ℂ) := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num),
    add_halves, Complex.Gamma_one, div_one, Complex.Gamma_one_half_eq]
  rw [← Complex.cpow_add _ _ (show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero),
    add_halves, Complex.cpow_one]

theorem scalarBetaHalf_recurrence (k : ℕ) :
    (2*(k:ℂ)+2)*Complex.betaIntegral (((k+1:ℕ):ℂ)+1/2) (1/2) =
      (2*(k:ℂ)+1)*Complex.betaIntegral ((k:ℂ)+1/2) (1/2) := by
  have hk : 0 < (((k:ℂ)+1/2).re) := by simp; positivity
  have hk1 : 0 < ((((k+1:ℕ):ℂ)+1/2).re) := by simp; positivity
  have hh : 0 < ((1/2:ℂ).re) := by norm_num
  let z : ℂ := (k:ℂ)+1/2
  have hz : z ≠ 0 := Complex.ne_zero_of_re_pos hk
  have hzs : z+1/2 ≠ 0 := Complex.ne_zero_of_re_pos (by simpa only [z, Complex.add_re] using add_pos hk hh)
  have hn : (((k+1:ℕ):ℂ)+1/2) = z+1 := by dsimp [z]; push_cast; ring
  have hs : (((k+1:ℕ):ℂ)+1/2)+(1/2:ℂ) = (z+1/2)+1 := by dsimp [z]; push_cast; ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hk1 hh,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ hk hh, hs, hn,
    Complex.Gamma_add_one _ hz, Complex.Gamma_add_one _ hzs]
  change (2*(k:ℂ)+2)*(z*Complex.Gamma z*Complex.Gamma (1/2)/
    ((z+1/2)*Complex.Gamma (z+1/2))) =
    (2*(k:ℂ)+1)*(Complex.Gamma z*Complex.Gamma (1/2)/Complex.Gamma (z+1/2))
  have hg : Complex.Gamma (z+1/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa only [z, Complex.add_re] using add_pos hk hh)
  have hc0 : 2*(k:ℂ)+2 = 2*(z+1/2) := by dsimp [z]; ring
  have hc1 : 2*(k:ℂ)+1 = 2*z := by dsimp [z]; ring
  rw [hc0, hc1]
  calc
    (2*(z+1/2))*(z*Complex.Gamma z*Complex.Gamma (1/2)/
        ((z+1/2)*Complex.Gamma (z+1/2))) =
        2*((z+1/2)*(z*Complex.Gamma z*Complex.Gamma (1/2))/
          ((z+1/2)*Complex.Gamma (z+1/2))) := by ring
    _ = 2*(z*Complex.Gamma z*Complex.Gamma (1/2)/Complex.Gamma (z+1/2)) := by
      rw [mul_div_mul_left _ _ hzs]
    _ = _ := by ring


theorem scalarUnitRadialIntegral_beta (k : ℕ) :
    (scalarUnitRadialIntegral k : ℂ) =
      (1/2:ℂ)*Complex.betaIntegral ((k:ℂ)+1/2) (1/2) := by
  induction k with
  | zero =>
      rw [scalarUnitRadialIntegral_zero]
      norm_num only [Nat.cast_zero, zero_add, Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [scalarBetaHalf_zero]
      ring
  | succ k ih =>
      have hc : (2*(k:ℂ)+2) ≠ 0 := by
        apply Complex.ne_zero_of_re_pos
        simp
        positivity
      apply mul_left_cancel₀ hc
      calc
        (2*(k:ℂ)+2)*(scalarUnitRadialIntegral (k+1):ℂ) =
            (2*(k:ℂ)+1)*(scalarUnitRadialIntegral k:ℂ) := by
          exact_mod_cast scalarUnitRadialIntegral_recurrence k
        _ = (2*(k:ℂ)+2)*((1/2:ℂ)*Complex.betaIntegral (((k+1:ℕ):ℂ)+1/2) (1/2)) := by
          rw [ih]
          linear_combination -(1/2:ℂ)*scalarBetaHalf_recurrence k


theorem shapeRadialIntegral_unit (k : ℕ) :
    shapeRadialIntegral k 1 1 =
      (1/2:ℂ)*Complex.betaIntegral ((k:ℂ)+1/2) (1/2) := by
  rw [← scalarUnitRadialIntegral_beta]
  unfold shapeRadialIntegral scalarUnitRadialIntegral
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp [shapeRadialKernel, shapeQuadratic, shapeRadialMajorant]

theorem shapeRadialKernel_positive_scale (k : ℕ) {Q c t : ℝ}
    (ht : c*t^2 = Q) (r : ℝ) :
    shapeRadialKernel k Q (c:ℂ) (t*r) =
      ((t:ℂ)^(2*k)/(Q:ℂ)^(k+1))*shapeRadialKernel k 1 1 r := by
  have ht' : (c:ℂ)*(t:ℂ)^2 = (Q:ℂ) := by exact_mod_cast ht
  have hd : (Q:ℂ)+(c:ℂ)*((t:ℂ)*(r:ℂ))^2 =
      (Q:ℂ)*(1+(r:ℂ)^2) := by
    calc
      _ = (Q:ℂ)+((c:ℂ)*(t:ℂ)^2)*(r:ℂ)^2 := by ring
      _ = _ := by rw [ht']; ring
  unfold shapeRadialKernel shapeQuadratic
  simp only [Complex.ofReal_mul, Complex.ofReal_one, one_mul]
  rw [hd]
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem shapeRadialIntegral_positive_scale (k : ℕ) {Q c t : ℝ}
    (htpos : 0 < t) (ht : c*t^2 = Q) :
    shapeRadialIntegral k Q (c:ℂ) =
      ((t:ℂ)*((t:ℂ)^(2*k)/(Q:ℂ)^(k+1)))*shapeRadialIntegral k 1 1 := by
  have h := integral_comp_mul_left_Ioi' (shapeRadialKernel k Q (c:ℂ)) 0 htpos
  simp only [mul_zero] at h
  unfold shapeRadialIntegral
  rw [← h]
  simp_rw [shapeRadialKernel_positive_scale k ht]
  rw [integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem scalar_positive_scale_factor (k : ℕ) {Q c : ℝ} (hQ : 0 < Q) (hc : 0 < c) :
    (Real.sqrt Q / Real.sqrt c) *
      ((Real.sqrt Q / Real.sqrt c)^(2*k)/Q^(k+1)) =
      (Real.sqrt Q)⁻¹ * (c^k)⁻¹ * (Real.sqrt c)⁻¹ := by
  have hsQ : (Real.sqrt Q)^2 = Q := Real.sq_sqrt hQ.le
  have hsc : (Real.sqrt c)^2 = c := Real.sq_sqrt hc.le
  have hnQ : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hnc : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have ht : (Real.sqrt Q / Real.sqrt c)^2 = Q/c := by rw [div_pow, hsQ, hsc]
  rw [pow_mul, ht, div_pow, pow_succ Q k]
  field_simp
  nlinarith [hsQ]

theorem shapeRadialIntegral_positive_sqrt (k : ℕ) {Q c : ℝ}
    (hQ : 0 < Q) (hc : 0 < c) :
    shapeRadialIntegral k Q (c:ℂ) =
      (1/2:ℂ)*(Real.sqrt Q:ℂ)⁻¹*((c:ℂ)^k)⁻¹*(Real.sqrt c:ℂ)⁻¹*
        Complex.betaIntegral ((k:ℂ)+1/2) (1/2) := by
  let t := Real.sqrt Q / Real.sqrt c
  have htpos : 0 < t := div_pos (Real.sqrt_pos.mpr hQ) (Real.sqrt_pos.mpr hc)
  have ht : c*t^2 = Q := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt hQ.le, Real.sq_sqrt hc.le]
    field_simp
  rw [shapeRadialIntegral_positive_scale k htpos ht, shapeRadialIntegral_unit]
  have hcoef : (t:ℂ)*((t:ℂ)^(2*k)/(Q:ℂ)^(k+1)) =
      (Real.sqrt Q:ℂ)⁻¹*((c:ℂ)^k)⁻¹*(Real.sqrt c:ℂ)⁻¹ := by
    exact_mod_cast scalar_positive_scale_factor k hQ hc
  rw [hcoef]
  ring


theorem scalarPositive_cpow_half {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(1/2:ℂ) = (Real.sqrt x:ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
  norm_num

/-- Exact beta value of the actual radial integral for positive real coefficients.
The proof uses the genuine derivative recurrence, vanishing endpoint terms,
positive scaling and the principal positive-real complex powers. -/
theorem shapeRadialIntegral_positive_beta (k : ℕ) {Q c : ℝ}
    (hQ : 0 < Q) (hc : 0 < c) :
    shapeRadialIntegral k Q (c:ℂ) =
      (1/2:ℂ)*(Q:ℂ)^(-1/2:ℂ)*(c:ℂ)^(-(k:ℂ)-1/2)*
        Complex.betaIntegral ((k:ℂ)+1/2) (1/2) := by
  rw [shapeRadialIntegral_positive_sqrt k hQ hc]
  have hQhalf : (Q:ℂ)^(-1/2:ℂ) = (Real.sqrt Q:ℂ)⁻¹ := by
    rw [show (-1/2:ℂ) = -(1/2) by ring, Complex.cpow_neg,
      scalarPositive_cpow_half hQ]
  have hcfull : (c:ℂ)^(-(k:ℂ)-1/2) = ((c:ℂ)^k)⁻¹*(Real.sqrt c:ℂ)⁻¹ := by
    rw [show -(k:ℂ)-1/2 = -((k:ℂ)+1/2) by ring, Complex.cpow_neg,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hc.ne'),
      Complex.cpow_natCast, scalarPositive_cpow_half hc, mul_inv_rev]
    ring
  rw [hQhalf, hcfull]
  ring

end
end IsingBulk.First
