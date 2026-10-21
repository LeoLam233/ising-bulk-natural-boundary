import IsingBulk.First.ActualShapeAmplitude
import IsingBulk.HT.First.OrderArithmetic

/-! Exact phase of the actual odd-particle local density. The literal LT
pre-parity center formula is reused; only its parity simplification changes. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.First
open scoped Topology

/-- The normalized physical numerator at an odd center is -i K, not K. -/
theorem actualRegularFactor_center_eq_odd_K (a : OrderedChartData) (n : ℕ)
    (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) /
      ((n+1).factorial:ℂ) = -I*(a.K (n+1):ℂ) := by
  rw [actualRegularFactor_center_explicit a n ha hb,firstStrictPairs_twice_card]
  have hex : (n+1)*n+(n+1) = (n+1)^2 := by ring
  rw [hex,mul_pow,mul_inv_rev]
  have hi : (I^((n+1)^2))⁻¹ = -I := by
    simpa only [← Nat.cast_pow,zpow_neg,zpow_natCast] using odd_particle_phase ho
  rw [hi]
  simp only [OrderedChartData.K,ofReal_mul,ofReal_div,ofReal_ofNat,
    ofReal_inv,ofReal_pow,ofReal_natCast,Nat.add_sub_cancel]
  ring

/-- Highest-pole amplitude of the literal odd density at its actual center. -/
theorem actualLeadingAmplitude_odd_center (a : OrderedChartData) (n k : ℕ)
    (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualLeadingAmplitude a n k (exp ((a.theta:ℂ)*I),0) =
      -I*((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k) := by
  have hB : complexDensityRegular a.alpha
      (exp ((a.theta:ℂ)*I),(0 : Fin (n+1) → ℂ))/((n+1).factorial:ℂ) =
      -I*(a.K (n+1):ℂ) := by
    convert actualRegularFactor_center_eq_odd_K a n ho ha hb using 1
    rw [← complexDensityRegular_real_shape]
    simp only [shapeExtend_zero_exact,Pi.zero_apply,ofReal_zero]
    rfl
  unfold actualLeadingAmplitude
  rw [actualSincFactor_zero,ofReal_one,one_mul,realShapeEmbedding_center]
  unfold jointPoleLeadingNumerator poleLeadingNumerator
  rw [(actual_shape_denominator_hasDerivAt a n hb).deriv]
  linear_combination (-1:ℂ)^k*(k.factorial:ℂ)*a.Ds (n+1)^k*hB

/-- Actual intrinsic odd amplitude limit. All continuity is inherited from
LT's parity-free analytic density theorem; only the center phase is adapted. -/
theorem intrinsicLeadingAmplitude_odd_scale_limit {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) (x : ShapeSpace n) :
    Tendsto (fun lam : ℝ => intrinsicLeadingAmplitude a k (lam^2,lam • x))
      (𝓝[>] 0) (𝓝 (-I*((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k))) := by
  have hp : Tendsto (fun lam : ℝ => (lam^2,lam • x)) (𝓝[>] 0) (𝓝 (0,0)) := by
    have hc : Continuous (fun lam : ℝ => (lam^2,lam • x)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have h := (intrinsicLeadingAmplitude_continuousAt_zero a k).tendsto.comp hp
  simpa only [Function.comp_def,intrinsicLeadingAmplitude,intrinsicRadialEmbedding_zero,
    actualLeadingAmplitude_odd_center a n k ho ha hb] using h

/-- The prime-order lower center has the p-root identity required by the
actual mean pole. No even-particle root identity is substituted. -/
theorem selected_odd_lower_center_root {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a) :
    exp (-(p:ℂ)*(IsingBulk.PrimeFamily.angle p a:ℂ)*I) = 1 := by
  have hpw := (IsingBulk.PrimeFamily.angleRoot_primitive hp ha).pow_eq_one
  rw [show -(p:ℂ)*(IsingBulk.PrimeFamily.angle p a:ℂ)*I =
    -(p:ℂ)*((IsingBulk.PrimeFamily.angle p a:ℂ)*I) by ring,
    neg_mul,exp_neg,exp_nat_mul]
  change (IsingBulk.PrimeFamily.angleRoot p a^p)⁻¹ = 1
  rw [hpw,inv_one]

end
end IsingBulk.HT.First
