import IsingBulk.First.ShapeSource
import IsingBulk.HT.First.OrderArithmetic

/-!
Absolute integrability of the actual HT constrained Vandermonde period.
The LT weighted polar theorem is unchanged. The genuinely new radial exponent
is 2k−1, with k=(p²−1)/2. The estimate covers both signs of the curvature.
-/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set IsingBulk.First

/-- HT radial majorant, with k=m+1. -/
def oddRadialMajorant (m : ℕ) (r : ℝ) : ℝ :=
  |r|^(2*m+1)/(1+r^2)^(m+2)

theorem oddRadialMajorant_nonneg (m : ℕ) (r : ℝ) :
    0 ≤ oddRadialMajorant m r := by unfold oddRadialMajorant; positivity

theorem oddRadialMajorant_le (m : ℕ) (r : ℝ) :
    oddRadialMajorant m r ≤ (1+r^2)⁻¹ := by
  have h : 0 < 1+r^2 := by positivity
  have hab : |r| ≤ 1+r^2 := by nlinarith [sq_nonneg (|r|-1),sq_abs r]
  have hp : (|r|^2)^m ≤ (1+r^2)^m :=
    pow_le_pow_left₀ (sq_nonneg _) (by rw [sq_abs]; linarith) _
  rw [oddRadialMajorant,div_le_iff₀ (pow_pos h _)]
  calc
    |r|^(2*m+1) = (|r|^2)^m*|r| := by rw [pow_add,pow_mul,pow_one]
    _ ≤ (1+r^2)^m*(1+r^2) := mul_le_mul hp hab (abs_nonneg _) (by positivity)
    _ = (1+r^2)⁻¹*(1+r^2)^(m+2) := by
      rw [pow_add]
      field_simp

theorem oddRadialMajorant_integrable (m : ℕ) : Integrable (oddRadialMajorant m) := by
  refine integrable_inv_one_add_sq.mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
  · apply Continuous.aestronglyMeasurable
    unfold oddRadialMajorant
    have hn : ∀ r : ℝ, (1+r^2)^(m+2) ≠ 0 := fun r => ne_of_gt (by positivity)
    fun_prop
  · rw [Real.norm_eq_abs,abs_of_nonneg (oddRadialMajorant_nonneg m r)]
    exact oddRadialMajorant_le m r

/-- Two-sided curvature version of the LT quadratic lower bound. The real
part supplies Q and the absolute imaginary part supplies |d|r². -/
theorem odd_shapeQuadratic_lower {Q d : ℝ} (_hQ : 0 < Q) (_hd : d ≠ 0) (r : ℝ) :
    min Q |d|/2*(1+r^2) ≤ ‖shapeQuadratic Q (-Complex.I*d) r‖ := by
  have hre := Complex.re_le_norm (shapeQuadratic Q (-Complex.I*d) r)
  have him := Complex.abs_im_le_norm (shapeQuadratic Q (-Complex.I*d) r)
  have hparts : (shapeQuadratic Q (-Complex.I*d) r).re = Q ∧
      (shapeQuadratic Q (-Complex.I*d) r).im = -d*r^2 := by
    constructor <;> simp [shapeQuadratic,pow_two]
  rw [hparts.1] at hre
  rw [hparts.2,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg r)] at him
  have hminQ := min_le_left Q |d|
  have hmind := mul_le_mul_of_nonneg_right (min_le_right Q |d|) (sq_nonneg r)
  nlinarith

theorem odd_shapeQuadratic_ne_zero {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) (r : ℝ) :
    shapeQuadratic Q (-Complex.I*d) r ≠ 0 := by
  have hdpos : 0 < |d| := abs_pos.mpr hd
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (by positivity) (odd_shapeQuadratic_lower hQ hd r)

theorem odd_radial_kernel_integrable (m : ℕ) {Q d : ℝ}
    (hQ : 0 < Q) (hd : d ≠ 0) :
    Integrable (fun r : ℝ => (r:ℂ)^(2*m+1)/
      shapeQuadratic Q (-Complex.I*d) r^(m+2)) := by
  let a : ℝ := min Q |d|/2
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have ha : 0 < a := by dsimp [a]; positivity
  refine ((oddRadialMajorant_integrable m).const_mul (a^(m+2))⁻¹).mono' ?_
    (Filter.Eventually.of_forall fun r => ?_)
  · apply Continuous.aestronglyMeasurable
    have hn : ∀ r : ℝ, shapeQuadratic Q (-Complex.I*d) r^(m+2) ≠ 0 :=
      fun r => pow_ne_zero _ (odd_shapeQuadratic_ne_zero hQ hd r)
    have hc : Continuous (shapeQuadratic Q (-Complex.I*d)) := by
      unfold shapeQuadratic
      fun_prop
    fun_prop
  · rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,norm_pow]
    calc
      |r|^(2*m+1)/‖shapeQuadratic Q (-Complex.I*d) r‖^(m+2)
          ≤ |r|^(2*m+1)/(a*(1+r^2))^(m+2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by positivity) (odd_shapeQuadratic_lower hQ hd r) _
      _ = (a^(m+2))⁻¹*oddRadialMajorant m r := by
        simp only [oddRadialMajorant,mul_pow,div_eq_mul_inv,mul_inv_rev]
        ring

/-- The LT quotient majorant is also integrable with the new odd degree.
Only the radial calculation changes; the shape polynomial and measure do not. -/
theorem odd_shapeMajorant_integrable {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) : Integrable (@shapeMajorant n k) := by
  cases k with
  | zero => omega
  | succ m =>
    have hdeg : n-1+(n+1)*n = 2*m+1 := by omega
    let f : ℝ → ℂ := fun r => (((1+r^2)^(m+2):ℝ):ℂ)⁻¹
    have hrbase := ((oddRadialMajorant_integrable m).ofReal (𝕜 := ℂ)).integrableOn
      (s := Ioi (0:ℝ))
    have hr : IntegrableOn (fun r : ℝ => (r^(n-1+(n+1)*n)) • f r) (Ioi 0) := by
      apply hrbase.congr_fun
      · intro r hr
        have hr0 : 0 < r := hr
        simp only [f,hdeg,oddRadialMajorant,abs_of_pos hr0,
          Complex.real_smul,div_eq_mul_inv,Complex.ofReal_pow]
        change Complex.ofReal (r^(2*m+1)*((1+r^2)^(m+2))⁻¹) =
          (Complex.ofReal r)^(2*m+1)*((Complex.ofReal (1+r^2))^(m+2))⁻¹
        simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow]
      · exact measurableSet_Ioi
    have hc : Integrable (fun x : ShapeSpace n => (shapeMajorant (m+1) x:ℂ)) := by
      simpa only [shapeMajorant,f,show m+1+1=m+2 by omega,
        Complex.real_smul,Complex.ofReal_div,div_eq_mul_inv,
        Complex.ofReal_mul,Complex.ofReal_inv] using
        integrable_shapeVandermonde_polar hn f hr
    simpa using hc.re

/-- Parity-independent polar infrastructure applied to the new odd radial
exponent. This is integrability of the existing actual shape integral. -/
theorem odd_shapePeriodIntrinsic_integrable {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) :
    Integrable (fun x : ShapeSpace n => (shapeVandermondeSq x:ℂ)/
      ((Q:ℂ)-Complex.I*d*(‖x‖:ℂ)^2)^(k+1)) := by
  cases k with
  | zero => omega
  | succ m =>
    have hdeg : n-1+(n+1)*n = 2*m+1 := by omega
    have hr := (odd_radial_kernel_integrable m hQ hd).integrableOn (s := Ioi 0)
    have hi := integrable_shapeVandermonde_polar hn
      (fun r => (((Q:ℂ)-Complex.I*d*(r:ℂ)^2)^(m+2))⁻¹)
    have hb : IntegrableOn
        (fun r : ℝ => (r^(n-1+(n+1)*n)) •
          (((Q:ℂ)-Complex.I*d*(r:ℂ)^2)^(m+2))⁻¹) (Ioi 0) := by
      simpa only [hdeg,shapeQuadratic,Complex.real_smul,Complex.ofReal_pow,
        div_eq_mul_inv,neg_mul,sub_eq_add_neg] using hr
    simpa only [Nat.succ_eq_add_one,show m+1+1=m+2 by omega,
      Complex.real_smul,div_eq_mul_inv] using hi hb

/-- Source p-particle coordinate version, with k=(p²−1)/2 and either sign of d. -/
theorem odd_shapePeriod_integrable {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) :
    Integrable (fun t : Fin (p-1) → ℝ =>
      let x := shapeCoordinateEquiv (p-1) (WithLp.toLp 2 t)
      (shapeVandermondeSq x:ℂ)/
        ((Q:ℂ)-Complex.I*d*(‖x‖:ℂ)^2)^(derivativeOrder p+1)) := by
  have hp1 : p-1+1=p := by omega
  have hdg : (p-1)-1+(p-1+1)*(p-1) = 2*derivativeOrder p-1 := by
    rw [hp1]
    exact odd_shape_radial_exponent hp hp3
  have hi := odd_shapePeriodIntrinsic_integrable (by omega : 1 ≤ p-1)
    (derivativeOrder_pos hp hp3) hdg hQ hd
  have hc := (shapeCoordinateEquiv_measurePreserving (p-1)).integrable_comp_of_integrable hi
  have hz : ENNReal.ofReal (Real.sqrt ((p-1:ℕ)+1:ℝ)) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (Real.sqrt ((p-1:ℕ)+1:ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hv := (integrable_smul_measure hz ht).mp hc
  exact (PiLp.volume_preserving_toLp (Fin (p-1))).integrable_comp_of_integrable hv

end
end IsingBulk.HT.First
