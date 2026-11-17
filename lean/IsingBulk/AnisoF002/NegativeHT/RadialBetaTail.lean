import IsingBulk.AnisoF002.NegativeHT.UniformCurvaturePhase

/-!
# Integrated radial tail for the negative-HT real-cycle beta law

F002 `eq:rc-radial-tail` uses the whole positive radial half-line and the
exact beta normalizer.  This file proves the real normalizer, its order
comparison, and an exponentially small integrated tail.  All powers in
the integral are integer powers; the flexible indices J,j,k permit
integer rounding in the eventual Taylor-order selection.

No physical pole-density error or angular exponential moment is assumed
to have been proved by this radial calculation.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Literal positive radial density after the paper's change of radius. -/
def radialBetaDensity (α j : ℕ) (x : ℝ) : ℝ :=
  x^(α-1)/(1+x)^(j+1)

/-- The full normalizing integral, with no finite-radius truncation. -/
def radialBeta (α j : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), radialBetaDensity α j x

theorem radialBetaDensity_nonneg (α j : ℕ) {x : ℝ} (hx : 0≤x) :
    0≤radialBetaDensity α j x := by
  unfold radialBetaDensity
  positivity

theorem integrableOn_radialBetaDensity (α j : ℕ) (hα : 0<α) (hj : α≤j) :
    IntegrableOn (radialBetaDensity α j) (Ioi (0 : ℝ)) := by
  have he : α-1+(j-α)+2 = j+1 := by omega
  have hc : ∀ x : ℝ, complexRadialIntegrand (α-1) (j-α) 1 1 x =
      (radialBetaDensity α j x : ℂ) := by
    intro x
    simp only [complexRadialIntegrand, radialBetaDensity, he, Complex.ofReal_one, one_mul]
    push_cast
    rfl
  have hi := integrableOn_complexRadialIntegrand (α-1) (j-α)
    (by norm_num : (0:ℝ)<1) (by norm_num : 0<(1:ℂ).re)
  rw [funext hc] at hi
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hi.re

/-- Exact normalization of the real beta density, deduced from the
already proved complex real-cycle integral. -/
theorem radialBeta_eq (α j : ℕ) (hα : 0<α) (hj : α≤j) :
    radialBeta α j = (Nat.factorial (α-1) : ℝ)*gammaQuotient j α := by
  have he := complexRadialPeriod_eq α j hα hj
    (by norm_num : (0:ℝ)<1) (by norm_num : 0<(1:ℂ).re)
  have hp : complexRadialPeriod α j 1 1 = (radialBeta α j : ℂ) := by
    unfold complexRadialPeriod radialBeta radialBetaDensity
    simp only [Complex.ofReal_one, one_mul]
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    push_cast
    rfl
  rw [hp] at he
  simp only [Complex.ofReal_one, one_pow, mul_one] at he
  apply Complex.ofReal_injective
  convert he using 1
  unfold gammaQuotient
  push_cast
  ring

theorem radialBeta_pos (α j : ℕ) (hα : 0<α) (hj : α≤j) :
    0<radialBeta α j := by
  rw [radialBeta_eq α j hα hj]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos (α-1)) (gammaQuotient_pos j α)

/-- Exact factorial quotients control the normalizer ratio for every
integer pair of orders in the required half-order range. -/
theorem gammaQuotient_half_order_bound (α J j : ℕ)
    (hα : 2*α≤J) (hj : j≤2*J) (hαj : α≤j) :
    gammaQuotient J α ≤ (4:ℝ)^α*gammaQuotient j α := by
  induction α with
  | zero => simp [gammaQuotient, Nat.factorial_ne_zero]
  | succ α ih =>
    have haJ : α<J := by omega
    have haj : α<j := by omega
    have hJ : (0:ℝ)<(J:ℝ)-α := sub_pos.mpr (by exact_mod_cast haJ)
    have hjp : (0:ℝ)<(j:ℝ)-α := sub_pos.mpr (by exact_mod_cast haj)
    have hr : ((j:ℝ)-α)/((J:ℝ)-α) ≤ 4 := by
      apply (div_le_iff₀ hJ).mpr
      have h1 : 2*(α:ℝ)≤J := by exact_mod_cast (show 2*α≤J by omega)
      have h2 : (j:ℝ)≤2*J := by exact_mod_cast hj
      linarith
    have hQJ : gammaQuotient J (α+1) = gammaQuotient J α/((J:ℝ)-α) := by
      apply (eq_div_iff hJ.ne').mpr
      simpa only [mul_comm] using (gammaQuotient_particle_step J α haJ).symm
    have hQj : gammaQuotient j (α+1) = gammaQuotient j α/((j:ℝ)-α) := by
      apply (eq_div_iff hjp.ne').mpr
      simpa only [mul_comm] using (gammaQuotient_particle_step j α haj).symm
    rw [hQJ, hQj]
    calc
      _ ≤ ((4:ℝ)^α*gammaQuotient j α)/((J:ℝ)-α) :=
        div_le_div_of_nonneg_right (ih (by omega) (by omega)) hJ.le
      _ = (4:ℝ)^α*(gammaQuotient j α/((j:ℝ)-α))*
          (((j:ℝ)-α)/((J:ℝ)-α)) := by field_simp
      _ ≤ (4:ℝ)^α*(gammaQuotient j α/((j:ℝ)-α))*4 := by
        exact mul_le_mul_of_nonneg_left hr
          (mul_nonneg (by positivity) (div_nonneg (gammaQuotient_pos j α).le hjp.le))
      _ = _ := by rw [pow_succ]; ring

/-- The whole beta normalizer ratio costs at most 4 to the particle exponent. -/
theorem radialBeta_half_order_bound (α J j : ℕ)
    (hα0 : 0<α) (hα : 2*α≤J) (hj : j≤2*J) (hαj : α≤j) :
    radialBeta α J ≤ (4:ℝ)^α*radialBeta α j := by
  rw [radialBeta_eq α J hα0 (by omega), radialBeta_eq α j hα0 hαj]
  have he := mul_le_mul_of_nonneg_left
    (gammaQuotient_half_order_bound α J j hα hj hαj)
    (show (0:ℝ)≤Nat.factorial (α-1) by positivity)
  nlinarith

/-- Integrating the actual tail retains a full exact beta normalizer.
There is no unintegrated pointwise bound left in the conclusion. -/
theorem integral_radialBeta_tail_le (α J k : ℕ) {R : ℝ}
    (hα : 0<α) (hJ : α≤J) (hR : 0≤R) :
    (∫ x in Ioi R, radialBetaDensity α (J+k) x) ≤
      radialBeta α J/(1+R)^k := by
  have hs : Ioi R ⊆ Ioi (0:ℝ) := fun _ hx => lt_of_le_of_lt hR hx
  have hi := integrableOn_radialBetaDensity α J hα hJ
  have ht := integrableOn_radialBetaDensity α (J+k) hα (by omega)
  have h1 : 0<1+R := by linarith
  have hpoint : ∀ x ∈ Ioi R,
      radialBetaDensity α (J+k) x ≤ ((1+R)^k)⁻¹*radialBetaDensity α J x := by
    intro x hx
    have hxR : R<x := hx
    have hx0 : 0<x := hs hx
    have hxp : 0<1+x := by linarith
    have he : radialBetaDensity α (J+k) x =
        radialBetaDensity α J x/(1+x)^k := by
      unfold radialBetaDensity
      rw [show J+k+1 = (J+1)+k by omega, pow_add]
      exact div_mul_eq_div_div _ _ _
    rw [he]
    calc
      _ ≤ radialBetaDensity α J x/(1+R)^k := by
        apply div_le_div_of_nonneg_left (radialBetaDensity_nonneg α J hx0.le)
          (pow_pos h1 k)
        exact pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = _ := by ring
  calc
    _ ≤ ∫ x in Ioi R, ((1+R)^k)⁻¹*radialBetaDensity α J x :=
      setIntegral_mono_on (ht.mono_set hs) ((hi.mono_set hs).const_mul _)
        measurableSet_Ioi hpoint
    _ = ((1+R)^k)⁻¹*(∫ x in Ioi R, radialBetaDensity α J x) := integral_const_mul _ _
    _ ≤ ((1+R)^k)⁻¹*radialBeta α J := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact radialBetaDensity_nonneg α J hx.le
      · exact Filter.Eventually.of_forall hs
    _ = _ := by ring

/-- Normalized version of the full radial-tail estimate, valid over all
radii beyond R and every integer order satisfying the half-order range. -/
theorem normalized_radialBeta_tail_le (α J j k : ℕ) {R : ℝ}
    (hα0 : 0<α) (hα : 2*α≤J) (hj : j≤2*J) (hαj : α≤j) (hR : 0≤R) :
    (∫ x in Ioi R, radialBetaDensity α (J+k) x)/radialBeta α j ≤
      (4:ℝ)^α/(1+R)^k := by
  have hZ := radialBeta_pos α j hα0 hαj
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ radialBeta α J/(1+R)^k := integral_radialBeta_tail_le α J k hα0 (by omega) hR
    _ ≤ ((4:ℝ)^α*radialBeta α j)/(1+R)^k := by
      apply div_le_div_of_nonneg_right
        (radialBeta_half_order_bound α J j hα0 hα hj hαj)
      positivity
    _ = _ := by ring

/-- Explicit exponential suppression of the scalar tail factor. -/
theorem radial_tail_factor_exp_bound (α k : ℕ) {R : ℝ}
    (hR0 : 0≤R) (hR1 : R≤1) (hlarge : 8*(α:ℝ)≤(k:ℝ)*R) :
    (4:ℝ)^α/(1+R)^k ≤ Real.exp (-(α:ℝ)) := by
  have hp : 0<1+R := by linarith
  have hlog : R/2≤Real.log (1+R) := by
    calc
      _ ≤ R/(1+R) := div_le_div_of_nonneg_left hR0 hp (by linarith)
      _ = 1-(1+R)⁻¹ := by field_simp; ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos hp
  have hlog4 := Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
  apply (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(4:ℝ)^α/(1+R)^k)).mp
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hA := mul_le_mul_of_nonneg_left hlog4 (show (0:ℝ)≤α by positivity)
  have hB := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤k by positivity)
  nlinarith

/-- The actual integrated normalized beta tail is exponentially small. -/
theorem normalized_radialBeta_tail_exp (α J j k : ℕ) {R : ℝ}
    (hα0 : 0<α) (hα : 2*α≤J) (hj : j≤2*J) (hαj : α≤j)
    (hR0 : 0≤R) (hR1 : R≤1) (hlarge : 8*(α:ℝ)≤(k:ℝ)*R) :
    (∫ x in Ioi R, radialBetaDensity α (J+k) x)/radialBeta α j ≤
      Real.exp (-(α:ℝ)) := by
  exact (normalized_radialBeta_tail_le α J j k hα0 hα hj hαj hR0).trans
    (radial_tail_factor_exp_bound α k hR0 hR1 hlarge)

/-- An explicit full-radius estimate at F002's cutoff `32*n^2/j`,
for Taylor orders divisible by four.  The eventual Taylor-order selection
still needs to justify restriction to this subsequence. -/
theorem firstWinding_radial_tail_exp (n k : ℕ)
    (hn : 2≤n) (hlarge : 8*n^2≤k) :
    (∫ x in Ioi (32*(n:ℝ)^2/(4*k)),
        radialBetaDensity (particleExponent n) (3*k) x) /
      radialBeta (particleExponent n) (4*k) ≤
        Real.exp (-((particleExponent n : ℕ):ℝ)) := by
  have hn2 : 4≤n^2 := by nlinarith
  have hk : 0<k := by omega
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hα : 0<particleExponent n := by
    unfold particleExponent
    omega
  have hαk : particleExponent n≤k := (particleExponent_le_sq n).trans (by omega)
  have hR : 0≤32*(n:ℝ)^2/(4*k) := by positivity
  have hR1 : 32*(n:ℝ)^2/(4*k)≤1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*k)).mpr
    have he : 8*(n:ℝ)^2≤k := by exact_mod_cast hlarge
    linarith
  have hmul : 8*(particleExponent n:ℝ)≤
      (k:ℝ)*(32*(n:ℝ)^2/(4*k)) := by
    rw [show (k:ℝ)*(32*(n:ℝ)^2/(4*k)) = 8*(n:ℝ)^2 by field_simp; ring]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast particleExponent_le_sq n)
      (by norm_num)
  simpa only [show 2*k+k = 3*k by omega] using
    normalized_radialBeta_tail_exp (particleExponent n) (2*k) (4*k) k
      hα (by omega) (by omega) (by omega) hR hR1 hmul

/-- The same actual integrated tail has the uniform Gaussian-in-n bound
required after absorbing the radial perturbation. -/
theorem firstWinding_radial_tail_gaussian (n k : ℕ)
    (hn : 2≤n) (hlarge : 8*n^2≤k) :
    (∫ x in Ioi (32*(n:ℝ)^2/(4*k)),
        radialBetaDensity (particleExponent n) (3*k) x) /
      radialBeta (particleExponent n) (4*k) ≤
        Real.exp (-(n:ℝ)^2/4) := by
  have hn2 : 4≤n^2 := by nlinarith
  have hr := Nat.mod_lt (n^2-1) (by norm_num : 0<2)
  have hd := Nat.mod_add_div (n^2-1) 2
  have hα : n^2≤4*particleExponent n := by
    unfold particleExponent
    omega
  have hα' : (n:ℝ)^2≤4*(particleExponent n:ℝ) := by exact_mod_cast hα
  exact (firstWinding_radial_tail_exp n k hn hlarge).trans
    (Real.exp_le_exp.mpr (by linarith))

end

end IsingBulk.AnisoF002.NegativeHT
