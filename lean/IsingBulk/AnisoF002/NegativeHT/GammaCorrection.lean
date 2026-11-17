import IsingBulk.AnisoF002.NegativeHT.FactorialRectangle
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Exact finite-product gamma correction and discrete curvature remainder

This proves the gamma contribution from finite sums before taking any
asymptotic limit. In particular the second difference is controlled at the
scale of the square of the exponent increment, rather than by subtracting
three coarse pointwise O(a²/j) estimates.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open scoped BigOperators

noncomputable section

/-- Equality with the literal gamma quotient in the frozen formula. -/
theorem gammaQuotient_eq_Gamma (j a : ℕ) (ha : a≤j) :
    gammaQuotient j a = Real.Gamma ((j:ℝ)+1-a)/Real.Gamma ((j:ℝ)+1) := by
  have he : (j:ℝ)+1-a = ((j-a:ℕ):ℝ)+1 := by
    rw [Nat.cast_sub ha]
    ring
  rw [he, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  rfl

/-- F002's exact finite-product correction E_j(a). -/
def logGammaCorrection (J : ℝ) (a : ℕ) : ℝ :=
  ∑ r ∈ Finset.range a, -Real.log (1-(r:ℝ)/J)

theorem logGammaCorrection_step (J : ℝ) (a : ℕ) :
    logGammaCorrection J (a+1) =
      logGammaCorrection J a - Real.log (1-(a:ℝ)/J) := by
  simp only [logGammaCorrection, Finset.sum_range_succ, sub_eq_add_neg]

/-- Exact gamma-factor recurrence in the particle exponent. -/
theorem gammaQuotient_particle_step (j a : ℕ) (ha : a<j) :
    gammaQuotient j a = ((j:ℝ)-a)*gammaQuotient j (a+1) := by
  have he : j-a = j-(a+1)+1 := by omega
  have hc : ((j-(a+1):ℕ):ℝ)+1 = (j:ℝ)-a := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  unfold gammaQuotient
  rw [he, Nat.factorial_succ]
  push_cast
  rw [hc]
  ring

/-- The correction sum equals the exact factorial quotient, not an asymptotic
replacement for it. -/
theorem log_gammaQuotient_exact (j a : ℕ) (hj : 0<j) (ha : a≤j) :
    Real.log (gammaQuotient j a) = -(a:ℝ)*Real.log (j:ℝ) +
      logGammaCorrection (j:ℝ) a := by
  induction a with
  | zero => simp [gammaQuotient, logGammaCorrection, Nat.factorial_ne_zero]
  | succ a ih =>
      have haj : a<j := by omega
      have hi := ih (by omega)
      have hj' : (0:ℝ)<j := by exact_mod_cast hj
      have hja : (0:ℝ)<(j:ℝ)-a := sub_pos.mpr (by exact_mod_cast haj)
      have hsmall : (0:ℝ)<1-(a:ℝ)/(j:ℝ) := by
        apply sub_pos.mpr
        exact (div_lt_one hj').mpr (by exact_mod_cast haj)
      have he : (j:ℝ)-(a:ℝ) = (j:ℝ)*(1-(a:ℝ)/(j:ℝ)) := by field_simp
      have hlog := congrArg Real.log (gammaQuotient_particle_step j a haj)
      rw [Real.log_mul hja.ne' (gammaQuotient_pos j (a+1)).ne', he,
        Real.log_mul hj'.ne' hsmall.ne'] at hlog
      rw [logGammaCorrection_step]
      push_cast
      linarith

/-- Lipschitz control of one exact logarithmic factor inside the half-order
range. Both the monotonicity and upper bound are retained. -/
theorem gamma_factor_increment_bounds (J r s : ℝ)
    (hJ : 0<J) (hrs : r≤s) (hs : 2*s≤J) :
    0 ≤ (-Real.log (1-s/J))-(-Real.log (1-r/J)) ∧
      (-Real.log (1-s/J))-(-Real.log (1-r/J)) ≤ 2*(s-r)/J := by
  have hhalf : (1/2:ℝ) ≤ 1-s/J := by
    have : s/J≤(1/2:ℝ) := (div_le_iff₀ hJ).mpr (by linarith)
    linarith
  have hx : 0<1-s/J := by linarith
  have hy : 0≤(s-r)/J := div_nonneg (by linarith) hJ.le
  have h := log_increment_bounds hx hy
  have he : 1-s/J+(s-r)/J = 1-r/J := by ring
  rw [he] at h
  have hub : ((s-r)/J)/(1-s/J) ≤ 2*(s-r)/J := by
    calc
      _ ≤ ((s-r)/J)/(1/2:ℝ) := div_le_div_of_nonneg_left hy (by norm_num) hhalf
      _ = _ := by ring
  constructor <;> linarith [h.1, h.2]

theorem logGammaCorrection_block (J : ℝ) (a d : ℕ) :
    logGammaCorrection J (a+d)-logGammaCorrection J a =
      ∑ i ∈ Finset.range d, -Real.log (1-((a+i:ℕ):ℝ)/J) := by
  unfold logGammaCorrection
  rw [Finset.sum_range_add]
  ring

/-- Pair equal-length exponent blocks before bounding the leftover block.
This identity is the source of the smaller discrete second-difference error. -/
theorem logGammaCorrection_rectangle (J : ℝ) (a v w : ℕ) :
    logGammaCorrection J (a+2*v+w) -
      2*logGammaCorrection J (a+v) + logGammaCorrection J a =
    (∑ i ∈ Finset.range v,
      ((-Real.log (1-((a+v+i:ℕ):ℝ)/J))-(-Real.log (1-((a+i:ℕ):ℝ)/J)))) +
    (∑ i ∈ Finset.range w, -Real.log (1-((a+2*v+i:ℕ):ℝ)/J)) := by
  have h0 := logGammaCorrection_block J a v
  have h1 := logGammaCorrection_block J (a+v) v
  have h2 := logGammaCorrection_block J (a+2*v) w
  have he : a+v+v = a+2*v := by omega
  rw [he] at h1
  rw [Finset.sum_sub_distrib]
  linarith

/-- Explicit second-difference gamma correction bound, valid uniformly when
all involved exponents are at most J/2. For F002, v=O_d(n), w=d², so this is
O_d(n²/J), as required for discrete curvature. -/
theorem logGammaCorrection_second_difference_bounds
    (J : ℝ) (a v w : ℕ) (hJ : 0<J) (hrange : 2*((a+2*v+w:ℕ):ℝ) ≤ J) :
    let R := logGammaCorrection J (a+2*v+w) -
      2*logGammaCorrection J (a+v) + logGammaCorrection J a
    0≤R ∧ R≤(2*(v:ℝ)^2+2*(w:ℝ)*((a+2*v+w:ℕ):ℝ))/J := by
  dsimp only
  rw [logGammaCorrection_rectangle]
  have hp : ∀ i ∈ Finset.range v,
      0 ≤ (-Real.log (1-((a+v+i:ℕ):ℝ)/J))-(-Real.log (1-((a+i:ℕ):ℝ)/J)) ∧
      (-Real.log (1-((a+v+i:ℕ):ℝ)/J))-(-Real.log (1-((a+i:ℕ):ℝ)/J)) ≤ 2*(v:ℝ)/J := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : ((a+v+i:ℕ):ℝ) ≤ ((a+2*v+w:ℕ):ℝ) := by exact_mod_cast (show a+v+i≤a+2*v+w by omega)
    have h := gamma_factor_increment_bounds J ((a+i:ℕ):ℝ) ((a+v+i:ℕ):ℝ) hJ
      (by exact_mod_cast (show a+i≤a+v+i by omega)) (by linarith)
    have he : ((a+v+i:ℕ):ℝ)-((a+i:ℕ):ℝ) = (v:ℝ) := by push_cast; ring
    rwa [he] at h
  have ht : ∀ i ∈ Finset.range w,
      0≤-Real.log (1-((a+2*v+i:ℕ):ℝ)/J) ∧
      -Real.log (1-((a+2*v+i:ℕ):ℝ)/J) ≤ 2*((a+2*v+w:ℕ):ℝ)/J := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : ((a+2*v+i:ℕ):ℝ) ≤ ((a+2*v+w:ℕ):ℝ) := by exact_mod_cast (show a+2*v+i≤a+2*v+w by omega)
    have h := gamma_factor_increment_bounds J 0 ((a+2*v+i:ℕ):ℝ) hJ (by positivity) (by linarith)
    simp only [zero_div, sub_zero, Real.log_one, neg_zero] at h
    refine ⟨h.1, h.2.trans ?_⟩
    exact div_le_div_of_nonneg_right (by linarith) hJ.le
  constructor
  · exact add_nonneg (Finset.sum_nonneg (fun i hi => (hp i hi).1))
      (Finset.sum_nonneg (fun i hi => (ht i hi).1))
  · calc
      _ ≤ (∑ i ∈ Finset.range v, 2*(v:ℝ)/J) +
          (∑ i ∈ Finset.range w, 2*((a+2*v+w:ℕ):ℝ)/J) :=
        add_le_add (Finset.sum_le_sum (fun i hi => (hp i hi).2))
          (Finset.sum_le_sum (fun i hi => (ht i hi).2))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Exact exponent increments on the odd particle progression with step 2p. -/
theorem particleExponent_progression (k p : ℕ) :
    particleExponent (2*(k+p)+1) = particleExponent (2*k+1) + 2*p*(2*k+p+1) ∧
    particleExponent (2*(k+2*p)+1) = particleExponent (2*k+1) +
      2*(2*p*(2*k+p+1)) + 4*p^2 := by
  simp only [particleExponent_odd]
  constructor <;> ring

/-- The gamma correction bound on exactly the allowed odd-particle lattice,
with the squared step retained explicitly. -/
theorem odd_particle_gamma_curvature_bounds (J : ℝ) (k p : ℕ) (hJ : 0<J)
    (hrange : 2*(particleExponent (2*(k+2*p)+1):ℝ)≤J) :
    let v : ℕ := 2*p*(2*k+p+1)
    let w : ℕ := 4*p^2
    let R := logGammaCorrection J (particleExponent (2*(k+2*p)+1)) -
      2*logGammaCorrection J (particleExponent (2*(k+p)+1)) +
      logGammaCorrection J (particleExponent (2*k+1))
    0≤R ∧ R≤(2*(v:ℝ)^2+2*(w:ℝ)*(particleExponent (2*(k+2*p)+1):ℝ))/J := by
  obtain ⟨hm, ht⟩ := particleExponent_progression k p
  dsimp only
  rw [ht, hm]
  rw [ht] at hrange
  exact logGammaCorrection_second_difference_bounds J (particleExponent (2*k+1))
    (2*p*(2*k+p+1)) (4*p^2) hJ hrange

end

end IsingBulk.AnisoF002.NegativeHT
