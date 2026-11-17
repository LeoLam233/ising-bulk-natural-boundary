import IsingBulk.AnisoF002.C03.RegularOffCollision
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The exact first resonances of the regular physical edge branch

The root selected on the complete real cycle is the lower unit root at
the collision.  Its order gives every possible resonant particle index.
For an odd denominator the first odd index is p and the first even index
is 2p; all lower physical coefficients are analytic by the actual pole
locus theorem, rather than by removal of selected terms from a series.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology

theorem upperEdgeRoot_cos {φ : ℝ} (hφ : 0 < φ) (hπ : φ < Real.pi) :
    upperEdgeRoot (Real.cos φ : ℂ) = Complex.exp (-(φ : ℂ) * Complex.I) := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ hπ
  have hd : 1 - (Real.cos φ : ℂ) ^ 2 = ((Real.sin φ) ^ 2 : ℝ) := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq φ] :
      1 - (Real.cos φ) ^ 2 = (Real.sin φ) ^ 2)
  have hsq : Complex.sqrt (((Real.sin φ) ^ 2 : ℝ) : ℂ) = (Real.sin φ : ℂ) := by
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg (Real.sin φ))]
    simp only [Complex.ofReal_re, Real.sqrt_sq hs.le]
  rw [upperEdgeRoot, hd, hsq]
  rw [show -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; rfl,
    Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

def regularRationalAngle (r p : ℕ) : ℝ := 2 * Real.pi * r / p

theorem regularRationalAngle_mem {r p : ℕ} (hr : 0 < r) (hrp : 2 * r < p) :
    0 < regularRationalAngle r p ∧ regularRationalAngle r p < Real.pi := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrp' : 2 * (r : ℝ) < p := by exact_mod_cast hrp
  constructor
  · exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hr') hp
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [Real.pi_pos]

theorem upperEdgeRoot_rational_primitive {r p : ℕ} (hr : 0 < r) (hrp : 2 * r < p)
    (hcop : r.Coprime p) :
    IsPrimitiveRoot (upperEdgeRoot (Real.cos (regularRationalAngle r p) : ℂ)) p := by
  have hp : p ≠ 0 := by omega
  have hφ := regularRationalAngle_mem hr hrp
  have h := (Complex.isPrimitiveRoot_exp_of_coprime r p hp hcop).inv
  rw [upperEdgeRoot_cos hφ.1 hφ.2]
  convert h using 1
  rw [← Complex.exp_neg]
  congr 1
  simp only [regularRationalAngle, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast]
  ring

theorem upperEdgeRoot_rational_resonance_iff {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (N : ℕ) :
    upperEdgeRoot (Real.cos (regularRationalAngle r p) : ℂ) ^ N = 1 ↔ p ∣ N :=
  (upperEdgeRoot_rational_primitive hr hrp hcop).pow_eq_one_iff_dvd N

theorem odd_denominator_even_nonresonance {p N : ℕ} (hp : Odd p)
    (hN : 0 < N) (heven : Even N) (hlt : N < 2 * p) : ¬ p ∣ N := by
  rintro ⟨k, hk⟩
  have hp' : 0 < p := by omega
  have hklt : k < 2 := by nlinarith
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    simp [hz] at hk
    omega
  have hkone : k = 1 := by omega
  have hNp : N = p := by simpa [hkone] using hk
  obtain ⟨j, hj⟩ := hp
  obtain ⟨l, hl⟩ := heven
  omega

namespace RegularEdgeCompleteControl

theorem rational_lower_odd_analytic {r p : ℕ} (hr : 0 < r) (hrp : 2 * r < p)
    (hcop : r.Coprime p) {a : ℂ → ℂ}
    (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) {n : ℕ} (hn : n + 1 < p) :
    AnalyticAt ℂ (edgeParticleCoefficient
      (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a n) 0 := by
  have hφ := regularRationalAngle_mem hr hrp
  have hb : |Real.cos (regularRationalAngle r p)| < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mp
    have hs := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    nlinarith [Real.sin_sq_add_cos_sq (regularRationalAngle r p)]
  apply d.nonresonant_particle_analytic hb ha
  intro he
  exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hn
    ((upperEdgeRoot_rational_resonance_iff hr hrp hcop (n + 1)).mp he)

theorem rational_lower_even_analytic {r p : ℕ} (hr : 0 < r) (hrp : 2 * r < p)
    (hcop : r.Coprime p) (hp : Odd p) {a : ℂ → ℂ}
    (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) {n : ℕ} (hn : n + 1 < 2 * p) (heven : Even (n + 1)) :
    AnalyticAt ℂ (edgeParticleCoefficient
      (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a n) 0 := by
  have hφ := regularRationalAngle_mem hr hrp
  have hb : |Real.cos (regularRationalAngle r p)| < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mp
    have hs := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    nlinarith [Real.sin_sq_add_cos_sq (regularRationalAngle r p)]
  apply d.nonresonant_particle_analytic hb ha
  intro he
  exact odd_denominator_even_nonresonance hp (Nat.succ_pos _) heven hn
    ((upperEdgeRoot_rational_resonance_iff hr hrp hcop (n + 1)).mp he)

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
