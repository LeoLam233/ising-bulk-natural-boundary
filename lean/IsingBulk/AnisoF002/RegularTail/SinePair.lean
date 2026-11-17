import IsingBulk.AnisoF002.RegularTail.CanceledPair

/-!
# The exact retained sine factor in a canceled pair

Frozen and published `eq:cancelpair` and the pairwise step preceding
`eq:fixed-subvandermonde`.  The identity holds for complex angles and
includes the coincident and reciprocal-angle loci.  The quotient is
constructed by a formula, without dividing by a sine which can vanish.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry

theorem exp_pair_sine_identity (q t : ℂ) :
    -(Complex.exp (q * Complex.I) - Complex.exp (t * Complex.I)) ^ 2 /
      (Complex.exp (q * Complex.I) * Complex.exp (t * Complex.I)) =
        4 * Complex.sin ((q - t) / 2) ^ 2 := by
  have he : (Complex.exp (q * Complex.I) - Complex.exp (t * Complex.I)) ^ 2 /
      (Complex.exp (q * Complex.I) * Complex.exp (t * Complex.I)) =
        Complex.exp ((q - t) * Complex.I) + Complex.exp (-(q - t) * Complex.I) - 2 := by
    rw [neg_sub, sub_mul, sub_mul, Complex.exp_sub, Complex.exp_sub]
    field_simp
    ring
  rw [neg_div, he, ← Complex.two_cos]
  have hc : Complex.cos (q - t) = 1 - 2 * Complex.sin ((q - t) / 2) ^ 2 := by
    convert Complex.cos_two_mul_eq_one_sub ((q - t) / 2) using 1
    ring
  rw [hc]
  ring

def sinePairCoefficient (B r s : ℂ) : ℂ := 4 * B * r * s / (1 - r * s) ^ 2

theorem canceledPair_eq_sinePair (B r s q t : ℂ) :
    canceledPair B r s (Complex.exp (q * Complex.I)) (Complex.exp (t * Complex.I)) =
      sinePairCoefficient B r s * Complex.sin ((q - t) / 2) ^ 2 := by
  by_cases hd : 1 - r * s = 0
  · simp [canceledPair, sinePairCoefficient, hd]
  have hi := exp_pair_sine_identity q t
  unfold canceledPair sinePairCoefficient
  calc
    _ = (B * r * s / (1 - r * s) ^ 2) *
        (-(Complex.exp (q * Complex.I) - Complex.exp (t * Complex.I)) ^ 2 /
          (Complex.exp (q * Complex.I) * Complex.exp (t * Complex.I))) := by
      field_simp
    _ = _ := by rw [hi]; ring

def spectralSinePairCoefficientF002 (lam : ℝ) (z : ℂ) (q t : ℝ) : ℂ :=
  sinePairCoefficient (spectralT lam z / spectralS z)
    (spectralSmallRootF002 lam z q) (spectralSmallRootF002 lam z t)

/-- The removable quotient at every real-angle coincidence, including zero
of the sine block. This is an identity, not a pointwise division convention. -/
theorem spectralCanceledPairF002_factorization (lam : ℝ) (z : ℂ) (q t : ℝ) :
    spectralCanceledPairF002 lam z q t =
      spectralSinePairCoefficientF002 lam z q t *
        (Real.sin ((q - t) / 2) ^ 2 : ℝ) := by
  unfold spectralCanceledPairF002 spectralSinePairCoefficientF002
  rw [canceledPair_eq_sinePair]
  simp only [Complex.ofReal_pow, Complex.ofReal_sin, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_ofNat]

theorem spectralSinePairCoefficientF002_analyticAt {lam : ℝ} {z : ℂ} (q t : ℝ)
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0) :
    AnalyticAt ℂ (fun w => spectralSinePairCoefficientF002 lam w q t) z := by
  have hSr : AnalyticAt ℂ spectralS z := by
    change AnalyticAt ℂ Complex.sinh z
    exact Complex.analyticAt_sinh
  have hTr : AnalyticAt ℂ (spectralT lam) z := by
    change AnalyticAt ℂ (fun w : ℂ => Complex.sinh ((lam : ℂ) * w)) z
    exact Complex.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_id)
  have hq := spectralSmallRootF002_analyticAt q hz
  have ht := spectralSmallRootF002_analyticAt t hz
  have hd := pair_root_denominator_ne_zero (spectralSmallRootF002_spec q hz).2
    (spectralSmallRootF002_spec t hz).2
  unfold spectralSinePairCoefficientF002 sinePairCoefficient
  exact (((analyticAt_const.mul (hTr.div hSr hS)).mul hq).mul ht).div
    ((analyticAt_const.sub (hq.mul ht)).pow 2) (pow_ne_zero _ hd)

end
end IsingBulk.AnisoF002.RegularTail
