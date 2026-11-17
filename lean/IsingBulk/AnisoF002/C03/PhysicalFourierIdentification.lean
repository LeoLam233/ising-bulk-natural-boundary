import IsingBulk.AnisoF002.C03.PhysicalVerticalDensity
import IsingBulk.AnisoF002.C03.PhysicalLatticeExchange
import IsingBulk.HT.Contour.FourierTorusCoordinates

/-!
# Exact full-lattice to constrained-angular identification

The separately audited generic total-angle shear supplies the literal
negative Fourier index.  Actual lattice summability supplies Fourier
inversion; the canonical root gap then justifies the remaining integer
transfer sum.  The complete original finite coefficient, its onsite
term, its factorial, and its independent angular measure are retained.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic
  IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry
open scoped Topology BigOperators
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem literal_horizontal_lattice_sum (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (hs : Summable (fun v : LatticeSite => latticeCoefficient (n + 1) (realB lam x) (realC lam x) v))
    (m : ℤ) :
    (∑' l : ℤ, latticeCoefficient (n + 1) (realB lam x) (realC lam x) (m, l)) =
      ((n + 1).factorial : ℂ)⁻¹ *
        ∫ q, literalRealVerticalDensity lam x m (flatConstrainedAngles q) ∂regularAngularProbability n := by
  let F := literalRealVerticalDensity (N := n + 1) lam x m
  have hF : Continuous F := literal_verticalDensity_continuous hlam hx hp m
  have hperiod : CoordinatePeriodic (n + 1) F := literal_verticalDensity_periodic hlam hx hp m
  let G := torusMeanCircle n F hF hperiod
  have he (l : ℤ) : latticeCoefficient (n + 1) (realB lam x) (realC lam x) (m, l) =
      ((n + 1).factorial : ℂ)⁻¹ * fourierCoeff G (-l) := by
    rw [show fourierCoeff G (-l) = _ from (torus_exponential_coefficient n F hF hperiod l).symm]
    unfold latticeCoefficient F literalRealVerticalDensity
    ring
  have hfac : ((n + 1).factorial : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hsc : Summable (fun l : ℤ => fourierCoeff G (-l)) := by
    apply (summable_mul_left_iff hfac).mp
    simpa only [he] using hs.prod_factor m
  have hsc' : Summable (fourierCoeff G) := by
    have hh := hsc.comp_injective (neg_injective : Function.Injective (fun l : ℤ => -l))
    change Summable (fun l : ℤ => fourierCoeff G (-(-l))) at hh
    simpa only [neg_neg] using hh
  have hzero : (∑' l : ℤ, fourierCoeff G l) = G 0 := by
    have hh := has_pointwise_sum_fourier_series_of_summable hsc' (0 : AddCircle (2 * Real.pi))
    simpa only [fourier_eval_zero, smul_eq_mul, mul_one] using hh.tsum_eq
  calc
    _ = ((n + 1).factorial : ℂ)⁻¹ * ∑' l : ℤ, fourierCoeff G (-l) := by
      simp_rw [he]
      rw [tsum_mul_left]
    _ = ((n + 1).factorial : ℂ)⁻¹ * G 0 := by
      have hn := (Equiv.neg ℤ).tsum_eq (fourierCoeff G)
      change (∑' l : ℤ, fourierCoeff G (-l)) = ∑' l : ℤ, fourierCoeff G l at hn
      rw [hn, hzero]
    _ = ((n + 1).factorial : ℂ)⁻¹ *
        (((2 * (Real.pi : ℂ))⁻¹) ^ n * multiAngleIntegral n (fun q => F (shapeExtend q))) := by
      rw [show G 0 = _ from torusMeanCircle_zero n F hF hperiod]
    _ = _ := by
      have hc : Continuous (fun q : Fin n → ℝ =>
          literalRealVerticalDensity lam x m (flatConstrainedAngles q)) :=
        (literal_verticalDensity_continuous hlam hx hp m).comp (literal_flatAngles_continuous n)
      exact congrArg (fun t : ℂ => ((n + 1).factorial : ℂ)⁻¹ * t)
        (regularAngularProbability_eq_original _ hc
          (literal_constrainedVerticalDensity_periodic hlam hx hp m)).symm

theorem literal_lattice_tsum_eq_canonical_coefficient (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (hs : Summable (fun v : LatticeSite => latticeCoefficient (n + 1) (realB lam x) (realC lam x) v)) :
    (∑' v : LatticeSite, latticeCoefficient (n + 1) (realB lam x) (realC lam x) v) =
      canonicalAngularCoefficientF002 lam n (x : ℂ) := by
  rw [hs.tsum_prod]
  simp_rw [literal_horizontal_lattice_sum n hlam hx hp hs]
  rw [tsum_mul_left, literal_constrainedVerticalDensity_integral_tsum n hlam hx hp]
  rfl

theorem literal_lattice_tsum_eq_published_angular (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (hs : Summable (fun v : LatticeSite => latticeCoefficient (n + 1) (realB lam x) (realC lam x) v)) :
    (∑' v : LatticeSite, latticeCoefficient (n + 1) (realB lam x) (realC lam x) v) =
      angularCoefficient n (realB lam x) (realC lam x) := by
  rw [literal_lattice_tsum_eq_canonical_coefficient n hlam hx hp hs,
    canonical_coefficient_eq_published_real n hlam hx hp]

theorem literal_canonical_coefficient_of_finite_residues (n : ℕ) {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (ha : ContourAnnulus lam (x : ℂ) r)
    (hrep : ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
      latticeCoefficient N (realB lam x) (realC lam x) v =
        (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v) :
    canonicalAngularCoefficientF002 lam n (x : ℂ) =
      (Real.sqrt (realProduct lam x) : ℂ) ^ (n + 1) * unscaledFullCoefficient (n + 1) lam (x : ℂ) := by
  have hsall := literal_real_joint_summable ha (fun k => k + 1) (fun k => Nat.succ_pos k)
    (fun k l h => by dsimp only at h; omega) (fun k v => hrep _ (Nat.succ_pos k) v)
  have hs : Summable (fun v : LatticeSite => latticeCoefficient (n + 1) (realB lam x) (realC lam x) v) :=
    hsall.prod_factor n
  rw [← literal_lattice_tsum_eq_canonical_coefficient n hlam hx hp hs]
  exact literal_real_lattice_sum (Nat.succ_pos n) hlam hx hp ha (hrep _ (Nat.succ_pos n))

end
end IsingBulk.AnisoF002.RegularTail.C03
