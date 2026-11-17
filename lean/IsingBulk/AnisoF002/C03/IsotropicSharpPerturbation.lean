import IsingBulk.AnisoF002.C03.IsotropicProtectedVariance

/-!
# Sharp joint perturbation of inverse differences

The first secant controls a common parameter increment with the extra
coordinate-separation factor. The same joint secant controls coordinate
increments by the actual endpoint derivative. This is the cancellation
used in the frozen covariance polydisk of radius c Δ / N².
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem triple_complex_norm_sub_le (s s' a a' b b' : ℂ) (ρ : ℝ)
    (hs : ‖s' - s‖ ≤ ρ) (ha : ‖a' - a‖ ≤ ρ) (hb : ‖b' - b‖ ≤ ρ) :
    ‖((s', a', b') : ℂ × ℂ × ℂ) - (s, a, b)‖ ≤ ρ := by
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] using max_le hs (max_le ha hb)

theorem secant_near_endpoint_derivative_bound (U : ℂ × ℂ → ℂ)
    (D : Set (ℂ × ℂ × ℂ)) (L K t ρ : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ p ∈ D, ∀ q ∈ D,
      ‖jointFirstSecant U q - jointFirstSecant U p‖ ≤ L * ‖q - p‖)
    (s s' a a' : ℂ) (hp : (s, a, a) ∈ D) (hq : (s', a', a) ∈ D)
    (hs : ‖s' - s‖ ≤ ρ) (ha : ‖a' - a‖ ≤ ρ)
    (hu : ‖deriv (fun z => U (s, z)) a‖ ≤ K * t) :
    ‖jointFirstSecant U (s', a', a)‖ ≤ K * t + L * ρ := by
  have hρ : 0 ≤ ρ := (norm_nonneg (s' - s)).trans hs
  have hd := triple_complex_norm_sub_le s s' a a' a a ρ hs ha (by simpa using hρ)
  have hsec := (hLip (s, a, a) hp (s', a', a) hq).trans
    (mul_le_mul_of_nonneg_left hd hL)
  have hbase : jointFirstSecant U (s, a, a) = deriv (fun z => U (s, z)) a := by
    simp only [jointFirstSecant, dslope_same]
  have hn := norm_le_norm_sub_add (jointFirstSecant U (s', a', a)) (jointFirstSecant U (s, a, a))
  rw [hbase] at hn hsec
  linarith

/-- Two coordinate increments and one common parameter increment cost
O(t ρ), provided the actual coordinate scale and endpoint derivatives
are O(t). In the F002 shells t=√T, ρ=cΔ/N² and tΔ=r₀. -/
theorem inverse_difference_sharp_perturbation (U : ℂ × ℂ → ℂ)
    (D : Set (ℂ × ℂ × ℂ)) (L K A t Δ ρ : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hΔ : 0 ≤ Δ) (hρ : 0 ≤ ρ) (hΔt : Δ ≤ t) (hρt : ρ ≤ t)
    (hLip : ∀ p ∈ D, ∀ q ∈ D,
      ‖jointFirstSecant U q - jointFirstSecant U p‖ ≤ L * ‖q - p‖)
    (s s' a a' b b' : ℂ)
    (haa : (s, a, a) ∈ D) (hbb : (s, b, b) ∈ D)
    (hab : (s, a, b) ∈ D) (hsab : (s', a, b) ∈ D)
    (hsa : (s', a', a) ∈ D) (hsb : (s', b', b) ∈ D)
    (hs : ‖s' - s‖ ≤ ρ) (ha : ‖a' - a‖ ≤ ρ) (hb : ‖b' - b‖ ≤ ρ)
    (habound : ‖a - b‖ ≤ A * Δ)
    (hUa : ‖deriv (fun z => U (s, z)) a‖ ≤ K * t)
    (hUb : ‖deriv (fun z => U (s, z)) b‖ ≤ K * t) :
    ‖(U (s', a') - U (s', b')) - (U (s, a) - U (s, b))‖ ≤
      (2 * K + 2 * L + L * A) * t * ρ := by
  have hseca := secant_near_endpoint_derivative_bound U D L K t ρ hL hLip
    s s' a a' haa hsa hs ha hUa
  have hsecb := secant_near_endpoint_derivative_bound U D L K t ρ hL hLip
    s s' b b' hbb hsb hs hb hUb
  have hcoordA : ‖U (s', a') - U (s', a)‖ ≤ ρ * (K * t + L * ρ) := by
    rw [jointFirstSecant_difference U s' a' a, norm_mul]
    exact mul_le_mul ha hseca (norm_nonneg _) hρ
  have hcoordB : ‖U (s', b') - U (s', b)‖ ≤ ρ * (K * t + L * ρ) := by
    rw [jointFirstSecant_difference U s' b' b, norm_mul]
    exact mul_le_mul hb hsecb (norm_nonneg _) hρ
  have hsame : ‖jointFirstSecant U (s', a, b) - jointFirstSecant U (s, a, b)‖ ≤
      L * ‖s' - s‖ := by
    have h := hLip (s, a, b) hab (s', a, b) hsab
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
      max_self, max_eq_left (norm_nonneg _)] using h
  have hcommon : ‖(U (s', a) - U (s', b)) - (U (s, a) - U (s, b))‖ ≤
      L * (A * Δ) * ρ := by
    exact (inverse_common_parameter_difference_bound U s s' a b L hsame).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left habound hL) hs (norm_nonneg _)
        (mul_nonneg hL (mul_nonneg hA hΔ)))
  have he : (U (s', a') - U (s', b')) - (U (s, a) - U (s, b)) =
      ((U (s', a') - U (s', a)) - (U (s', b') - U (s', b))) +
      ((U (s', a) - U (s', b)) - (U (s, a) - U (s, b))) := by ring
  rw [he]
  calc
    _ ≤ (‖U (s', a') - U (s', a)‖ + ‖U (s', b') - U (s', b)‖) +
        ‖(U (s', a) - U (s', b)) - (U (s, a) - U (s, b))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * ρ * (K * t + L * ρ) + L * (A * Δ) * ρ := by linarith
    _ = 2 * K * t * ρ + 2 * L * (ρ * ρ) + (L * A) * (Δ * ρ) := by ring
    _ ≤ 2 * K * t * ρ + 2 * L * (t * ρ) + (L * A) * (t * ρ) := by gcongr
    _ = _ := by ring

end IsingBulk.AnisoF002.Isotropic
