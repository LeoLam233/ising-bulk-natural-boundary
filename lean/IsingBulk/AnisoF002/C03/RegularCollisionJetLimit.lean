import IsingBulk.AnisoF002.C03.RegularCollisionKernel
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# All actual scaled collision derivatives

The exact filled density identity is differentiated in the blown-up
temperature. Joint analyticity then gives the limit of every actual
temperature jet, with its factorial and particle-number factors. These
are pointwise limits of the original complete density, before integration.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem iteratedDeriv_affine_reciprocal (j : ℕ) (A C t : ℂ) :
    iteratedDeriv j (fun u => (A * u + C)⁻¹) t =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * A ^ j / (A * t + C) ^ (j + 1) := by
  rw [iteratedDeriv_comp_mul_unconditional j (fun u : ℂ => (u + C)⁻¹),
    iteratedDeriv_comp_add_const, iteratedDeriv_eq_iterate]
  change A ^ j * (deriv^[j] Inv.inv) (A * t + C) = _
  rw [iter_deriv_inv,
    show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  ring

theorem collisionBlowupDensity_jet_center {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (j : ℕ) (t : ℂ) :
    iteratedDeriv j (fun u => collisionBlowupDensity b a x (0, u)) t =
      (2 * edgeVandermondeSquared x *
        edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) /
          deriv upperEdgePhase (b : ℂ)) *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (N : ℂ) ^ j /
          ((N : ℂ) * t + a 0 / 2 * ∑ i, x i ^ 2) ^ (j + 1)) := by
  have he : (fun u => collisionBlowupDensity b a x (0, u)) =
      fun u => (2 * edgeVandermondeSquared x *
        edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) /
          deriv upperEdgePhase (b : ℂ)) *
        ((N : ℂ) * u + a 0 / 2 * ∑ i, x i ^ 2)⁻¹ := by
    funext u
    rw [collisionBlowupDensity_center]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_affine_reciprocal]

theorem collisionBlowupDensity_jet_exact {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (s t : ℂ) (hs : s ≠ 0)
    (hres : upperEdgeRoot (b : ℂ) ^ N = 1) (j : ℕ) :
    s ^ (2 * j + 2) *
      iteratedDeriv j (fun u => edgeJointDensity (affineEdgeCenter b) a
        (u, fun i => s * x i)) (s ^ 2 * t) =
      s ^ (2 * N.choose 2) *
        iteratedDeriv j (fun u => collisionBlowupDensity b a x (s, u)) t := by
  have he : (fun u => s ^ 2 * edgeJointDensity (affineEdgeCenter b) a
      (s ^ 2 * u, fun i => s * x i)) =
      (fun u => s ^ (2 * N.choose 2) * collisionBlowupDensity b a x (s, u)) := by
    funext u
    exact collisionBlowupDensity_exact b a x s u hs hres
  have hj := congrArg (fun f : ℂ → ℂ => iteratedDeriv j f t) he
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_mul_unconditional j
      (fun u => edgeJointDensity (affineEdgeCenter b) a (u, fun i => s * x i)) (s ^ 2) t,
    ← pow_mul, ← mul_assoc, ← pow_add] at hj
  convert hj using 1
  congr 2
  omega

theorem collisionBlowupDensity_jet_quotient {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (s t : ℂ) (hs : s ≠ 0)
    (hres : upperEdgeRoot (b : ℂ) ^ N = 1) (j : ℕ) :
    (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
      iteratedDeriv j (fun u => edgeJointDensity (affineEdgeCenter b) a
        (u, fun i => s * x i)) (s ^ 2 * t) =
      iteratedDeriv j (fun u => collisionBlowupDensity b a x (s, u)) t := by
  apply (mul_left_cancel₀ (pow_ne_zero (2 * N.choose 2) hs))
  have he := collisionBlowupDensity_jet_exact b a x s t hs hres j
  field_simp [hs]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using he

theorem complete_density_scaled_jet_limit {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (d : RegularEdgeControl (affineEdgeCenter b) a) (hN : 0 < N)
    (hb : |b| < 1) (ha : 0 < (a 0).im) (hres : upperEdgeRoot (b : ℂ) ^ N = 1)
    (x : Fin N → ℝ) (j : ℕ) :
    Tendsto (fun s : ℂ => (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
      iteratedDeriv j (fun u => edgeJointDensity (affineEdgeCenter b) a
        (u, fun i => s * (x i : ℂ))) (s ^ 2 * Complex.I))
      (𝓝[≠] (0 : ℂ))
      (𝓝 ((2 * edgeVandermondeSquared (complexAngles x) *
        edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) /
          deriv upperEdgePhase (b : ℂ)) *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (N : ℂ) ^ j /
          ((N : ℂ) * Complex.I + a 0 / 2 * ∑ i, (x i : ℂ) ^ 2) ^ (j + 1)))) := by
  have hG := collisionBlowupTotal_center_ne_zero hN hb ha x
  have han := collisionBlowupDensity_analytic d hb (complexAngles x) Complex.I hG
  have hc := (second_parameter_jet_continuous han j).tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rw [collisionBlowupDensity_jet_center] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (collisionBlowupDensity_jet_quotient b a (complexAngles x) s Complex.I hs hres j).symm

end
end IsingBulk.AnisoF002.RegularTail.C03
