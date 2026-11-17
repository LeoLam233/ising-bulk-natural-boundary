import IsingBulk.AnisoF002.C03.NegativeAngularPowerBounds
import IsingBulk.AnisoF002.C03.NegativeIntegrandError

/-!
# The actual central radial scaling in the first-winding comparison

The radius is allowed to vary with the particle number and Taylor order.
The four inequalities retain the cubic and quartic angular errors; they
will be integrated with the complete constrained angular law.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

set_option maxHeartbeats 1000000 in
theorem central_radial_scaling {N k A r δ : ℝ}
    (hN : 0 < N) (hk : 0 < k) (hA : 1 ≤ A) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hscale : δ ^ 2 = N ^ 2 / k)
    (hcentral : r ^ 2 ≤ A * N / k) :
    Real.sqrt N * r ≤ A * δ ∧ N * r ^ 2 ≤ A * δ ∧
      k * r ^ 3 / Real.sqrt N ≤ A ^ 2 * δ ∧ k * r ^ 4 ≤ A ^ 2 * δ := by
  have hA0 : 0 ≤ A := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsNsq := Real.sq_sqrt hN.le
  have hkr : k * r ^ 2 ≤ A * N := by
    have hh := (le_div_iff₀ hk).mp hcentral
    nlinarith
  have hNr : N * r ^ 2 ≤ A * δ ^ 2 := by
    calc
      _ ≤ N * (A * N / k) := mul_le_mul_of_nonneg_left hcentral hN.le
      _ = A * δ ^ 2 := by rw [hscale]; ring
  have hAsq : A ≤ A ^ 2 := by nlinarith
  have hNr' : N * r ^ 2 ≤ A ^ 2 * δ ^ 2 :=
    hNr.trans (mul_le_mul_of_nonneg_right hAsq (sq_nonneg δ))
  have hroot : Real.sqrt N * r ≤ A * δ := by
    have he : (Real.sqrt N * r) ^ 2 = N * r ^ 2 := by rw [mul_pow, hsNsq]
    nlinarith [mul_nonneg hA0 hδ]
  have hrad : N * r ^ 2 ≤ A * δ :=
    hNr.trans (mul_le_mul_of_nonneg_left (by nlinarith : δ ^ 2 ≤ δ) hA0)
  have hquot : k * r ^ 2 / N ≤ A := (div_le_iff₀ hN).mpr hkr
  have hcubic : k * r ^ 3 / Real.sqrt N ≤ A ^ 2 * δ := by
    calc
      _ = (k * r ^ 2 / N) * (Real.sqrt N * r) := by
        field_simp
        rw [hsNsq]
      _ ≤ A * (A * δ) := mul_le_mul hquot hroot (by positivity) hA0
      _ = _ := by ring
  have hquartic : k * r ^ 4 ≤ A ^ 2 * δ := by
    calc
      _ = (k * r ^ 2 / N) * (N * r ^ 2) := by field_simp
      _ ≤ A * (A * δ) := mul_le_mul hquot hrad (by positivity) hA0
      _ = _ := by ring
  exact ⟨hroot, hrad, hcubic, hquartic⟩

set_option maxHeartbeats 2000000 in
theorem central_full_error_profile {N k A r δ Z Kρ Kp R D : ℝ} {ell : ℂ}
    (hN : 0 < N) (hk : 0 < k) (hA : 1 ≤ A) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hscale : δ ^ 2 = N ^ 2 / k)
    (hcentral : r ^ 2 ≤ A * N / k) (hZ : 0 ≤ Z)
    (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp) (hR : 0 ≤ R)
    (hD : 2 / N ^ 2 ≤ D)
    (hell : ‖ell‖ ≤ Kρ * (Real.sqrt (N * r ^ 2) + N * r ^ 2))
    (herr : R ≤ Kp / N *
      (r ^ 3 * Real.sqrt Z / Real.sqrt N / N + r ^ 4 * Z / N + r ^ 4 / N)) :
    ‖ell‖ + 2 * k * R / D ≤ 2 * A ^ 2 * (Kρ + Kp) * δ * (1 + Z) := by
  obtain ⟨hroot, hrad, hcubic, hquartic⟩ :=
    central_radial_scaling hN hk hA hr hδ hδ1 hscale hcentral
  have hA0 : 0 ≤ A := by linarith
  have hAsq : A ≤ A ^ 2 := by nlinarith
  have hDpos : 0 < D := (by positivity : 0 < 2 / N ^ 2).trans_le hD
  have hsroot : Real.sqrt (N * r ^ 2) = Real.sqrt N * r := by
    rw [Real.sqrt_mul hN.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
  have hell' : ‖ell‖ ≤ 2 * Kρ * A * δ := by
    rw [hsroot] at hell
    have hh := mul_le_mul_of_nonneg_left (add_le_add hroot hrad) hKρ
    nlinarith
  have hell'' : ‖ell‖ ≤ 2 * Kρ * A ^ 2 * δ * (1 + Z) := by
    calc
      _ ≤ 2 * Kρ * A * δ := hell'
      _ ≤ 2 * Kρ * A ^ 2 * δ := by gcongr
      _ ≤ 2 * Kρ * A ^ 2 * δ * (1 + Z) := by
        exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hdenom : 2 * k * R / D ≤ k * N ^ 2 * R := by
    calc
      _ ≤ 2 * k * R / (2 / N ^ 2) := by gcongr
      _ = _ := by field_simp
  have herror : k * N ^ 2 * R ≤
      Kp * (k * r ^ 3 / Real.sqrt N * Real.sqrt Z + k * r ^ 4 * Z + k * r ^ 4) := by
    calc
      _ ≤ k * N ^ 2 * (Kp / N *
        (r ^ 3 * Real.sqrt Z / Real.sqrt N / N + r ^ 4 * Z / N + r ^ 4 / N)) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ = _ := by field_simp
  have hterms : Kp * (k * r ^ 3 / Real.sqrt N * Real.sqrt Z + k * r ^ 4 * Z + k * r ^ 4) ≤
      Kp * (A ^ 2 * δ * Real.sqrt Z + A ^ 2 * δ * Z + A ^ 2 * δ) := by
    gcongr
  have hsZ : Real.sqrt Z ≤ 1 + Z := by nlinarith [Real.sq_sqrt hZ]
  have htail : Kp * (A ^ 2 * δ * Real.sqrt Z + A ^ 2 * δ * Z + A ^ 2 * δ) ≤
      2 * Kp * A ^ 2 * δ * (1 + Z) := by
    have hh := mul_le_mul_of_nonneg_left hsZ (by positivity : 0 ≤ Kp * A ^ 2 * δ)
    nlinarith
  have hrem := hdenom.trans (herror.trans (hterms.trans htail))
  nlinarith

end
end IsingBulk.AnisoF002.NegativeHT
