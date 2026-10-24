import IsingBulk.Anisotropic.FormFactors.ParticleLatticeExchange

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section

 theorem even_positive_envelope_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun n => hadamardEnvelope C (2*n+2)) := by
  have hh := (hadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective
  change Summable (fun n => hadamardEnvelope C (2*(n+1))) at hh
  simpa only [mul_add,mul_one] using hh

theorem physical_spectralProduct (lam x : ℝ) : spectralProduct lam (x:ℂ) = (realProduct lam x:ℂ) := by
  simp only [spectralProduct,spectralS,spectralT,realProduct,Complex.ofReal_mul,Complex.ofReal_sinh]

theorem physical_root_odd_power {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (n : ℕ) :
    (Real.sqrt (realProduct lam x))^(2*n+1) = Real.sqrt (realProduct lam x)*(realProduct lam x)^n := by
  have hp : 0 ≤ realProduct lam x :=
    (mul_pos (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))).le
  rw [pow_succ,pow_mul,Real.sq_sqrt hp,mul_comm]

theorem physical_root_even_power {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (n : ℕ) :
    (Real.sqrt (realProduct lam x))^(2*n+2) = (realProduct lam x)^(n+1) := by
  have hp : 0 ≤ realProduct lam x :=
    (mul_pos (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))).le
  rw [show 2*n+2=2*(n+1) by omega,pow_mul,Real.sq_sqrt hp]

theorem oddSiteSeries_summable_and_sum {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) :
    Summable (oddSiteSeries lam x) ∧
    (∑' v, oddSiteSeries lam x v) = (Real.sqrt (realProduct lam x):ℂ)*
      ∑' n, (spectralProduct lam (x:ℂ))^n*unscaledFullCoefficient (2*n+1) lam (x:ℂ) := by
  have habs := selected_particle_lattice_norm_summable hlam hx hp (fun n => 2*n+1)
    (fun _ => by omega) (fun _ hC => hadamardEnvelope_odd_summable hC)
  constructor
  · exact habs.of_norm.prod_symm.prod
  · simp only [oddSiteSeries]
    rw [selected_particle_lattice_exchange hlam hx hp (fun n => 2*n+1)
      (fun _ => by omega) (fun _ hC => hadamardEnvelope_odd_summable hC)]
    simp_rw [physical_root_odd_power hlam hx,Complex.ofReal_mul,Complex.ofReal_pow,
      mul_assoc,← physical_spectralProduct]
    rw [tsum_mul_left]

theorem evenSiteSeries_summable_and_sum {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) :
    Summable (evenSiteSeries lam x) ∧
    (∑' v, evenSiteSeries lam x v) =
      ∑' n, (spectralProduct lam (x:ℂ))^(n+1)*unscaledFullCoefficient (2*n+2) lam (x:ℂ) := by
  have habs := selected_particle_lattice_norm_summable hlam hx hp (fun n => 2*n+2)
    (fun _ => by omega) (fun _ hC => even_positive_envelope_summable hC)
  constructor
  · exact habs.of_norm.prod_symm.prod
  · simp only [evenSiteSeries]
    rw [selected_particle_lattice_exchange hlam hx hp (fun n => 2*n+2)
      (fun _ => by omega) (fun _ hC => even_positive_envelope_summable hC)]
    simp_rw [physical_root_even_power hlam hx,Complex.ofReal_pow,← physical_spectralProduct]

/-- Physical HT covariance identification, with the published real-only
spin representation as its sole physical premise. All exchanges are proved. -/
theorem high_covariance_sum {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x < 1) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    Summable (corrH x) ∧ (highCovarianceSum corrH x:ℂ) =
      ((1-realProduct lam x^2)^(1/4:ℝ):ℝ)*
        ∑' n, (spectralProduct lam (x:ℂ))^n*unscaledFullCoefficient (2*n+1) lam (x:ℂ) := by
  obtain ⟨hs,he⟩ := oddSiteSeries_summable_and_sum hlam hx hp.ne
  have hc : Summable (fun v => (corrH x v:ℂ)) := by
    simpa only [hphys.high_spin x hx hp] using hs.mul_left (realHighPrefactor lam x:ℂ)
  refine ⟨Complex.summable_ofReal.mp hc,?_⟩
  unfold highCovarianceSum
  rw [Complex.ofReal_tsum]
  simp_rw [hphys.high_spin x hx hp]
  rw [tsum_mul_left,he]
  have hsqrt : Real.sqrt (realProduct lam x) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx)))).ne'
  unfold realHighPrefactor
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hsqrt]

theorem low_covariance_sum {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : 1 < realProduct lam x) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    Summable (fun v => corrL x v-realMagnetizationSq lam x) ∧
      (lowCovarianceSum lam corrL x:ℂ) = (realMagnetizationSq lam x:ℂ)*
        ∑' n, (spectralProduct lam (x:ℂ))^(n+1)*unscaledFullCoefficient (2*n+2) lam (x:ℂ) := by
  obtain ⟨hs,he⟩ := evenSiteSeries_summable_and_sum hlam hx hp.ne'
  have hc : Summable (fun v => ((corrL x v-realMagnetizationSq lam x:ℝ):ℂ)) := by
    simpa only [low_connected_spin hphys hx hp] using hs.mul_left (realMagnetizationSq lam x:ℂ)
  refine ⟨Complex.summable_ofReal.mp hc,?_⟩
  unfold lowCovarianceSum
  rw [Complex.ofReal_tsum (f := fun v : LatticeSite => corrL x v-realMagnetizationSq lam x)]
  simp_rw [low_connected_spin hphys hx hp]
  rw [tsum_mul_left,he]
end
end IsingBulk.Anisotropic.FormFactors
