import IsingBulk.Joint.Negative.CurveCoordinates
import IsingBulk.Anisotropic.NegativeNormalForm.UniformCanonicalNormalForm
import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy
import IsingBulk.Anisotropic.NegativeNormalForm.ActualCentralFixedCutoff

/-! The dimension-uniform normal form for the *actual independent-coupling
curve*, including its exact spectral pole equation. The existing arbitrary-B
construction is reused, and the additional joint-coordinate bridge is proved
here. Nothing is inferred from an ambient nonextension theorem. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
open IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.NegativeCycles

/-- The actual spectral phase sum on an independent-coupling curve. -/
def actualPoleEquation {n : ℕ} (curve : ℂ → Coupling) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) : ℂ :=
  ∑ i, (edgePhase phi hphi (transferC (curve t) +
    transferB (curve t) * Complex.cos (d + v i)) - (phi : ℂ) * Complex.I)

theorem actualPoleEquation_eq {n : ℕ} (curve : ℂ → Coupling) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n)
    (hB : transferB (curve t) ≠ 0)
    (ht : edgeParameter (Real.cos phi : ℂ) (curve t) = t) :
    actualPoleEquation curve phi hphi d t v =
      poleEquation (curveB curve) phi hphi d t v := by
  unfold actualPoleEquation poleEquation negativePhase
  apply Finset.sum_congr rfl
  intro i _
  rw [curve_dispersion_identity (Real.cos phi) curve t (d + v i) hB ht]

/-- Averaging the complex bilinear quadratic form gives a dimension-free
bound in the supremum norm. No division by the quadratic form is used. -/
theorem norm_quadratic_div_two_dimension {n : ℕ} (hn : n ≠ 0) (v : Config n) :
    ‖quadratic v / (2 * (n : ℂ))‖ ≤ ‖v‖ ^ 2 / 2 := by
  have hsum : absoluteEnergy v ≤ (n : ℝ) * ‖v‖ ^ 2 := by
    calc
      absoluteEnergy v ≤ ∑ i : Fin n, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = _ := by simp
  rw [norm_div, norm_mul, Complex.norm_natCast]
  norm_num only [Complex.norm_ofNat]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  calc
    ‖quadratic v‖ / (2 * (n : ℝ)) ≤ ((n : ℝ) * ‖v‖ ^ 2) / (2 * (n : ℝ)) :=
      div_le_div_of_nonneg_right ((norm_quadratic_le v).trans hsum) (by positivity)
    _ = ‖v‖ ^ 2 / 2 := by field_simp

/-- For every analytic normalized negative transversal, one common ball works
for all particle dimensions and all small winding centers. The pole is the
actual independent-coupling phase sum, not only the abstract quadratic model.
The constraint and every coincidence divisor are preserved. -/
theorem curve_dimension_uniform_actual_normal_form
    (curve : ℂ → Coupling) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (hc : AnalyticAt ℂ curve 0) (hS : S (curve 0) ≠ 0)
    (hBi : (transferB (curve 0)).im < 0)
    (hcoord : ∀ᶠ t in 𝓝 (0 : ℂ), edgeParameter (Real.cos phi : ℂ) (curve t) = t) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, n ≠ 0 → ∀ d : ℂ, ‖d‖ < delta →
      ∃ pole : Config n → ℂ, ∃ Psi : Config n → Config n,
        AnalyticOnNhd ℂ pole (ball 0 delta) ∧ pole 0 = 1 - Complex.cos d ∧
        AnalyticOnNhd ℂ Psi (ball 0 delta) ∧ Psi 0 = 0 ∧
        HasFDerivAt Psi
          (scalarConfiguration (Complex.sqrt (centralHessian (curveB curve) phi d))⁻¹) 0 ∧
        (∀ e y, Psi (permute e y) = permute e (Psi y)) ∧
        (∀ y i k, y i = y k → Psi y i = Psi y k) ∧
        (∀ y, ‖y‖ ≤ delta → ‖Psi y - y‖ ≤ (1/8) * ‖y‖ ∧
          (ZeroMean y → ZeroMean (Psi y) ∧
            actualPoleEquation curve phi hphi d (pole (Psi y)) (Psi y) = 0 ∧
            pole (Psi y) = 1 - Complex.cos d + quadratic y / (2 * n))) := by
  have hBa := curveB_analyticAt hc hS
  have hB0 : curveB curve 0 ≠ 0 := transferB_ne_zero_of_im_neg hBi
  obtain ⟨delta0, hd0, hnormal⟩ :=
    exists_dimension_uniform_canonical_normal_form (curveB curve) phi hphi hBa hB0
  have hnear := hcoord.and (hBa.continuousAt.eventually_ne hB0)
  obtain ⟨rho, hrho, hchart⟩ := Metric.mem_nhds_iff.mp hnear
  have htau : ∀ᶠ d : ℂ in 𝓝 0, ‖1 - Complex.cos d‖ < rho / 2 := by
    have hh : ContinuousAt (fun d : ℂ => ‖1 - Complex.cos d‖) 0 := by fun_prop
    exact hh.eventually_lt continuousAt_const (by simpa using half_pos hrho)
  obtain ⟨eta, heta, htau⟩ := Metric.mem_nhds_iff.mp htau
  let delta := min delta0 (min eta (min 1 (rho / 2))) / 2
  have hd : 0 < delta := div_pos (lt_min hd0 (lt_min heta (lt_min (by norm_num) (half_pos hrho)))) (by norm_num)
  have hd0' : delta ≤ delta0 := by dsimp [delta]; linarith [min_le_left delta0 (min eta (min 1 (rho/2)))]
  have hde : delta ≤ eta := by
    have hh := (min_le_right delta0 _).trans (min_le_left eta (min 1 (rho/2)))
    dsimp [delta]; linarith
  have hd1 : delta ≤ 1 := by
    have hh := (min_le_right delta0 _).trans ((min_le_right eta _).trans (min_le_left 1 (rho/2)))
    dsimp [delta]; linarith
  have hdr : delta ≤ rho / 2 := by
    have hh := (min_le_right delta0 _).trans ((min_le_right eta _).trans (min_le_right 1 (rho/2)))
    dsimp [delta]; linarith
  refine ⟨delta, hd, ?_⟩
  intro n hn d hdn
  obtain ⟨pole, Psi, hp, hp0, hPsi, hPsi0, hder, hperm, _hlip, _hderbound, hfull⟩ :=
    hnormal n hn d (hdn.trans_le hd0')
  refine ⟨pole, Psi, hp.mono (ball_subset_ball hd0'), hp0,
    hPsi.mono (ball_subset_ball hd0'), hPsi0, hder, hperm,
    (fun y i k hy => equivariant_coincidence Psi hperm y i k hy), ?_⟩
  intro y hy
  obtain ⟨hclose, hzero⟩ := hfull y (hy.trans hd0')
  refine ⟨hclose, ?_⟩
  intro hm
  obtain ⟨hmean, hpole, heq⟩ := hzero hm
  refine ⟨hmean, ?_, heq⟩
  have hsmall : ‖pole (Psi y)‖ < rho := by
    rw [heq]
    have ht : ‖1 - Complex.cos d‖ < rho/2 := htau (by simpa using hdn.trans_le hde)
    have hq := norm_quadratic_div_two_dimension hn y
    have hsq : ‖y‖ ^ 2 ≤ delta := by nlinarith [norm_nonneg y]
    have hadd := norm_add_le (1 - Complex.cos d) (quadratic y / (2 * n))
    nlinarith
  obtain ⟨hc', hb'⟩ := hchart (by simpa using hsmall)
  rw [actualPoleEquation_eq curve phi hphi d (pole (Psi y)) (Psi y) hb' hc']
  exact hpole

end
end IsingBulk.Joint.Negative
