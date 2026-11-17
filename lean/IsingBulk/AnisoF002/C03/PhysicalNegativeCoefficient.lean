import IsingBulk.AnisoF002.C03.NegativePhysicalCoefficient
import IsingBulk.AnisoF002.C03.NegativePhysicalNumerator
import IsingBulk.AnisoF002.C03.NegativeInwardDisk
import IsingBulk.AnisoF002.C03.NegativeModelBranchSign
import IsingBulk.AnisoF002.C03.PhysicalSeriesAttachment

/-!
# Exact attachment of every complete negative physical coefficient

The negative independent angles are literally the physical constrained
angles minus pi.  This identifies the entire real cycle, with its original
factorial and Lebesgue normalization, with the canonical physical
coefficient.  A prescribed analytic physical square root is retained:
its ratio to the principal square root is one common sign, before the
particle number is selected.  One common open inward germ identifies all
coefficients and therefore the complete odd series.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
  IsingBulk.AnisoF002.NegativeHT
open scoped Topology BigOperators

theorem negativePhysicalCoefficient_root_scale {b b' B : ℂ → ℂ} (φ : ℝ)
    (n : ℕ) (t σ : ℂ) (hb : b' t = σ * b t) :
    negativePhysicalCoefficient b' B φ n t =
      σ ^ ((n + 1) ^ 2) * negativePhysicalCoefficient b B φ n t := by
  unfold negativePhysicalCoefficient
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    unfold completeNegativeNumerator
    rw [hb, mul_pow]
    ring

theorem negativePhysicalCoefficient_principal_eq_canonical {lam φ : ℝ}
    {B : ℂ → ℂ} {t z : ℂ}
    (hB : B t = spectralT lam z / spectralS z)
    (hroot : ∀ q : ℝ,
      Complex.exp (-negativeGlobalPhase B φ (t, ((q - Real.pi : ℝ) : ℂ))) =
        spectralSmallRootF002 lam z q) (n : ℕ) :
    negativePhysicalCoefficient (fun u => Complex.sqrt (B u)) B φ n t =
      canonicalAngularCoefficientF002 lam n z := by
  have hangle (q : Fin n → ℝ) :
      (fun i => Real.pi + 0 + negativeConstrainedAngles q i) = flatConstrainedAngles q := by
    funext i
    simp only [negativeConstrainedAngles, add_zero]
    ring
  have hnum (q : Fin n → ℝ) := completeNegativeNumerator_canonical lam z t
    (fun u => Complex.sqrt (B u)) (negativeGlobalPhase B φ) 0
    (negativeConstrainedAngles q) (fun i => by
      rw [show Real.pi + 0 + negativeConstrainedAngles q i = flatConstrainedAngles q i by
        dsimp only [negativeConstrainedAngles]
        ring]
      simpa only [Complex.ofReal_zero, zero_add, negativeConstrainedAngles] using
        (hroot (flatConstrainedAngles q i)).symm)
    ((edgePrefactor_sq B t).trans hB)
  have hnum' (q : Fin n → ℝ) :
      completeNegativeNumerator (n + 1) (fun u => Complex.sqrt (B u))
        (negativeGlobalPhase B φ) 0 t (fun i => (negativeConstrainedAngles q i : ℂ)) =
      (windingNormalization (n + 1))⁻¹ *
        fullRootNumeratorF002 lam z (Complex.sqrt (spectralRatioF002 lam z))
          (flatConstrainedAngles q) := by
    have hh := hnum q
    simp only [Complex.ofReal_zero] at hh
    rw [← hh, hangle q, hB]
    simp only [spectralRatioF002, div_eq_mul_inv, mul_comm]
  have hsite (q : Fin n → ℝ) :
      edgeSiteFactor (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t
        (negativeConstrainedAngles q) =
      (1 + ∏ i, spectralSmallRootF002 lam z (flatConstrainedAngles q i)) /
        (1 - ∏ i, spectralSmallRootF002 lam z (flatConstrainedAngles q i)) := by
    rw [edgeSiteFactor_eq_product]
    have he (i : Fin (n + 1)) :
        edgeAngleRoot (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t
          (negativeConstrainedAngles q i) =
        spectralSmallRootF002 lam z (flatConstrainedAngles q i) := by
      rw [← edgeAnglePhase_exp_neg, ← negativeGlobalPhase_real]
      exact hroot _
    simp_rw [he]
  unfold negativePhysicalCoefficient canonicalAngularCoefficientF002
  simp_rw [hnum', hsite, mul_assoc]
  unfold canonicalAngularDensityF002
  rw [integral_const_mul, regularAngularProbability_integral]
  simp only [Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat, windingNormalization, Nat.add_sub_cancel,
    mul_inv_rev]
  ring

theorem physical_unit_odd_square_power {σ : ℂ} (hσ : σ ^ 2 = 1) {N : ℕ}
    (hN : Odd N) : σ ^ (N ^ 2) = σ := by
  obtain ⟨k, rfl⟩ := hN
  have he : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
  rw [he, pow_add, pow_mul, hσ, one_pow, one_mul, pow_one]

theorem negativePhysicalCoefficient_branch_eq_canonical {lam φ : ℝ}
    {b B : ℂ → ℂ} {t z : ℂ}
    (hB : B t = spectralT lam z / spectralS z) (hBn : B t ≠ 0)
    (hbsq : b t ^ 2 = B t)
    (hroot : ∀ q : ℝ,
      Complex.exp (-negativeGlobalPhase B φ (t, ((q - Real.pi : ℝ) : ℂ))) =
        spectralSmallRootF002 lam z q) (n : ℕ) (hn : Odd (n + 1)) :
    canonicalAngularCoefficientF002 lam n z =
      (Complex.sqrt (B t) / b t) * negativePhysicalCoefficient b B φ n t := by
  have hbn : b t ≠ 0 := by
    intro hb
    rw [hb, zero_pow two_ne_zero] at hbsq
    exact hBn hbsq.symm
  rw [← negativePhysicalCoefficient_principal_eq_canonical hB hroot n,
    negativePhysicalCoefficient_root_scale (b := b) (b' := fun u => Complex.sqrt (B u))
      (B := B) φ n t (Complex.sqrt (B t) / b t) (div_mul_cancel₀ _ hbn).symm,
    physical_unit_odd_square_power (physical_root_branch_sign_sq hBn hbsq) hn]

theorem exists_negative_canonical_root_germs {lam φ : ℝ} {Z B : ℂ → ℂ}
    (d : NegativeCoefficientControl B φ)
    (hchart : ∀ᶠ t in 𝓝 (0 : ℂ), spectralS (Z t) ≠ 0 ∧
      ∀ δ : ℂ, (spectralA lam (Z t) - spectralT lam (Z t) *
        Complex.cos ((Real.pi : ℂ) + δ)) / spectralS (Z t) =
        (Real.cos φ : ℂ) + B t * (t - 1 + Complex.cos δ)) :
    ∃ eps1 : ℝ, 0 < eps1 ∧ eps1 ≤ d.eps0 ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ eps1 →
        ∀ᶠ u in 𝓝 (-(eps : ℂ)), ∀ q : ℝ,
          Complex.exp (-negativeGlobalPhase B φ (u, ((q - Real.pi : ℝ) : ℂ))) =
            spectralSmallRootF002 lam (Z u) q := by
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp hchart
  let eps1 := min d.eps0 (s / 2)
  have heps1 : 0 < eps1 := lt_min d.eps0_pos (half_pos hs)
  refine ⟨eps1, heps1, min_le_left _ _, ?_⟩
  intro eps he he1
  have he0 : eps ≤ d.eps0 := he1.trans (min_le_left _ _)
  have ht : -(eps : ℂ) ∈ Metric.ball (0 : ℂ) s := by
    rw [Metric.mem_ball, dist_zero_right, norm_neg, Complex.norm_real, Real.norm_of_nonneg he.le]
    exact (he1.trans (min_le_right _ _)).trans_lt (half_lt_self hs)
  obtain ⟨r, eta, hr, heta, _, hprot⟩ := d.exists_inward_common_disk he he0
  filter_upwards [Metric.isOpen_ball.mem_nhds ht,
    Metric.closedBall_mem_nhds (-(eps : ℂ)) hr] with u hu hur
  have hc := hlocal (Metric.mem_ball.mp hu)
  intro q
  have hphase : 0 < (negativeGlobalPhase B φ (u, ((q - Real.pi : ℝ) : ℂ))).re := by
    have hh := (half_pos heta).trans_le ((hprot u hur).2.2 1 (by norm_num) (fun _ => q - Real.pi))
    rw [negativeGlobalPhase_real]
    simpa only [edgeTotalPhase, Fin.sum_univ_one] using hh
  apply phase_exp_eq_spectralSmallRoot hc.1 ?_ hphase
  have hspec := hc.2 (((q - Real.pi : ℝ) : ℂ))
  have hangle : (Real.pi : ℂ) + ((q - Real.pi : ℝ) : ℂ) = (q : ℂ) := by
    push_cast
    ring
  rw [hangle, ← Complex.ofReal_cos] at hspec
  rw [negativeGlobalPhase_cosh]
  calc
    localNegativeDispersion B φ (u, ((q - Real.pi : ℝ) : ℂ)) =
        (Real.cos φ : ℂ) + B u * (u - 1 + Complex.cos ((q - Real.pi : ℝ) : ℂ)) := by
      unfold localNegativeDispersion
      ring
    _ = _ := hspec.symm

theorem exists_negative_physical_coefficient_germs {lam φ : ℝ} {Z b B : ℂ → ℂ}
    (d : NegativeCoefficientControl B φ)
    (hBa : AnalyticAt ℂ B 0) (hba : AnalyticAt ℂ b 0) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hB : ∀ t, B t = spectralT lam (Z t) / spectralS (Z t))
    (hchart : ∀ᶠ t in 𝓝 (0 : ℂ), spectralS (Z t) ≠ 0 ∧
      ∀ δ : ℂ, (spectralA lam (Z t) - spectralT lam (Z t) *
        Complex.cos ((Real.pi : ℂ) + δ)) / spectralS (Z t) =
        (Real.cos φ : ℂ) + B t * (t - 1 + Complex.cos δ)) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ u in 𝓝 (-(eps : ℂ)),
        (∀ n : ℕ, Odd (n + 1) → canonicalAngularCoefficientF002 lam n (Z u) =
          (Complex.sqrt (B 0) / b 0) * negativePhysicalCoefficient b B φ n u) ∧
        canonicalAngularTailF002 lam 0 (Z u) =
          (Complex.sqrt (B 0) / b 0) * ∑' n : ℕ, negativePhysicalCoefficient b B φ (2 * n) u := by
  obtain ⟨eps1, heps1, _, hroot⟩ := exists_negative_canonical_root_germs d hchart
  obtain ⟨r, hr, hsign⟩ := exists_common_physical_root_sign hBa hba (Or.inr hBi.ne) hbsq
  have hBn : B 0 ≠ 0 := Complex.slitPlane_ne_zero (Or.inr hBi.ne)
  have hlocal : ∀ᶠ u in 𝓝 (0 : ℂ), B u ≠ 0 ∧
      Complex.sqrt (B u) / b u = Complex.sqrt (B 0) / b 0 := by
    filter_upwards [hBa.continuousAt.eventually_ne hBn, Metric.ball_mem_nhds (0 : ℂ) hr] with u hu hur
    exact ⟨hu, hsign u hur⟩
  obtain ⟨s, hs, hlocal'⟩ := Metric.eventually_nhds_iff.mp hlocal
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds heps1).filter_mono nhdsWithin_le_nhds,
    (gt_mem_nhds hs).filter_mono nhdsWithin_le_nhds] with eps he he1 hes
  have ht : -(eps : ℂ) ∈ Metric.ball (0 : ℂ) s := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg he.le] using hes
  filter_upwards [hroot eps he he1.le, Metric.isOpen_ball.mem_nhds ht] with u hur hu
  have hl := hlocal' (Metric.mem_ball.mp hu)
  have hcoef (n : ℕ) (hn : Odd (n + 1)) : canonicalAngularCoefficientF002 lam n (Z u) =
      (Complex.sqrt (B 0) / b 0) * negativePhysicalCoefficient b B φ n u := by
    rw [negativePhysicalCoefficient_branch_eq_canonical (hB u) hl.1 (hbsq u) hur n hn, hl.2]
  refine ⟨hcoef, ?_⟩
  unfold canonicalAngularTailF002
  simp only [zero_add]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => hcoef (2 * n) ⟨n, rfl⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
