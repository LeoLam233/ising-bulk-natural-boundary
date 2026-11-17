import IsingBulk.AnisoF002.C03.PhysicalRegularChart

/-!
# Complete regular tails attached to the actual canonical spectral roots

The edge functions are identified on one open germ with the literal
canonical-root angular coefficients along the constructed spectral inverse.
The equality holds for every particle number simultaneously, hence for the
actual infinite tail and all its derivatives.  Identification of these
angular coefficients with the original double-contour/form-factor series
remains a separate physical correspondence obligation.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Filter Set MeasureTheory
open scoped Topology BigOperators

def canonicalAngularDensityF002 {N : ℕ} (lam : ℝ) (z : ℂ) (x : Fin N → ℝ) : ℂ :=
  fullRootNumeratorF002 lam z (Complex.sqrt (spectralRatioF002 lam z)) x *
    ((1 + ∏ i, spectralSmallRootF002 lam z (x i)) /
      (1 - ∏ i, spectralSmallRootF002 lam z (x i)))

def canonicalAngularCoefficientF002 (lam : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ *
    ∫ q, canonicalAngularDensityF002 lam z (flatConstrainedAngles q) ∂regularAngularProbability n

def canonicalAngularTailF002 (lam : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, canonicalAngularCoefficientF002 lam (m + 2 * n) z

theorem edgeFullDensity_eq_canonical {N : ℕ} {lam b : ℝ} {Z B : ℂ → ℂ} {t : ℂ}
    (hB : B t = spectralT lam (Z t) / spectralS (Z t))
    (hr : edgeAngleRoot (affineEdgeCenter b) B t = spectralSmallRootF002 lam (Z t))
    (x : Fin N → ℝ) :
    edgeFullDensity (affineEdgeCenter b) B t x = canonicalAngularDensityF002 lam (Z t) x := by
  rw [edgeFullDensity, edgeFullNumerator_eq_canonical hB hr, edgeSiteFactor_eq_product, hr]
  rfl

theorem edgeParticleCoefficient_eq_canonical {lam b : ℝ} {Z B : ℂ → ℂ} {t : ℂ}
    (hB : B t = spectralT lam (Z t) / spectralS (Z t))
    (hr : edgeAngleRoot (affineEdgeCenter b) B t = spectralSmallRootF002 lam (Z t)) (n : ℕ) :
    edgeParticleCoefficient (affineEdgeCenter b) B n t =
      canonicalAngularCoefficientF002 lam n (Z t) := by
  unfold edgeParticleCoefficient canonicalAngularCoefficientF002
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun q => edgeFullDensity_eq_canonical hB hr _)

theorem exists_canonical_regular_germs {lam b : ℝ} {Z B : ℂ → ℂ}
    (d : RegularEdgeCompleteControl b B)
    (hB : ∀ t, B t = spectralT lam (Z t) / spectralS (Z t))
    (hchart : ∀ᶠ t in 𝓝 0, spectralS (Z t) ≠ 0 ∧
      ∀ q : ℂ, (spectralA lam (Z t) - spectralT lam (Z t) * Complex.cos q) / spectralS (Z t) =
        affineEdgeCenter b t + B t * (1 - Complex.cos q)) :
    ∃ eps1 : ℝ, 0 < eps1 ∧ eps1 ≤ d.eps0 ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ eps1 →
        ∀ᶠ u in 𝓝 ((eps : ℂ) * Complex.I),
          (∀ n : ℕ, edgeParticleCoefficient (affineEdgeCenter b) B n u =
            canonicalAngularCoefficientF002 lam n (Z u)) ∧
          (∀ m : ℕ, edgeParticleTail (affineEdgeCenter b) B m u =
            canonicalAngularTailF002 lam m (Z u)) := by
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp hchart
  let eps1 := min d.eps0 (s / 2)
  have heps1 : 0 < eps1 := lt_min d.eps0_pos (half_pos hs)
  refine ⟨eps1, heps1, min_le_left _ _, ?_⟩
  intro eps he he1
  have he0 : eps ≤ d.eps0 := he1.trans (min_le_left _ _)
  have ht : (eps : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) s := by
    rw [Metric.mem_ball, dist_zero_right, inward_parameter_norm he.le]
    exact (he1.trans (min_le_right _ _)).trans_lt (half_lt_self hs)
  obtain ⟨r, eta, hr, heta, _, hprot⟩ := d.exists_inward_common_pole_disk he he0
  filter_upwards [Metric.isOpen_ball.mem_nhds ht,
    Metric.closedBall_mem_nhds ((eps : ℂ) * Complex.I) hr] with u hu hur
  have hc := hlocal (Metric.mem_ball.mp hu)
  have hp := hprot u hur
  have hphase (q : ℝ) : 0 < (edgeAnglePhase (affineEdgeCenter b) B u q).re := by
    have hh := (half_pos heta).trans_le (hp.2 1 (by norm_num) (fun _ => q))
    simpa [edgeTotalPhase] using hh
  have hroot := edgeAngleRoot_eq_canonical hc.1 hc.2 hphase
  have hcoef (n : ℕ) := edgeParticleCoefficient_eq_canonical (hB u) hroot n
  refine ⟨hcoef, ?_⟩
  intro m
  exact tsum_congr fun n => hcoef (m + 2 * n)

/-- The derivatives bounded here belong to the actual canonical-root
infinite tail evaluated along the actual physical spectral inverse. -/
theorem exists_positive_canonical_tail_control {lam b : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z) :
    ∃ (Z : ℂ → ℂ) (eps1 : ℝ), AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ 0 < eps1 ∧
      HasDerivAt Z (edgeDerivativeF002 lam 1 z)⁻¹ 0 ∧
      (∀ᶠ w in 𝓝 z, Z (positiveParameterF002 lam b w) = w) ∧
      ∀ n j : ℕ, 1 ≤ n → 2 * j ≤ n ^ 2 →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps1 →
          ‖iteratedDeriv j (fun u : ℂ => canonicalAngularTailF002 lam (n + 1) (Z u))
            ((eps : ℂ) * Complex.I)‖ ≤ M := by
  obtain ⟨Z, B, d, hZa, hZ0, hZd, _, _, hB, hchart, hleft⟩ :=
    exists_positive_physical_edge_control hlam hx hb hinc hdet
  obtain ⟨eps1, heps1, heps0, hgerm⟩ := exists_canonical_regular_germs d hB
    (hchart.mono fun _ h => h.2)
  refine ⟨Z, eps1, hZa, hZ0, heps1, hZd, hleft, ?_⟩
  intro n j hn hj
  obtain ⟨M, hM, hbound⟩ := d.selected_tail_derivative_uniform hn hj
  refine ⟨M, hM, ?_⟩
  intro eps he he1
  have heq : edgeParticleTail (affineEdgeCenter b) B (n + 1) =ᶠ[𝓝 ((eps : ℂ) * Complex.I)]
      fun u => canonicalAngularTailF002 lam (n + 1) (Z u) :=
    (hgerm eps he he1).mono fun _ h => h.2 (n + 1)
  rw [← heq.iteratedDeriv_eq j]
  exact hbound eps he (he1.trans heps0)

end
end IsingBulk.AnisoF002.RegularTail.C03
