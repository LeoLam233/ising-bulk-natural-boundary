import IsingBulk.AnisoF002.C03.NegativePhysicalBranch
import IsingBulk.AnisoF002.C03.RegularTailSum

/-!
# The regular positive-edge chart from the literal physical spectrum

The inverse parameter and coefficient are constructed from A,S,T.  The
complete edge control is then obtained by the proved regular mechanism.
The actual root is identified by the unsquared dispersion and its strict
decay on the physical side; no abstract analytic coefficient is supplied.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
  IsingBulk.AnisoF002.NegativeHT Filter Set
open scoped Topology BigOperators

def positiveParameterF002 (lam b : ℝ) (z : ℂ) : ℂ :=
  edgeCoordinateF002 lam 1 z - (b : ℂ)

theorem spectralRatioF002_im (lam : ℝ) (z : ℂ) :
    (spectralRatioF002 lam z).im = spectralDetF002 lam z / Complex.normSq (spectralS z) := by
  unfold spectralRatioF002 spectralDetF002
  rw [Complex.div_im]
  ring

theorem positiveParameterF002_center {lam b : ℝ} {z : ℂ}
    (hS : spectralS z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z) :
    positiveParameterF002 lam b z = 0 := by
  unfold positiveParameterF002
  rw [edgeCoordinate_eq_of_incidence hS (by simpa using hinc), sub_self]

theorem positive_dispersion_literal {lam b : ℝ} {z t q : ℂ}
    (hS : spectralS z ≠ 0) (ht : positiveParameterF002 lam b z = t) :
    (spectralA lam z - spectralT lam z * Complex.cos q) / spectralS z =
      affineEdgeCenter b t + spectralRatioF002 lam z * (1 - Complex.cos q) := by
  rw [← ht]
  unfold positiveParameterF002 edgeCoordinateF002 affineEdgeCenter spectralRatioF002
  push_cast
  field_simp
  ring

/-- The entire regular control is constructed at an actual positive
endpoint of the unsquared physical spectral equation. -/
theorem exists_positive_physical_edge_control {lam b : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z) :
    ∃ (Z B : ℂ → ℂ) (_d : RegularEdgeCompleteControl b B),
      AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧
      HasDerivAt Z (edgeDerivativeF002 lam 1 z)⁻¹ 0 ∧
      AnalyticAt ℂ B 0 ∧ B 0 = spectralT lam z / spectralS z ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ᶠ t in 𝓝 0, positiveParameterF002 lam b (Z t) = t ∧ spectralS (Z t) ≠ 0 ∧
        ∀ q : ℂ, (spectralA lam (Z t) - spectralT lam (Z t) * Complex.cos q) / spectralS (Z t) =
          affineEdgeCenter b t + B t * (1 - Complex.cos q)) ∧
      (∀ᶠ w in 𝓝 z, Z (positiveParameterF002 lam b w) = w) := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hpa : AnalyticAt ℂ (positiveParameterF002 lam b) z :=
    (analyticAt_edgeCoordinateF002 (e := 1) hS).sub analyticAt_const
  have hpd : HasDerivAt (positiveParameterF002 lam b) (edgeDerivativeF002 lam 1 z) z :=
    (edgeCoordinate_hasDerivAt (lam := lam) (Or.inl rfl) hS).sub_const _
  have hd0 : edgeDerivativeF002 lam 1 z ≠ 0 :=
    edgeDerivative_ne_zero_all_re hlam hx hb (Or.inl rfl) (by simpa using hinc)
  obtain ⟨Z, hZa, hZ0, hZd, hright, hleft⟩ := exists_local_analytic_inverse_zero
    hpa hpd hd0 (positiveParameterF002_center hS hinc)
  let B : ℂ → ℂ := fun t => spectralRatioF002 lam (Z t)
  have hBa : AnalyticAt ℂ B 0 := (analyticAt_spectralRatioF002 hS).comp_of_eq hZa hZ0
  have hB0 : B 0 = spectralT lam z / spectralS z := by simp only [B, hZ0, spectralRatioF002]
  have hBim : 0 < (B 0).im := by
    change 0 < (spectralRatioF002 lam (Z 0)).im
    rw [hZ0, spectralRatioF002_im]
    exact div_pos hdet (Complex.normSq_pos.mpr hS)
  obtain ⟨d⟩ := exists_regular_edge_complete_control hBa hb hBim
  refine ⟨Z, B, d, hZa, hZ0, hZd, hBa, hB0, fun _ => rfl, ?_, hleft⟩
  have hS' : ∀ᶠ t in 𝓝 0, spectralS (Z t) ≠ 0 :=
    ((analyticAt_spectralS_f002 z).comp_of_eq hZa hZ0).continuousAt.eventually_ne
      (by simpa only [Function.comp_def, hZ0] using hS)
  filter_upwards [hright, hS'] with t ht hs
  exact ⟨ht, hs, fun q => positive_dispersion_literal hs ht⟩

/-- Equality to the canonical physical root follows from the literal
dispersion and strict decay.  It applies simultaneously to all real angles. -/
theorem edgeAngleRoot_eq_canonical {lam b : ℝ} {Z B : ℂ → ℂ} {t : ℂ}
    (hS : spectralS (Z t) ≠ 0)
    (hdisp : ∀ q : ℂ,
      (spectralA lam (Z t) - spectralT lam (Z t) * Complex.cos q) / spectralS (Z t) =
        affineEdgeCenter b t + B t * (1 - Complex.cos q))
    (hphase : ∀ q : ℝ, 0 < (edgeAnglePhase (affineEdgeCenter b) B t q).re) :
    edgeAngleRoot (affineEdgeCenter b) B t = spectralSmallRootF002 lam (Z t) := by
  funext q
  rw [← edgeAnglePhase_exp_neg]
  apply phase_exp_eq_spectralSmallRoot hS
  · rw [edgeAnglePhase_cosh, Complex.ofReal_cos, hdisp]
  · exact hphase q

theorem edgeFullNumerator_eq_canonical {N : ℕ} {lam b : ℝ} {Z B : ℂ → ℂ} {t : ℂ}
    (hB : B t = spectralT lam (Z t) / spectralS (Z t))
    (hr : edgeAngleRoot (affineEdgeCenter b) B t = spectralSmallRootF002 lam (Z t))
    (x : Fin N → ℝ) :
    edgeFullNumerator (affineEdgeCenter b) B t x =
      fullRootNumeratorF002 lam (Z t) (Complex.sqrt (spectralRatioF002 lam (Z t))) x := by
  unfold edgeFullNumerator edgePrefactor
  rw [hr, hB]
  rfl

end
end IsingBulk.AnisoF002.RegularTail.C03
