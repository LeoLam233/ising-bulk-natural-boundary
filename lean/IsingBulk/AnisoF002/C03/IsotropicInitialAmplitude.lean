import IsingBulk.AnisoF002.C03.IsotropicIteratedCurrent

/-!
# The complete normalized physical amplitude enters the recurrence

The initial amplitude includes every one-body factor and every canceled
physical pair, with the frozen factorial and angular normalization.
Smooth real weights are allowed without continuing them analytically.
The density identity is an equality of scalar coefficients on the
original angular variables.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff
open Set Metric
open IsingBulk.AnisoF002.RegularTail

def isotropicParticleNormalization (N : ℕ) : ℂ :=
  ((N.factorial : ℂ) * (2 * (Real.pi : ℂ)) ^ (N - 1))⁻¹

def actualRegularNumerator {N : ℕ} (η τ ξ : ℝ) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  completeRegularNumerator N (q.1, fun i => actualPhysicalCoordinate η τ ξ i q)

def actualInitialAmplitude {N : ℕ} (η τ ξ : ℝ)
    (cutoff : (ℂ × (Fin N → ℝ)) → ℂ) (q : ℂ × (Fin N → ℝ)) : ℂ :=
  isotropicParticleNormalization N * cutoff q * actualRegularNumerator η τ ξ q

/-- The initial regular scalar density is exactly the complete physical
deformed density, including all pair factors and its original normalization. -/
theorem actualInitialAmplitude_physical_density {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (cutoff : (ℂ × (Fin N → ℝ)) → ℂ) (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hU : ∀ i, explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i)
    (hD : ∀ i, Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0) :
    actualCoordinateDeterminant η τ ξ q *
        (actualSignedProductKernel σ η τ ξ q * actualInitialAmplitude η τ ξ cutoff q) =
      isotropicParticleNormalization N * cutoff q *
        (actualBalancedJacobian η τ ξ q.2).det *
        ((1 + σ * ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i)) /
          (1 - σ * ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i))) *
        (∏ i, (Complex.sinh (Complex.I * actualPhysicalPhase η τ ξ q i))⁻¹) *
        ∏ ij ∈ indexPairs N,
          canceledPair 1
            (isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 ij.1))
            (isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 ij.2))
            (Complex.exp (actualHomotopyAngle η τ ξ q.2 ij.1 * Complex.I))
            (Complex.exp (actualHomotopyAngle η τ ξ q.2 ij.2 * Complex.I)) := by
  have hd := actual_complete_scalar_density η τ ξ q hq hU hD
  rw [actualSignedProductKernel_eq_physical σ η τ ξ q]
  unfold actualInitialAmplitude actualRegularNumerator
  calc
    _ = isotropicParticleNormalization N * cutoff q *
        ((1 + σ * ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i)) /
          (1 - σ * ∏ i, isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i))) *
        (actualCoordinateDeterminant η τ ξ q *
          completeRegularNumerator N (q.1, fun i => actualPhysicalCoordinate η τ ξ i q)) := by ring
    _ = _ := by rw [hd]; ring

theorem retainedRegularNumerator_empty (N : ℕ) :
    retainedRegularNumerator (∅ : Finset (Fin N × Fin N)) = completeRegularNumerator N := by
  funext q
  simp [retainedRegularNumerator, retainedInversePairProduct, completeRegularNumerator,
    completeInversePairProduct]

/-- On the entire actual one-sided image the full normalized amplitude
is smooth, including every partial and total coincidence. -/
theorem exists_actual_initialAmplitude_smooth (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ (η τ ξ : ℝ), 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-Real.pi - δ) δ) →
      ∀ cutoff : (ℂ × (Fin N → ℝ)) → ℂ, ContDiffAt ℝ ∞ cutoff (s, θ) →
        ContDiffAt ℝ ∞ (actualInitialAmplitude η τ ξ cutoff) (s, θ) := by
  obtain ⟨r, _, _, _, hr, _, _, _, hnum⟩ :=
    exists_actual_oneSided_retainedNumerator_analytic_gaussian S hS
  obtain ⟨δ, hδ, himage⟩ := exists_actual_oneSided_homotopy_domain S r hS hr
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear η τ ξ hη hτ hξ θ hθ cutoff hc
  have hq := (himage N hN s hs hsnear η τ ξ hη hτ hξ θ hθ).1
  have ha := (hnum N ∅ (Finset.empty_subset _) _ hq).1
  rw [retainedRegularNumerator_empty] at ha
  have hχ (i : Fin N) : ContDiffAt ℝ ∞ (actualPhysicalCoordinate η τ ξ i) (s, θ) :=
    actualPhysicalCoordinate_contDiffAt η τ ξ i (s, θ) ⊤
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i)
  have hmap : ContDiffAt ℝ ∞
      (fun q : ℂ × (Fin N → ℝ) => (q.1, fun i => actualPhysicalCoordinate η τ ξ i q)) (s, θ) :=
    contDiffAt_fst.prodMk (contDiffAt_pi.mpr hχ)
  have hn : ContDiffAt ℝ ∞ (actualRegularNumerator η τ ξ) (s, θ) :=
    ha.restrictScalars.contDiffAt.comp (s, θ) hmap
  exact (contDiffAt_const.mul hc).mul hn

/-- Every derivative step of the actual full normalized right density
uses the same physical kernel and the complete descendant amplitude. -/
theorem exists_actual_complete_density_current (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ k, θ k ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ∀ i j, θ i ≠ θ j → ∀ anchor : Fin N,
        ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ∀ cutoff : (ℂ × (Fin N → ℝ)) → ℂ, ContDiffAt ℝ ∞ cutoff (s, θ) → ∀ n : ℕ,
        let b := actualTransportDescendant η τ ξ (actualInitialAmplitude η τ ξ cutoff)
        ContDiffAt ℝ ∞ (b n) (s, θ) ∧
          scalarPartial (fun y => actualCoordinateDeterminant η τ ξ y *
              (actualSignedProductKernel σ η τ ξ y * b n y)) actualTimeDirection (s, θ) -
            (∑ k ∈ Finset.univ.erase anchor,
              scalarPartial (fun y => actualCovarianceAngularVelocity η τ ξ k y *
                actualCoordinateDeterminant η τ ξ y * (actualSignedProductKernel σ η τ ξ y * b n y))
                (actualAngularDirection k - actualAngularDirection anchor) (s, θ)) =
          actualCoordinateDeterminant η τ ξ (s, θ) * actualSignedProductKernel σ η τ ξ (s, θ) *
            b (n + 1) (s, θ) := by
  obtain ⟨r₁, hr₁, hnum⟩ := exists_actual_initialAmplitude_smooth S hS
  obtain ⟨r₂, hr₂, hcurrent⟩ := exists_actual_iterated_constrained_current S η hS hη
  let δ := min r₁ r₂
  have hδ : 0 < δ := lt_min hr₁ hr₂
  have hd1 : δ ≤ r₁ := min_le_left _ _
  have hd2 : δ ≤ r₂ := min_le_right _ _
  have hb := (rightBranchEndpoint_lt_pi S hS.1).le
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ i j hij anchor σ hσ cutoff hc n
  have hθ1 : ∀ k, θ k ∈ Icc (-Real.pi - r₁) r₁ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd1⟩
  have hθ2 : ∀ k, θ k ∈ Icc (-rightBranchEndpoint S - r₂) r₂ :=
    fun k => ⟨by linarith [(hθ k).1], (hθ k).2.trans hd2⟩
  have hn := hnum N hN s hs (hsnear.trans_le hd1) η τ ξ hη
    ⟨hτ.1, hτ.2.trans hd1⟩ hξ θ hθ1 cutoff hc
  exact hcurrent N hN s hs (hsnear.trans_le hd2) τ ⟨hτ.1, hτ.2.trans hd2⟩ ξ hξ θ
    hθ2 i j hij anchor σ hσ (actualInitialAmplitude η τ ξ cutoff) hn n

end IsingBulk.AnisoF002.Isotropic
