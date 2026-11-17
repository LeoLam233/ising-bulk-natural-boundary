import IsingBulk.AnisoF002.C03.NegativeAllWindingResidueBounds
import IsingBulk.AnisoF002.C03.NegativeRealQuadraticPeriod
import IsingBulk.AnisoF002.C03.RegularWindingPhysicalSectors

/-!
# Constructed quantitative control of the literal physical winding sectors

The original complete numerator, phase derivative, moving pole, cutoff,
and independent measure are preserved.  One control is constructed from
the physical analytic data before any population, winding, or order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology BigOperators Classical

def windingMass (n : ℕ) (w : ℤ) : ℝ := (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ)

theorem windingMass_pos (n : ℕ) {w : ℤ} (hw : w ≠ 0) : 0 < windingMass n w := by
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw
  exact div_pos (mul_pos (sq_pos_of_ne_zero hwR) (sq_pos_of_pos Real.pi_pos)) (by positivity)

theorem allWindingCenterMagnitude_nonneg (n : ℕ) (b0 : ℂ) {φ : ℝ}
    (hφ : 0 < φ) (hπ : φ < Real.pi) : 0 ≤ allWindingCenterMagnitude n b0 φ := by
  unfold allWindingCenterMagnitude
  exact div_nonneg (pow_nonneg (norm_nonneg _) _)
    (mul_nonneg (by positivity) (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi hφ hπ).le _))

structure PhysicalWindingResidueControl (b B : ℂ → ℂ) (φ : ℝ) where
  radius : ℝ
  cutoff : ℝ
  A : ℝ
  K : ℝ
  C : ℝ
  radius_pos : 0 < radius
  cutoff_pos : 0 < cutoff
  A_pos : 0 < A
  K_pos : 0 < K
  C_pos : 0 < C
  cutoff_le_one : cutoff ≤ 1
  cutoff_lt_pi_sq : cutoff < Real.pi ^ 2
  K_cutoff : K * cutoff ≤ 1 / 4
  center_nonneg : ∀ n, 0 ≤ allWindingCenterMagnitude n (b 0) φ
  measurable : ∀ N : ℕ, 0 < N → ∀ r s Mi ki : ℝ,
    ∀ d : InnerRemainderFamily b B φ N r s Mi ki,
    0 ≤ s → r / (4 * (N : ℝ)) ≤ radius → ∀ j : ℕ, Measurable (actualInnerPoleDensity d j)
  bound : ∀ s : ℝ, 0 < s → s ≤ cutoff → ∀ N : ℕ, 0 < N →
    ∀ v : Fin N → ℝ, ∀ T : ℂ, (∑ i, v i ^ 2) ≤ s → ‖T‖ ≤ radius →
    realPhaseTotal B φ N v T = (N : ℂ) * ((φ : ℂ) * Complex.I) →
    ∀ k : ℕ, 0 < (∑ i, v i ^ 2) →
      ‖(-(2 * completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 T (fun i => (v i : ℂ))) /
          deriv (realPhaseTotal B φ N v) T) / T ^ k‖ ≤
        (2 * allWindingCenterMagnitude N (b 0) φ * realWindingVandermondeSquared N v *
          Real.exp (C * (N : ℝ) * s)) / (A * (N : ℝ)) /
          (((1 / 2 - K * s) * (∑ i, v i ^ 2)) / (N : ℝ)) ^ k

theorem exists_physical_winding_residue_control {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) : Nonempty (PhysicalWindingResidueControl b B φ) := by
  obtain ⟨R, s, A, K, C, hR, hs, hA, hK, hC, hKs, hbound⟩ :=
    exists_actual_all_winding_residue_bounds hb hB hφ hπ hBi hbsq
  obtain ⟨rJ, hrJ, hmeas⟩ := exists_actual_inner_pole_density_measurable_radius hb hB hφ hπ hBi hbsq
  let radius := min R (rJ / 2)
  let cutoff := min s (min 1 (Real.pi ^ 2 / 2))
  have hcut : 0 < cutoff := lt_min hs (lt_min zero_lt_one (half_pos (sq_pos_of_pos Real.pi_pos)))
  have hcutS : cutoff ≤ s := min_le_left _ _
  refine ⟨{
    radius := radius
    cutoff := cutoff
    A := A
    K := K
    C := C
    radius_pos := lt_min hR (half_pos hrJ)
    cutoff_pos := hcut
    A_pos := hA
    K_pos := hK
    C_pos := hC
    cutoff_le_one := (min_le_right _ _).trans (min_le_left _ _)
    cutoff_lt_pi_sq := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
      (half_lt_self (sq_pos_of_pos Real.pi_pos))
    K_cutoff := (mul_le_mul_of_nonneg_left hcutS hK.le).trans hKs
    center_nonneg := fun n => allWindingCenterMagnitude_nonneg n (b 0) hφ hπ
    measurable := ?_
    bound := ?_ }⟩
  · intro N hN r σ Mi ki d hσ hr j
    exact hmeas N hN r σ Mi ki d hσ
      (hr.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hrJ))) j
  · intro σ hσ hσc N hN v T hS hT hp k hSp
    exact (hbound σ hσ (hσc.trans hcutS) N hN v T hS
      (hT.trans (min_le_left _ _)) hp).2.2.2.2 k hSp

theorem centeredWindingAngles_continuous (n : ℕ) (w : ℤ) :
    Continuous (centeredWindingAngles (n := n) w) := by
  apply continuous_pi
  intro i
  exact continuous_const.add ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp continuous_subtype_val)

theorem physicalWindingSectorKernel_measurable {b B : ℂ → ℂ} {φ r s Mi ki : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki) (hsπ : s ≤ Real.pi ^ 2)
    (j : ℕ) (hm : Measurable (actualInnerPoleDensity d j)) (w : ℤ) :
    Measurable (physicalWindingSectorKernel d (j + 1) w) := by
  have heq : physicalWindingSectorKernel d (j + 1) w = fun v : constrainedPlane n =>
      if ‖v‖ ^ 2 + windingMass n w ≤ s then actualInnerPoleDensity d j (centeredWindingAngles w v) else 0 := by
    funext v
    change (if ‖v‖ ^ 2 + windingMass n w ≤ s then
      d.actualResidue (centeredWindingAngles w v) / d.pole (centeredWindingAngles w v) ^ (j + 1) else 0) = _
    by_cases hc : ‖v‖ ^ 2 + windingMass n w ≤ s
    · have hshort : angularShortSquare (centeredWindingAngles w v) ≤ s := by
        rw [angularShortSquare_eq_of_sq_sum_le_pi_sq _ (by rw [centeredWindingAngles_square]; exact hc.trans hsπ),
          centeredWindingAngles_square]
        exact hc
      simp only [actualInnerPoleDensity, shortCutDensity, hc, hshort, ↓reduceIte]
    · simp only [hc, ↓reduceIte]
  rw [heq]
  exact Measurable.ite (measurableSet_le ((continuous_norm.pow 2).add continuous_const).measurable measurable_const)
    (hm.comp (centeredWindingAngles_continuous n w).measurable) measurable_const

namespace PhysicalWindingResidueControl
variable {b B : ℂ → ℂ} {φ : ℝ} (c : PhysicalWindingResidueControl b B φ)

def sectorFactor (n k : ℕ) (s : ℝ) : ℝ :=
  (2 * allWindingCenterMagnitude (n + 1) (b 0) φ * Real.exp (c.C * (n + 1 : ℕ) * s) /
    (c.A * (n + 1 : ℕ))) * (((n + 1 : ℕ) : ℝ) / (1 / 2 - c.K * s)) ^ k

theorem alpha_pos {s : ℝ} (hs : s ≤ c.cutoff) : 0 < 1 / 2 - c.K * s := by
  have h := (mul_le_mul_of_nonneg_left hs c.K_pos.le).trans c.K_cutoff
  linarith

theorem sectorFactor_nonneg (n k : ℕ) {s : ℝ} (hs : s ≤ c.cutoff) : 0 ≤ c.sectorFactor n k s := by
  unfold sectorFactor
  exact mul_nonneg (div_nonneg (by positivity [c.center_nonneg (n + 1)])
    (mul_pos c.A_pos (by positivity)).le) (pow_nonneg (div_pos (by positivity) (c.alpha_pos hs)).le k)

set_option maxHeartbeats 1000000 in
theorem sector_kernel_beta_bound {r s Mi ki : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki)
    (hs : 0 < s) (hsc : s ≤ c.cutoff) (hr : r / (4 * (n + 1 : ℕ)) ≤ c.radius)
    (j : ℕ) {w : ℤ} (hw : w ≠ 0) :
    Measurable (physicalWindingSectorKernel d (j + 1) w) ∧
      ∀ v : constrainedPlane n,
        ‖physicalWindingSectorKernel d (j + 1) w v‖ ≤
          c.sectorFactor n (j + 1) s * realQuadraticWeight n (j + 1) (windingMass n w) v := by
  have hsπ : s ≤ Real.pi ^ 2 := hsc.trans c.cutoff_lt_pi_sq.le
  refine ⟨physicalWindingSectorKernel_measurable d hsπ j
    (c.measurable (n + 1) (Nat.succ_pos n) r s Mi ki d hs.le hr j) w, ?_⟩
  intro v
  have hm := windingMass_pos n hw
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hα := c.alpha_pos hsc
  change ‖if ‖v‖ ^ 2 + windingMass n w ≤ s then
    d.actualResidue (centeredWindingAngles w v) / d.pole (centeredWindingAngles w v) ^ (j + 1) else 0‖ ≤ _
  by_cases hcut : ‖v‖ ^ 2 + windingMass n w ≤ s
  · have hshort : angularShortSquare (centeredWindingAngles w v) ≤ s := by
      rw [angularShortSquare_eq_of_sq_sum_le_pi_sq _ (by rw [centeredWindingAngles_square]; exact hcut.trans hsπ),
        centeredWindingAngles_square]
      exact hcut
    have hsum : 0 < ∑ i, centeredWindingAngles w v i ^ 2 := by
      rw [centeredWindingAngles_square]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) hm
    have hbnd := c.bound s hs hsc (n + 1) (Nat.succ_pos n) (centeredWindingAngles w v)
      (d.pole (centeredWindingAngles w v)) (by rw [centeredWindingAngles_square]; exact hcut)
      ((d.pole_bound ⟨_, hshort⟩).trans hr) (d.pole_phase (Nat.succ_pos n) _ hshort) (j + 1) hsum
    simp only [neg_div, norm_neg] at hbnd
    rw [centeredWindingAngles_vandermonde, centeredWindingAngles_square] at hbnd
    simp only [hcut, ↓reduceIte]
    apply hbnd.trans_eq
    unfold sectorFactor realQuadraticWeight windingMass
    rw [div_pow, mul_pow, div_pow]
    field_simp
    ring
  · simp only [hcut, ↓reduceIte, norm_zero]
    exact mul_nonneg (c.sectorFactor_nonneg n (j + 1) hsc)
      (realQuadraticWeight_nonneg n (j + 1) hm.le v)

theorem sector_coefficient_beta_bound {r s Mi ki : ℝ} {n α j : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki)
    (hn : 0 < n) (hα : radialShape n = (α : ℝ)) (hj : α < j + 1)
    (hs : 0 < s) (hsc : s ≤ c.cutoff) (hr : r / (4 * (n + 1 : ℕ)) ≤ c.radius)
    {w : ℤ} (hw : w ≠ 0) :
    Integrable (physicalWindingSectorKernel d (j + 1) w) (independentMeasure n) ∧
      ‖physicalWindingSectorCoefficient d j w‖ ≤ c.sectorFactor n (j + 1) s *
        (constrainedGaussianIntegral n * ((j - α).factorial : ℝ) /
          ((j.factorial : ℝ) * windingMass n w ^ (j + 1 - α))) := by
  obtain ⟨hm, hbnd⟩ := c.sector_kernel_beta_bound d hs hsc hr j hw
  have hi := realQuadraticWeight_integrable hn hα hj (windingMass_pos n hw)
  have hc := c.sectorFactor_nonneg n (j + 1) hsc
  have hFi : Integrable (physicalWindingSectorKernel d (j + 1) w) (independentMeasure n) :=
    (hi.const_mul _).mono' hm.aestronglyMeasurable (Eventually.of_forall hbnd)
  refine ⟨hFi, ?_⟩
  unfold physicalWindingSectorCoefficient
  rw [norm_neg]
  calc
    _ ≤ ∫ v, ‖physicalWindingSectorKernel d (j + 1) w v‖ ∂independentMeasure n := norm_integral_le_integral_norm _
    _ ≤ ∫ v, c.sectorFactor n (j + 1) s * realQuadraticWeight n (j + 1) (windingMass n w) v ∂independentMeasure n :=
      integral_mono_ae hFi.norm (hi.const_mul _) (Eventually.of_forall hbnd)
    _ = _ := by
      rw [integral_const_mul, integral_realQuadraticWeight hn hα hj (windingMass_pos n hw)]
      simp only [Nat.add_sub_cancel, show j + 1 - α - 1 = j - α by omega]

end PhysicalWindingResidueControl
end
end IsingBulk.AnisoF002.NegativeHT
