import IsingBulk.AnisoF002.C03.NegativeWindingSectorMajorants
import IsingBulk.AnisoF002.C03.NegativeWindingCenterEnvelope

/-!
# Every actual high-particle winding residue, at every Taylor order

The exact complete winding kernel is dominated on the full constrained
unit ball.  This gives the half N² log N decay before choosing j, including
all sectors and all populations without a Beta convergence restriction.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology BigOperators Classical

theorem windingMass_lower (n : ℕ) {w : ℤ} (hw : w ≠ 0) :
    Real.pi ^ 2 / (n + 1 : ℕ) ≤ windingMass n w := by
  have hwa : (1 : ℤ) ≤ |w| := by have := abs_pos.mpr hw; omega
  have hwar : (1 : ℝ) ≤ |(w : ℝ)| := by exact_mod_cast hwa
  have hw2 : (1 : ℝ) ≤ (w : ℝ) ^ 2 := by nlinarith [sq_abs (w : ℝ)]
  unfold windingMass
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg Real.pi]

namespace PhysicalWindingResidueControl
variable {b B : ℂ → ℂ} {φ : ℝ} (c : PhysicalWindingResidueControl b B φ)

def highSectorFactor (n k : ℕ) (s : ℝ) : ℝ :=
  (2 * allWindingCenterMagnitude (n + 1) (b 0) φ * Real.exp (c.C * (n + 1 : ℕ) * s) /
    (c.A * (n + 1 : ℕ))) * (4 * ((n + 1 : ℕ) : ℝ) ^ 2 / Real.pi ^ 2) ^ k

theorem highSectorFactor_nonneg (n k : ℕ) (s : ℝ) : 0 ≤ c.highSectorFactor n k s := by
  have hH := c.center_nonneg (n + 1)
  have hA := c.A_pos
  unfold highSectorFactor
  positivity

theorem sector_kernel_high_bound {r s Mi ki : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki)
    (hs : 0 < s) (hsc : s ≤ c.cutoff) (hr : r / (4 * (n + 1 : ℕ)) ≤ c.radius)
    (j : ℕ) {w : ℤ} (hw : w ≠ 0) (v : constrainedPlane n) :
    ‖physicalWindingSectorKernel d (j + 1) w v‖ ≤
      c.highSectorFactor n (j + 1) s * planeVandermonde v := by
  have hbnd := (c.sector_kernel_beta_bound d hs hsc hr j hw).2 v
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hα := c.alpha_pos hsc
  have hm := windingMass_pos n hw
  have hS : 0 < windingMass n w + ‖v‖ ^ 2 := add_pos_of_pos_of_nonneg hm (sq_nonneg _)
  have hSlo : Real.pi ^ 2 / (n + 1 : ℕ) ≤ windingMass n w + ‖v‖ ^ 2 := by
    linarith [windingMass_lower n hw, sq_nonneg ‖v‖]
  have hα4 : (1 / 4 : ℝ) ≤ 1 / 2 - c.K * s := by
    have h := (mul_le_mul_of_nonneg_left hsc c.K_pos.le).trans c.K_cutoff
    linarith
  have hden : (1 / 4 : ℝ) * (Real.pi ^ 2 / (n + 1 : ℕ)) ≤
      (1 / 2 - c.K * s) * (windingMass n w + ‖v‖ ^ 2) :=
    mul_le_mul hα4 hSlo (by positivity) hα.le
  have hratio : (((n + 1 : ℕ) : ℝ) / ((1 / 2 - c.K * s) * (windingMass n w + ‖v‖ ^ 2))) ≤
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 / Real.pi ^ 2 := by
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) / ((1 / 4 : ℝ) * (Real.pi ^ 2 / (n + 1 : ℕ))) :=
        div_le_div_of_nonneg_left hN.le (by positivity) hden
      _ = _ := by field_simp
  have hbase : 0 ≤ 2 * allWindingCenterMagnitude (n + 1) (b 0) φ * Real.exp (c.C * (n + 1 : ℕ) * s) /
      (c.A * (n + 1 : ℕ)) := by
    have hH := c.center_nonneg (n + 1)
    have hA := c.A_pos
    positivity
  apply hbnd.trans
  unfold sectorFactor realQuadraticWeight highSectorFactor
  calc
    _ = (2 * allWindingCenterMagnitude (n + 1) (b 0) φ * Real.exp (c.C * (n + 1 : ℕ) * s) /
        (c.A * (n + 1 : ℕ))) *
        (((n + 1 : ℕ) : ℝ) / ((1 / 2 - c.K * s) * (windingMass n w + ‖v‖ ^ 2))) ^ (j + 1) *
        planeVandermonde v := by
      have halg (β x a z V : ℝ) (k : ℕ) :
          β * (x / a) ^ k * (V / z ^ k) = β * (x / (a * z)) ^ k * V := by
        simp only [div_eq_mul_inv, mul_inv_rev, mul_pow, inv_pow]
        ring
      exact halg _ _ _ _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_pos hN (mul_pos hα hS)).le hratio _) hbase) (planeVandermonde_nonneg v)

theorem sector_kernel_zero_off_unit_ball {r s Mi ki : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki) (hsc : s ≤ c.cutoff)
    (k : ℕ) (w : ℤ) (v : constrainedPlane n) (hv : v ∉ Metric.closedBall 0 1) :
    physicalWindingSectorKernel d k w v = 0 := by
  have hn : (1 : ℝ) < ‖v‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hv
  have hm : 0 ≤ windingMass n w := by unfold windingMass; positivity
  have hs1 : s ≤ 1 := hsc.trans c.cutoff_le_one
  have hcut : ¬ ‖v‖ ^ 2 + windingMass n w ≤ s := by nlinarith
  change (if ‖v‖ ^ 2 + windingMass n w ≤ s then _ else 0) = 0
  simp only [hcut, ↓reduceIte]

theorem sector_coefficient_high_bound {r s Mi ki : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki)
    (hn : 0 < n) (hs : 0 < s) (hsc : s ≤ c.cutoff) (hr : r / (4 * (n + 1 : ℕ)) ≤ c.radius)
    (j : ℕ) {w : ℤ} (hw : w ≠ 0) :
    Integrable (physicalWindingSectorKernel d (j + 1) w) (independentMeasure n) ∧
      ‖physicalWindingSectorCoefficient d j w‖ ≤ c.highSectorFactor n (j + 1) s *
        Real.exp (-((n + 1 : ℕ) : ℝ) ^ 2 / 2 * Real.log ((n + 1 : ℕ) : ℝ) +
          4 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hm := (c.sector_kernel_beta_bound d hs hsc hr j hw).1
  have hbnd := c.sector_kernel_high_bound d hs hsc hr j hw
  have hc := c.highSectorFactor_nonneg n (j + 1) s
  have hPi : IntegrableOn planeVandermonde (Metric.closedBall (0 : constrainedPlane n) 1)
      (independentMeasure n) := (continuous_planeVandermonde n).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hFiOn : IntegrableOn (physicalWindingSectorKernel d (j + 1) w)
      (Metric.closedBall (0 : constrainedPlane n) 1) (independentMeasure n) :=
    (hPi.const_mul _).mono' hm.aestronglyMeasurable (Eventually.of_forall hbnd)
  have hzero := c.sector_kernel_zero_off_unit_ball d hsc (j + 1) w
  have hsupport : Function.support (physicalWindingSectorKernel d (j + 1) w) ⊆
      Metric.closedBall (0 : constrainedPlane n) 1 := by
    intro v hv
    by_contra hn
    exact hv (hzero v hn)
  have hFi := (integrableOn_iff_integrable_of_support_subset hsupport).mp hFiOn
  refine ⟨hFi, ?_⟩
  unfold physicalWindingSectorCoefficient
  rw [norm_neg, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ ∫ v in Metric.closedBall (0 : constrainedPlane n) 1,
        ‖physicalWindingSectorKernel d (j + 1) w v‖ ∂independentMeasure n := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Metric.closedBall (0 : constrainedPlane n) 1,
        c.highSectorFactor n (j + 1) s * planeVandermonde v ∂independentMeasure n :=
      integral_mono_ae hFiOn.norm (hPi.const_mul _) (Eventually.of_forall hbnd)
    _ = c.highSectorFactor n (j + 1) s *
        ∫ v in Metric.closedBall (0 : constrainedPlane n) 1, planeVandermonde v ∂independentMeasure n := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (full_vandermonde_ball_exponential_bound hn zero_lt_one le_rfl) hc

end PhysicalWindingResidueControl

theorem windingSectorIndices_card_le (n : ℕ) : (windingSectorIndices n).card ≤ 2 * (n + 1) + 1 := by
  have hcard : (windingSectorIndices n).card ≤ (Finset.Icc (-(n + 1 : ℤ)) (n + 1)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hI : (Finset.Icc (-(n + 1 : ℤ)) (n + 1)).card = 2 * (n + 1) + 1 := by
    rw [Int.card_Icc]
    omega
  exact hcard.trans_eq hI

namespace PhysicalWindingResidueControl
variable {b B : ℂ → ℂ} {φ : ℝ} (c : PhysicalWindingResidueControl b B φ)

theorem all_sector_high_bound {r s Mi ki : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s Mi ki)
    (hn : 0 < n) (hs : 0 < s) (hsc : s ≤ c.cutoff) (hr : r / (4 * (n + 1 : ℕ)) ≤ c.radius)
    (j : ℕ) :
    (∑ w ∈ windingSectorIndices n, ‖physicalWindingSectorCoefficient d j w‖) ≤
      (2 * ((n + 1 : ℕ) : ℝ) + 1) * c.highSectorFactor n (j + 1) s *
        Real.exp (-((n + 1 : ℕ) : ℝ) ^ 2 / 2 * Real.log ((n + 1 : ℕ) : ℝ) +
          4 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hsum := Finset.sum_le_sum (s := windingSectorIndices n)
    (f := fun w => ‖physicalWindingSectorCoefficient d j w‖)
    (g := fun _ => c.highSectorFactor n (j + 1) s *
      Real.exp (-((n + 1 : ℕ) : ℝ) ^ 2 / 2 * Real.log ((n + 1 : ℕ) : ℝ) + 4 * ((n + 1 : ℕ) : ℝ) ^ 2))
    (fun w hw => (c.sector_coefficient_high_bound d hn hs hsc hr j
      (by obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hw).2; omega)).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  apply hsum.trans
  have hcard : ((windingSectorIndices n).card : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast windingSectorIndices_card_le n
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcard
    (mul_nonneg (c.highSectorFactor_nonneg n (j + 1) s) (Real.exp_pos _).le)

theorem exists_complete_high_particle_residue_bound (hφ : 0 < φ) (hπ : φ < Real.pi) :
    ∃ D : ℝ, 0 < D ∧ ∀ r s Mi ki : ℝ, ∀ n : ℕ,
      ∀ d : InnerRemainderFamily b B φ (n + 1) r s Mi ki,
      0 < n → 0 < s → s ≤ c.cutoff → r / (4 * (n + 1 : ℕ)) ≤ c.radius → ∀ j : ℕ,
        (∑ w ∈ windingSectorIndices n, ‖physicalWindingSectorCoefficient d j w‖) ≤
          Real.exp (2 * (j : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) -
            ((n + 1 : ℕ) : ℝ) ^ 2 / 2 * Real.log ((n + 1 : ℕ) : ℝ) +
            D * ((n + 1 : ℕ) : ℝ) ^ 2 + D * (j : ℝ) + D) := by
  obtain ⟨C0, hC0, hcenter⟩ := exists_allWindingCenterMagnitude_exponential (b 0) hφ hπ
  obtain ⟨D, hD, hscalar⟩ := high_particle_scalar_envelope c.A_pos c.C_pos.le hC0.le
    (by positivity : 0 < Real.pi ^ 2 / 4) c.cutoff_le_one
  refine ⟨D, hD, ?_⟩
  intro r s Mi ki n d hn hs hsc hr j
  apply (c.all_sector_high_bound d hn hs hsc hr j).trans
  apply le_trans _ (hscalar (n + 1) j (Nat.succ_le_succ (Nat.zero_le n)))
  unfold highSectorFactor
  rw [show 4 * ((n + 1 : ℕ) : ℝ) ^ 2 / Real.pi ^ 2 =
    ((n + 1 : ℕ) : ℝ) ^ 2 / (Real.pi ^ 2 / 4) by ring]
  have hH := c.center_nonneg (n + 1)
  have hA := c.A_pos
  have hC := c.C_pos
  have hfac : 2 * allWindingCenterMagnitude (n + 1) (b 0) φ *
      Real.exp (c.C * (n + 1 : ℕ) * s) / (c.A * (n + 1 : ℕ)) ≤
      2 * Real.exp (C0 * ((n + 1 : ℕ) : ℝ) ^ 2) *
      Real.exp (c.C * (n + 1 : ℕ) * c.cutoff) / (c.A * (n + 1 : ℕ)) := by
    gcongr
    exact hcenter (n + 1)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) + 1))
      (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 2 / (Real.pi ^ 2 / 4)) ^ (j + 1)))
    (Real.exp_pos (-((n + 1 : ℕ) : ℝ) ^ 2 / 2 * Real.log ((n + 1 : ℕ) : ℝ) +
      4 * ((n + 1 : ℕ) : ℝ) ^ 2)).le
  simpa only [mul_assoc] using hh

end PhysicalWindingResidueControl
end
end IsingBulk.AnisoF002.NegativeHT
