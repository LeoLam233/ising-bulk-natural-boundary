import IsingBulk.Anisotropic.FormFactors.ContourContinuity
import IsingBulk.Anisotropic.FormFactors.LatticeMultiplier

/-! Absolute full-site summation of the literal anisotropic double contours.
The separate real-angular/residue identification is not assumed by this file. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Set MeasureTheory
open scoped BigOperators

def unscaledLatticeCoefficientAtRadius (N : ℕ) (r lam : ℝ) (z : ℂ) (v : ℤ × ℤ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y => multiCircleIntegral r N (fun x =>
    onsiteDensity lam z x y * (coordinateProduct x)^v.1.natAbs * (coordinateProduct y)^v.2.natAbs))

theorem unscaledLatticeCoefficientAtRadius_eq_box (N : ℕ) (hN : 0 < N)
    {r lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) (v : ℤ × ℤ) :
    unscaledLatticeCoefficientAtRadius N r lam z v =
      (N.factorial:ℂ)⁻¹ * ∫ p in angleBox N ×ˢ angleBox N,
        doubleAngularDensityOf r (onsiteDensity lam z) p *
          ((coordinateProduct (angleTuple r p.1))^v.1.natAbs *
            (coordinateProduct (angleTuple r p.2))^v.2.natAbs) := by
  have hO := (normalizationDensities_continuous_angles N hN h).1
  have hX := continuous_coordinateProduct (fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r p.1) ((angleTuple_continuous (N := N) r).comp continuous_fst)
  have hY := continuous_coordinateProduct (fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleTuple r p.2) ((angleTuple_continuous (N := N) r).comp continuous_snd)
  unfold unscaledLatticeCoefficientAtRadius
  rw [doubleCircleIntegral_eq_product N r _ ((hO.mul (hX.pow _)).mul (hY.pow _))]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  unfold doubleAngularDensityOf
  ring

/-- Actual absolute convergence over the entire infinite square lattice at
 each positive particle number, followed by the legitimate sum/integral swap. -/
theorem unscaledLattice_summable_eq_full (N : ℕ) (hN : 0 < N)
    {r lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    Summable (fun v : ℤ × ℤ => ‖unscaledLatticeCoefficientAtRadius N r lam z v‖) ∧
    (∑' v : ℤ × ℤ, unscaledLatticeCoefficientAtRadius N r lam z v) =
      unscaledFullCoefficientAtRadius N r lam z := by
  let S := angleBox N ×ˢ angleBox N
  let A := doubleAngularDensityOf r (onsiteDensity (N := N) lam z)
  let X := fun p : (Fin N → ℝ) × (Fin N → ℝ) => coordinateProduct (angleTuple r p.1)
  let Y := fun p : (Fin N → ℝ) × (Fin N → ℝ) => coordinateProduct (angleTuple r p.2)
  let F := fun (v : ℤ × ℤ) p => A p*(X p^v.1.natAbs*Y p^v.2.natAbs)
  have hA : Continuous A := doubleAngularDensityOf_continuous N r _
    (normalizationDensities_continuous_angles N hN h).1
  have hXc : Continuous X := continuous_coordinateProduct _ ((angleTuple_continuous r).comp continuous_fst)
  have hYc : Continuous Y := continuous_coordinateProduct _ ((angleTuple_continuous r).comp continuous_snd)
  have hX (p) : ‖X p‖ = r^N := physical_angle_coordinateProduct_norm h.1.le _
  have hY (p) : ‖Y p‖ = r^N := physical_angle_coordinateProduct_norm h.1.le _
  have ha : 0 ≤ r^N := pow_nonneg h.1.le _
  have ha1 : r^N < 1 := pow_lt_one₀ h.1.le h.2.1 hN.ne'
  have hi (v : ℤ × ℤ) : IntegrableOn (F v) S :=
    (hA.mul ((hXc.pow _).mul (hYc.pow _))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hsI : Summable (fun v : ℤ × ℤ => ∫ p in S, ‖F v p‖) :=
    physical_geometric_integral_norm_summable (volume.restrict S) A X Y ha ha1 hX hY
  have hsNorm : Summable (fun v : ℤ × ℤ => ‖∫ p in S, F v p‖) :=
    hsI.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  have hbox (v : ℤ × ℤ) : unscaledLatticeCoefficientAtRadius N r lam z v =
      (N.factorial:ℂ)⁻¹ * ∫ p in S, F v p := unscaledLatticeCoefficientAtRadius_eq_box N hN h v
  constructor
  · simpa only [hbox,norm_mul] using hsNorm.mul_left ‖(N.factorial:ℂ)⁻¹‖
  · calc
      (∑' v : ℤ × ℤ, unscaledLatticeCoefficientAtRadius N r lam z v) =
          (N.factorial:ℂ)⁻¹ * ∑' v : ℤ × ℤ, ∫ p in S, F v p := by
            simp_rw [hbox]
            rw [tsum_mul_left]
      _ = (N.factorial:ℂ)⁻¹ * ∫ p in S, ∑' v : ℤ × ℤ, F v p := by
            rw [integral_tsum_of_summable_integral_norm hi hsI]
      _ = (N.factorial:ℂ)⁻¹ * ∫ p in S,
          A p * (((1+X p)/(1-X p))*((1+Y p)/(1-Y p))) := by
            congr 1
            apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
            intro p _
            simp only [F,tsum_mul_left]
            rw [physical_geometric_lattice_sum ((hX p).trans_lt ha1) ((hY p).trans_lt ha1)]
      _ = unscaledFullCoefficientAtRadius N r lam z := by
            rw [unscaledFullCoefficientAtRadius_eq_box N hN h]
            congr 1
            apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
            intro p _
            dsimp [A,X,Y,doubleAngularDensityOf,onsiteDensity,fullDensity]
            simp only [div_eq_mul_inv,mul_inv_rev]
            ring
end
end IsingBulk.Anisotropic.FormFactors
