import IsingBulk.HT.Contour.PhysicalLatticeResidue
import IsingBulk.HT.Contour.PhysicalLatticeReflection
import IsingBulk.HT.Final.FourierSummation
import IsingBulk.First.NormalizationIntegral
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute full-lattice summation of the actual physical coefficients

The displacement powers on a fixed interior double contour have the common
ratio r^N < 1. Their two-sided product is an absolutely summable majorant
before the infinite lattice sum is interchanged with the integral. Summing
both genuine displacement coordinates then gives exactly standardDensity.
No Fourier summability, lattice-sum identity, or physical-contour equality is
assumed in the endpoint.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final Set MeasureTheory
open scoped BigOperators

theorem physical_real_twoSided_geometric_summable {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun n : ℤ => a^n.natAbs) := by
  have hs := summable_geometric_of_lt_one ha ha1
  apply Summable.of_nat_of_neg
  · simpa using hs
  · simpa using hs

theorem physical_twoSided_geometric_norm_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℤ => ‖z^n.natAbs‖) := by
  simpa only [norm_pow] using
    physical_real_twoSided_geometric_summable (norm_nonneg z) hz

/-- The product series is absolutely summable, not just two iterated formal
geometric sums. -/
theorem physical_geometric_lattice_sum {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (∑' v : ℤ × ℤ, x^v.1.natAbs*y^v.2.natAbs) =
      ((1+x)/(1-x))*((1+y)/(1-y)) := by
  rw [← tsum_mul_tsum_of_summable_norm
    (physical_twoSided_geometric_norm_summable hx)
    (physical_twoSided_geometric_norm_summable hy),
    vertical_displacement_geometric_sum hx,
    vertical_displacement_geometric_sum hy]

/-- Exact absolute integral majorant on a common-radius contour. This
statement is used with the real, coupled Ising amplitude, not a product of
independent one-body amplitudes. -/
theorem physical_geometric_integral_norm_summable
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A X Y : α → ℂ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hX : ∀ p, ‖X p‖=a) (hY : ∀ p, ‖Y p‖=a) :
    Summable (fun v : ℤ × ℤ =>
      ∫ p, ‖A p*(X p^v.1.natAbs*Y p^v.2.natAbs)‖ ∂μ) := by
  have hs := physical_real_twoSided_geometric_summable ha ha1
  have hp : Summable (fun v : ℤ × ℤ => a^v.1.natAbs*a^v.2.natAbs) :=
    hs.mul_of_nonneg hs (fun _ => pow_nonneg ha _) (fun _ => pow_nonneg ha _)
  convert hp.mul_left (∫ p, ‖A p‖ ∂μ) using 1
  funext v
  simp only [norm_mul,norm_pow,hX,hY,integral_mul_const]

theorem physical_angle_coordinateProduct_norm {N : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (phi : Fin N → ℝ) :
    ‖coordinateProduct (angleTuple r phi)‖ = r^N := by
  simp only [coordinateProduct,norm_prod,angleTuple,anglePoint_norm hr,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem physicalLatticeCoefficient_horizontal_natAbs (N : ℕ) {t : ℝ}
    (ht : 1 < t) (m : ℕ) (n : ℤ) :
    physicalLatticeCoefficient N t m n =
      physicalLatticeCoefficient N t m (n.natAbs:ℤ) := by
  rw [Int.natCast_natAbs]
  by_cases hn : 0 ≤ n
  · rw [abs_of_nonneg hn]
  · rw [abs_of_neg (lt_of_not_ge hn)]
    exact (physicalLatticeCoefficient_horizontal_reflection N ht m n).symm

/-- The actual full-lattice coefficient has its fixed-radius double-angular
integral with both displacement powers retained. -/
theorem physicalFullLatticeCoefficient_eq_box (N : ℕ) (hN : 0 < N)
    {t r : ℝ} (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) (v : ℤ × ℤ) :
    physicalFullLatticeCoefficient N t v =
      (N.factorial:ℂ)⁻¹ *
        ∫ p in angleBox N ×ˢ angleBox N,
          doubleAngularDensityOf r (onsiteDensity (t:ℂ)) p *
            ((coordinateProduct (angleTuple r p.1))^v.1.natAbs *
             (coordinateProduct (angleTuple r p.2))^v.2.natAbs) := by
  have hO := (normalizationDensities_continuous_angles N hN r (t:ℂ)
    (rightRoot (t:ℂ)) (rightRoot_admissible hr hr1 hm)).1
  have hX := continuous_coordinateProduct (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    angleTuple r p.1) ((angleTuple_continuous r).comp continuous_fst)
  have hY := continuous_coordinateProduct (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    angleTuple r p.2) ((angleTuple_continuous r).comp continuous_snd)
  unfold physicalFullLatticeCoefficient
  rw [physicalLatticeCoefficient_horizontal_natAbs N ht,
    physicalLatticeCoefficient_eq_double_contour N v.1.natAbs v.2.natAbs ht hr hr1 hm]
  have hinner (y : Fin N → ℂ) :
      (coordinateProduct y)^v.2.natAbs *
        multiCircleIntegral r N (fun x =>
          (coordinateProduct x)^v.1.natAbs*onsiteDensity (t:ℂ) x y) =
      multiCircleIntegral r N (fun x =>
        (coordinateProduct y)^v.2.natAbs *
          ((coordinateProduct x)^v.1.natAbs*onsiteDensity (t:ℂ) x y)) :=
    (multiCircleIntegral_const_mul r N _ _).symm
  simp_rw [hinner]
  rw [doubleCircleIntegral_eq_product N r _
    ((hY.pow _).mul ((hX.pow _).mul hO))]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  unfold doubleAngularDensityOf
  ring

theorem physical_standardDensity_from_lattice_kernel {N : ℕ} (s : ℂ)
    (x y : Fin N → ℂ)
    (hx : coordinateProduct x ≠ 0) (hy : coordinateProduct y ≠ 0)
    (hx1 : 1-coordinateProduct x ≠ 0) (hy1 : 1-coordinateProduct y ≠ 0) :
    onsiteDensity s x y *
      (((1+coordinateProduct x)/(1-coordinateProduct x)) *
       ((1+coordinateProduct y)/(1-coordinateProduct y))) =
      standardDensity s x y := by
  unfold onsiteDensity standardDensity
  field_simp [hx,hy,hx1,hy1]
  ring

/-- Absolute convergence and the exact value of the full square-lattice sum
at every positive particle number, hence in particular every odd HT order.
All summability and sum/integral exchange obligations are discharged here. -/
theorem physicalFullLatticeCoefficient_summable_eq_standardFormFactor
    (N : ℕ) (hN : 0 < N) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    Summable (fun v : ℤ × ℤ => ‖physicalFullLatticeCoefficient N t v‖) ∧
      (∑' v : ℤ × ℤ, physicalFullLatticeCoefficient N t v) =
        standardFormFactor N r (t:ℂ) := by
  let S := angleBox N ×ˢ angleBox N
  let A := doubleAngularDensityOf r (onsiteDensity (N := N) (t:ℂ))
  let X := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    coordinateProduct (angleTuple r p.1)
  let Y := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    coordinateProduct (angleTuple r p.2)
  let F := fun (v : ℤ × ℤ) p => A p*(X p^v.1.natAbs*Y p^v.2.natAbs)
  obtain ⟨hO,hStd⟩ := normalizationDensities_continuous_angles N hN r (t:ℂ)
    (rightRoot (t:ℂ)) (rightRoot_admissible hr hr1 hm)
  have hA : Continuous A := doubleAngularDensityOf_continuous N r _ hO
  have hXc : Continuous X := continuous_coordinateProduct _
    ((angleTuple_continuous r).comp continuous_fst)
  have hYc : Continuous Y := continuous_coordinateProduct _
    ((angleTuple_continuous r).comp continuous_snd)
  have hX (p) : ‖X p‖=r^N := physical_angle_coordinateProduct_norm hr.le _
  have hY (p) : ‖Y p‖=r^N := physical_angle_coordinateProduct_norm hr.le _
  have ha : 0 ≤ r^N := pow_nonneg hr.le _
  have ha1 : r^N < 1 := pow_lt_one₀ hr.le hr1 hN.ne'
  have hi (v : ℤ × ℤ) : IntegrableOn (F v) S :=
    (hA.mul ((hXc.pow _).mul (hYc.pow _))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hsI : Summable (fun v : ℤ × ℤ => ∫ p in S, ‖F v p‖) :=
    physical_geometric_integral_norm_summable (volume.restrict S) A X Y ha ha1 hX hY
  have hsNorm : Summable (fun v : ℤ × ℤ => ‖∫ p in S, F v p‖) :=
    hsI.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)
  have hbox (v : ℤ × ℤ) :
      physicalFullLatticeCoefficient N t v =
        (N.factorial:ℂ)⁻¹*(∫ p in S, F v p) :=
    physicalFullLatticeCoefficient_eq_box N hN ht hr hr1 hm v
  constructor
  · simpa only [hbox,norm_mul] using hsNorm.mul_left ‖(N.factorial:ℂ)⁻¹‖
  · calc
      (∑' v : ℤ × ℤ, physicalFullLatticeCoefficient N t v) =
          (N.factorial:ℂ)⁻¹*(∑' v : ℤ × ℤ, ∫ p in S, F v p) := by
            simp_rw [hbox]
            rw [tsum_mul_left]
      _ = (N.factorial:ℂ)⁻¹*(∫ p in S, ∑' v : ℤ × ℤ, F v p) := by
            rw [integral_tsum_of_summable_integral_norm hi hsI]
      _ = (N.factorial:ℂ)⁻¹*(∫ p in S,
          A p*(((1+X p)/(1-X p))*((1+Y p)/(1-Y p)))) := by
            congr 1
            apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
            intro p _
            simp only [F,tsum_mul_left]
            rw [physical_geometric_lattice_sum ((hX p).trans_lt ha1)
              ((hY p).trans_lt ha1)]
      _ = standardFormFactor N r (t:ℂ) := by
            unfold standardFormFactor
            rw [doubleCircleIntegral_eq_product N r _ hStd]
            congr 1
            apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
            intro p _
            have hx0 : coordinateProduct (angleTuple r p.1) ≠ 0 := by
              apply Finset.prod_ne_zero_iff.mpr
              intro i _
              exact norm_ne_zero_iff.mp ((anglePoint_norm hr.le (p.1 i)).trans_ne hr.ne')
            have hy0 : coordinateProduct (angleTuple r p.2) ≠ 0 := by
              apply Finset.prod_ne_zero_iff.mpr
              intro i _
              exact norm_ne_zero_iff.mp ((anglePoint_norm hr.le (p.2 i)).trans_ne hr.ne')
            have hx1 : 1-coordinateProduct (angleTuple r p.1) ≠ 0 :=
              one_sub_coordinateProduct_ne_zero hN
                (fun i => (anglePoint_norm hr.le (p.1 i)).trans_lt hr1)
            have hy1 : 1-coordinateProduct (angleTuple r p.2) ≠ 0 :=
              one_sub_coordinateProduct_ne_zero hN
                (fun i => (anglePoint_norm hr.le (p.2 i)).trans_lt hr1)
            dsimp only [A,X,Y,doubleAngularDensityOf]
            rw [mul_assoc,physical_standardDensity_from_lattice_kernel
              (t:ℂ) _ _ hx0 hy0 hx1 hy1]

theorem physicalFullLatticeCoefficient_summable (N : ℕ) (hN : 0 < N)
    {t r : ℝ} (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    Summable (physicalFullLatticeCoefficient N t) :=
  (physicalFullLatticeCoefficient_summable_eq_standardFormFactor
    N hN ht hr hr1 hm).1.of_norm

theorem physicalFullLatticeCoefficient_tsum_eq_standardFormFactor
    (N : ℕ) (hN : 0 < N) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    (∑' v : ℤ × ℤ, physicalFullLatticeCoefficient N t v) =
      standardFormFactor N r (t:ℂ) :=
  (physicalFullLatticeCoefficient_summable_eq_standardFormFactor
    N hN ht hr hr1 hm).2

end
end IsingBulk.HT.Contour
