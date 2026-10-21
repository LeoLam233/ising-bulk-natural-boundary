import IsingBulk.HT.Final.PhysicalSusceptibilityGerm
import IsingBulk.HT.Final.RealGermUniqueness

/-! Physical identification is logically separate from the analytic boundary
proof. A real physical representation alone does not identify an arbitrary
complex-valued function away from the real interval. This file makes the
necessary analyticity hypothesis explicit and proves uniqueness on the disk.
It does not prove the statistical-mechanical full-lattice representation. -/
namespace IsingBulk.HT.Final
noncomputable section
open Set Filter
open scoped Topology

/-- The explicit physical full-bulk representation identifies any analytic
beta-free continuation with the independently constructed full odd germ. -/
theorem physicalBulk_eqOn_unitDisk {X : ℂ → ℂ}
    (hX : AnalyticOnNhd ℂ X {s : ℂ | ‖s‖ < 1})
    (hrep : RealFullBulkRepresentation X) :
    EqOn X interiorFullBulk {s : ℂ | ‖s‖ < 1} :=
  analytic_unitDisk_eq_of_real_germ hX interiorFullBulk_analyticOn
    (fun _ hx hxsmall => interiorFullBulk_physical_real_germ hrep hx hxsmall)

/-- The physical susceptibility, including beta, is uniquely identified.
The real representation and analyticity premises remain visible in the type. -/
theorem physicalSusceptibility_eqOn_unitDisk {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ}
    (hchi : AnalyticOnNhd ℂ chi {s : ℂ | ‖s‖ < 1})
    (hrep : PhysicalSusceptibilityRepresentation J chi) :
    EqOn chi (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} :=
  analytic_unitDisk_eq_of_real_germ hchi
    (interiorPhysicalSusceptibility_analyticOn hJ)
    (fun _ hx hxsmall => physicalSusceptibility_real_germ hJ hrep hx hxsmall)

end
end IsingBulk.HT.Final
