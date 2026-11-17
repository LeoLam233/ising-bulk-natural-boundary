import IsingBulk.AnisoF002.Audit.C03FinalMathRoot
import IsingBulk.AnisoF002.Audit.C03SupportPolicy04R2

/-! Final complete checked type/value/constructor audit under the
unchanged finite, independently inspected historical support catalogue.
Mechanisms must occur in stored proof bodies, not only in annotations. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

run_cmd do
  let session ← AnisoF002Audit.newSession
  AnisoF002Audit.C03Cohort04R2.checkDomainNumeralHelpersIn session
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.full_uniform_field_conclusion
    #[`IsingBulk.AnisoF002.literal_fullAnalyticConclusion,
      `IsingBulk.AnisoF002.RegularTail.C03.literal_realPhysicalIdentification,
      `IsingBulk.AnisoF002.Physical.literal_realUniformFieldIdentification]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.literal_fullAnalyticConclusion
    #[`IsingBulk.AnisoF002.Isotropic.isotropic_high_normalized_naturalBoundary,
      `IsingBulk.AnisoF002.Isotropic.isotropic_low_normalized_naturalBoundary,
      `IsingBulk.AnisoF002.Isotropic.isotropic_high_physical_naturalBoundary,
      `IsingBulk.AnisoF002.Isotropic.isotropic_low_physical_naturalBoundary,
      `IsingBulk.AnisoF002.RegularTail.C03.anisotropic_high_normalized_naturalBoundary,
      `IsingBulk.AnisoF002.RegularTail.C03.anisotropic_low_normalized_naturalBoundary,
      `IsingBulk.AnisoF002.RegularTail.C03.anisotropic_high_physical_naturalBoundary,
      `IsingBulk.AnisoF002.RegularTail.C03.anisotropic_low_physical_naturalBoundary]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.full_analytic_conclusion
    #[`IsingBulk.AnisoF002.literal_fullAnalyticConclusion]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.Isotropic.isotropic_high_normalized_naturalBoundary
    #[`IsingBulk.AnisoF002.Isotropic.isotropic_positive_prime_no_radial_germ,
      `IsingBulk.AnisoF002.Isotropic.isotropic_negative_prime_no_radial_germ]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.Isotropic.isotropic_low_normalized_naturalBoundary
    #[`IsingBulk.AnisoF002.Isotropic.isotropic_even_prime_no_radial_germ]
  for name in #[`IsingBulk.AnisoF002.Isotropic.isotropic_positive_prime_no_radial_germ,
      `IsingBulk.AnisoF002.Isotropic.isotropic_even_prime_no_radial_germ,
      `IsingBulk.AnisoF002.Isotropic.isotropic_negative_prime_no_radial_germ] do
    AnisoF002Audit.C03Cohort04R2.auditTheoremIn session name
      #[`IsingBulk.AnisoF002.Isotropic.IsotropicFirstArithmeticData.full_first_scaled_limit,
        `IsingBulk.AnisoF002.Isotropic.IsotropicFirstArithmeticData.actual_lower_particle_bound,
        `IsingBulk.AnisoF002.Isotropic.actual_complete_series_no_radial_germ_of_first]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.Isotropic.exists_actual_full_particle_summable_jet_majorants
    #[`IsingBulk.AnisoF002.Isotropic.exists_actual_right_summable_jet_majorants,
      `IsingBulk.AnisoF002.Isotropic.exists_actual_mixed_summable_jet_majorants,
      `IsingBulk.AnisoF002.Isotropic.exists_actual_anchor_summable_jet_majorants]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.Isotropic.actual_full_first_particle_scaled_limit
    #[`IsingBulk.AnisoF002.Isotropic.exists_actual_first_compact_mean_scaled_limit,
      `IsingBulk.AnisoF002.Isotropic.exists_actual_finite_partition_control]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.Isotropic.actual_complete_series_no_radial_germ_of_first
    #[`IsingBulk.AnisoF002.Isotropic.exists_actual_complete_series_local_jet_majorants,
      `IsingBulk.AnisoF002.Isotropic.exists_actual_full_particle_summable_jet_majorants]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.NegativeHT.negative_physical_odd_sum_no_analytic_inward_germ
    #[`IsingBulk.AnisoF002.NegativeHT.negative_physical_full_taylor_growth,
      `IsingBulk.AnisoF002.NegativeHT.physical_oddSum_boundary_jets]
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session
    `IsingBulk.AnisoF002.Physical.literal_realUniformFieldIdentification
    #[`IsingBulk.AnisoF002.RegularTail.C03.literal_realPhysicalIdentification,
      `IsingBulk.AnisoF002.Physical.literal_uniformField_of_realIdentification]
  AnisoF002Audit.C03Cohort04R2.auditAllMathematicsIn session
  AnisoF002Audit.auditSessionStats session
  Lean.logInfo "C03_FINAL_STORED_ROUTE_AGGREGATE_PASS"
