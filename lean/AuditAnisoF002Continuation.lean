import IsingBulkAnisoF002Continuation
import IsingBulk.AnisoF002.Audit.RouteCheck

/-!
# Checked-environment audit of the partial F002 continuation mathematical root

The allowlist contains definitions only.  It cannot whitelist a historical
theorem or axiom.  All declarations are scanned, including private helpers
and lemmas not used by a displayed result.  Selected results additionally
require named new mechanisms in the stored-value body graph.

Passing this audit certifies the displayed partial development.  It is not
a claim that the missing exact physical terminal theorem has been proved.
-/

open AnisoF002Audit

set_option maxHeartbeats 0
set_option maxRecDepth 100000

run_cmd do
  let session ← newSession
  let definitions := #[`IsingBulk.Anisotropic.spectralS, `IsingBulk.Anisotropic.spectralT,
    `IsingBulk.Anisotropic.spectralA, `IsingBulk.Anisotropic.geometryF1,
    `IsingBulk.Anisotropic.geometryF2]
  auditAllNewDeclarationsIn session definitions
  auditRootIn session `IsingBulk.AnisoF002.Geometry.spectral_regular_endpoint_strict definitions
    #[`IsingBulk.AnisoF002.Geometry.regular_edge_strict_coordinate,
      `IsingBulk.AnisoF002.Geometry.endpoint_defect_identity]
  auditRootIn session `IsingBulk.AnisoF002.RegularTail.schur_uniform_squared_bound definitions
    #[`IsingBulk.AnisoF002.RegularTail.schur_norm_defect]
  auditRootIn session `IsingBulk.AnisoF002.RegularTail.fixed_block_uniform_majorant definitions
    #[`IsingBulk.AnisoF002.RegularTail.radial_kernel_le_power,
      `IsingBulk.AnisoF002.RegularTail.fixed_block_degree_budget]
  auditRootIn session `IsingBulk.AnisoF002.RegularTail.gaussian_log_envelope_summable definitions
    #[`IsingBulk.AnisoF002.RegularTail.eventually_log_absorption]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.two_sided_competitor_bound definitions
    #[`IsingBulk.AnisoF002.NegativeHT.exp_competitor_prefix_le]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.middle_window_norm_bound definitions
    #[`IsingBulk.AnisoF002.NegativeHT.two_sided_competitor_bound]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.complete_series_ne_zero definitions
    #[`IsingBulk.AnisoF002.NegativeHT.complete_series_lower_bound]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.centered_log_ratio_order_step definitions
    #[`IsingBulk.AnisoF002.NegativeHT.log_modelMagnitude_order_step]
  auditRootIn session `IsingBulk.AnisoF002.Isotropic.deformedOccupancy_hasDerivAt definitions
    #[`IsingBulk.AnisoF002.Isotropic.occupancy_path_hasDerivAt,
      `IsingBulk.AnisoF002.Isotropic.occupancy_rank_two_identity]
  auditRootIn session `IsingBulk.AnisoF002.Isotropic.complete_pair_product_bound definitions
    #[`IsingBulk.AnisoF002.Isotropic.sameCellPairs_lower,
      `IsingBulk.AnisoF002.Isotropic.card_sameCellPairs]
  auditRootIn session `IsingBulk.AnisoF002.Isotropic.pairVariance_protected_ne_zero definitions
    #[`IsingBulk.AnisoF002.Isotropic.pairVariance_coordinate_perturbation]

  auditRootIn session `IsingBulk.AnisoF002.Geometry.endpoint_boundary_criterion definitions
    #[`IsingBulk.AnisoF002.Geometry.endpoint_locus_realization,
      `IsingBulk.AnisoF002.Geometry.complex_singular_square_fiber_endpoint]
  auditRootIn session `IsingBulk.AnisoF002.Geometry.spectralSmallRootF002_physical definitions
    #[`IsingBulk.AnisoF002.Geometry.exists_unique_spectral_small_root,
      `IsingBulk.AnisoF002.Geometry.positive_real_spectral_gap_f002]
  auditRootIn session `IsingBulk.AnisoF002.Geometry.spectralSmallRootF002_compact_gap definitions
    #[`IsingBulk.AnisoF002.Geometry.exists_joint_analytic_spectral_root]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.complexRadialPeriod_eq definitions
    #[`IsingBulk.AnisoF002.NegativeHT.integral_complexRadialBeta]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.higherWinding_radialPeriod_sum_le definitions
    #[`IsingBulk.AnisoF002.NegativeHT.norm_radialPeriod_winding]
  auditRootIn session `IsingBulk.AnisoF002.Isotropic.exists_right_inverse_common_convex_neighborhood definitions
    #[`IsingBulk.AnisoF002.Isotropic.explicitRightInverse_second_derivative,
      `IsingBulk.AnisoF002.Isotropic.explicitRightInverse_on_right_arc]
  auditRootIn session `IsingBulk.AnisoF002.Isotropic.balancedAngularJacobian_det_ne_zero definitions
    #[`IsingBulk.AnisoF002.Isotropic.balancedAngularJacobian_injective]
  auditRootIn session `IsingBulk.AnisoF002.RegularTail.spectral_schur_pair_eq_canceled definitions
    #[`IsingBulk.AnisoF002.RegularTail.dispersion_pair_subtraction]

  auditRootIn session `IsingBulk.AnisoF002.Geometry.omegaHF002_eq_physical_component definitions
    #[`IsingBulk.AnisoF002.Geometry.endpoint_boundary_criterion,
      `IsingBulk.AnisoF002.Geometry.omegaHF002_starConvex]
  auditRootIn session `IsingBulk.AnisoF002.Geometry.omegaLF002_isSimplyConnected definitions
    #[`IsingBulk.AnisoF002.Geometry.omegaLF002_eq_shear_preimage]
  auditRootIn session `IsingBulk.AnisoF002.Geometry.profileDifference_locally_nonzero definitions
    #[`IsingBulk.AnisoF002.Geometry.profileDifference_ne_zero_at_first_tip]
  auditRootIn session `IsingBulk.AnisoF002.NegativeHT.exists_resonant_moving_pole_residue definitions
    #[`IsingBulk.AnisoF002.NegativeHT.movingPole_fderiv_formula]
  auditRootIn session `IsingBulk.AnisoF002.Isotropic.rightCovarianceField_on_real_right_arc definitions
    #[`IsingBulk.AnisoF002.Isotropic.rightArc_pairVariance_ne_zero,
      `IsingBulk.AnisoF002.Isotropic.second_secant_re_lower_bound]
  auditRootIn session `IsingBulk.AnisoF002.RegularTail.fullRootNumeratorF002_retained_factorization definitions
    #[`IsingBulk.AnisoF002.RegularTail.spectralCanceledPairF002_factorization]
  auditRootIn session `IsingBulk.AnisoF002.RegularTail.fullRootNumeratorF002_log_branch definitions
    #[`IsingBulk.AnisoF002.RegularTail.complete_anisotropy_power,
      `IsingBulk.AnisoF002.RegularTail.oneBody_exp_eq_inv_sinh]

  auditSessionStats session

#print axioms IsingBulk.AnisoF002.Geometry.spectral_regular_endpoint_strict
#print axioms IsingBulk.AnisoF002.RegularTail.gaussian_log_envelope_summable
#print axioms IsingBulk.AnisoF002.NegativeHT.complete_series_ne_zero
#print axioms IsingBulk.AnisoF002.Isotropic.deformedOccupancy_hasDerivAt
