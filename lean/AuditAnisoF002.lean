import IsingBulkAnisoF002
import IsingBulk.AnisoF002.Audit.RouteCheck

/-!
# Checked-environment audit of the partial F002 mathematical root

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

  auditSessionStats session

#print axioms IsingBulk.AnisoF002.Geometry.spectral_regular_endpoint_strict
#print axioms IsingBulk.AnisoF002.RegularTail.gaussian_log_envelope_summable
#print axioms IsingBulk.AnisoF002.NegativeHT.complete_series_ne_zero
#print axioms IsingBulk.AnisoF002.Isotropic.deformedOccupancy_hasDerivAt
