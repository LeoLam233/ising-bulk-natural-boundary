import IsingBulk.AnisoF002.Audit.C03SupportPolicy04R2
import IsingBulk.AnisoF002.Audit.HistoricalAliasControl

/-!
External audit controls only. The first uses the actual unchanged C001
dimension-uniform exact-normal-form endpoint and its already stored alias.
The second rejects a requested mechanism present only in a theorem's type.
Neither fixture is imported by any mathematical root or claimed as progress.
-/

namespace AnisoF002C03SupportControl04R2

theorem harmless (p : Prop) (h : p) : p := h

def typeOnlyMechanism : Prop := True

theorem type_only (h : typeOnlyMechanism) : typeOnlyMechanism := h

end AnisoF002C03SupportControl04R2

set_option maxHeartbeats 0
set_option maxRecDepth 100000

run_cmd do
  let session ← AnisoF002Audit.newSession
  AnisoF002Audit.C03Cohort04R2.auditTheoremIn session `AnisoF002C03SupportControl04R2.harmless
  AnisoF002Audit.C03Cohort04R2.assertTypeOnlyRejectedIn session
    `AnisoF002C03SupportControl04R2.type_only `AnisoF002C03SupportControl04R2.typeOnlyMechanism
  AnisoF002Audit.C03Cohort04R2.assertHistoricalRejectedIn session
    `AnisoF002NegativeControl.historical_alias
    `IsingBulk.Anisotropic.NegativeNormalForm.exists_dimension_uniform_exact_normal_form
  AnisoF002Audit.auditSessionStats session
  Lean.logInfo "C03_SUPPORT_CONTROLS_04_PASS"
