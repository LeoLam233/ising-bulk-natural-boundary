import IsingBulk.AnisoF002.Audit.RouteCheck

/-! Lightweight audit self-test.  These declarations are test fixtures only;
they are not included in the F002 mathematical root or counted as progress.
The synthetic historical name tests that a forbidden value dependency is
noticed even when the alias's statement is just `True`.  The separate
HistoricalAliasControl file tests the actual completed ANISO endpoint. -/
namespace AnisoF002AuditSelfTest

theorem harmless (p : Prop) (h : p) : p := h

def typeOnlyMechanism : Prop := True

theorem type_only (h : typeOnlyMechanism) : typeOnlyMechanism := h

end AnisoF002AuditSelfTest

namespace IsingBulk.AnisoF002AuditSyntheticHistorical

theorem fixture : True := True.intro

end IsingBulk.AnisoF002AuditSyntheticHistorical

namespace AnisoF002AuditSelfTest

theorem indirect_forbidden : True :=
  IsingBulk.AnisoF002AuditSyntheticHistorical.fixture

end AnisoF002AuditSelfTest

set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd AnisoF002Audit.auditRoot `AnisoF002AuditSelfTest.harmless
run_cmd do
  AnisoF002Audit.assertHistoricalRejected
    `AnisoF002AuditSelfTest.indirect_forbidden
    `IsingBulk.AnisoF002AuditSyntheticHistorical.fixture

run_cmd do
  AnisoF002Audit.assertTypeOnlyRejected
    `AnisoF002AuditSelfTest.type_only
    `AnisoF002AuditSelfTest.typeOnlyMechanism
