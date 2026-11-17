import AuditAnisoF002
import AuditAnisoF002Continuation
import IsingBulk.AnisoF002.Audit.TargetContract
import IsingBulk.AnisoF002.Audit.ContinuationTargetContract
import IsingBulk.AnisoF002.Audit.HistoricalAliasControl
import IsingBulk.AnisoF002.Audit.CheckerSelfTest

/-!
# Replay closure of every required F002 audit driver

This audit-only bundle lets official leanchecker --fresh replay all six
required audit drivers and their complete imported declarations in one
empty kernel environment. The new mathematical root is replayed separately.
The historical alias is a deliberately rejected negative-control fixture;
this bundle must never enter the mathematical root's import closure.
Command elaborators are also reexecuted individually, not inferred from
cached imports or from kernel replay.
-/
