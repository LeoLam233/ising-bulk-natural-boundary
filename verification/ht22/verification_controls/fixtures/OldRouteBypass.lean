import IsingBulk.HT22.Physical.GermBridge
import IsingBulk.HT.Final.FullNaturalBoundary

/-! EXPECTED KERNEL ACCEPTANCE, EXPECTED ROUTE-POLICY REJECTION.
This theorem is mathematically true. It is intentionally proved by the old HT
terminal endpoint, and therefore is NOT an admissible independent F001 proof.
No source importer or compilation-only test can detect that contract defect. -/
namespace AuditSentinel
open Set IsingBulk.HT22.Physical

theorem oldRouteBypass : ∀ z : ℂ, ‖z‖=1 →
    ¬IsingBulk.HT.Final.HasInteriorExtension interiorBulk z := by
  intro z hz he
  apply IsingBulk.HT.Final.interiorFullBulk_unit_circle_no_extension z hz
  obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq hs).trans (interiorBulk_eqOn_existing hs.2.2)
end AuditSentinel
