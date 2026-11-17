import IsingBulk.Anisotropic.Final.CompleteTarget

/-!
Automatically extracted from the immutable original theorem's signature.
Source: IsingBulk/Anisotropic/Final/FullTheorem.lean
Source SHA-256: 51a30dcb9dfe9e83c8e52adde0b42fc1f5d6124075ea02e2df0ea12278b5bd80
Only the declaration header before `:=` is used.  No historical proof or
completed boundary theorem is imported.  This defines an unproved proposition.
-/

namespace IsingBulk.AnisoF002.Audit
open IsingBulk.Anisotropic
open IsingBulk.Anisotropic.FormFactors IsingBulk.Anisotropic.PhysicalField

-- Preserve the literal original binder names; this is a proposition definition.
set_option linter.unusedVariables false in
def FrozenTerminalStatement : Prop :=
  ∀ {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL),
    FullUniformFieldConclusion J lam corrH corrL mH mL

end IsingBulk.AnisoF002.Audit
