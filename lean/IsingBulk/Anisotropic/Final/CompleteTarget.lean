import IsingBulk.Anisotropic.Final.FieldDerivative
import IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbs
import IsingBulk.Anisotropic.PhysicalField.SymmetryDerivative

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors PhysicalField Set

/-- The literal field convention: bilateral HT derivative at zero, right LT
plus-phase derivative, zero HT mean and the specified positive LT mean. -/
structure RealUniformFieldIdentification (J lam : ℝ)
    (corrH corrL : ℝ → LatticeSite → ℝ) (mH mL : ℝ → ℝ → ℝ) : Prop where
  high_derivative : ∀ x, 0<x → realProduct lam x<1 →
    HasDerivAt (mH x) (highEnergyFieldResponse J corrH x) 0
  high_zero : ∀ x, 0<x → realProduct lam x<1 → mH x 0=0
  low_derivative : ∀ x, 0<x → 1<realProduct lam x →
    HasDerivWithinAt (mL x) (lowEnergyFieldResponse J lam corrL x) (Ioi 0) 0
  low_zero_square : ∀ x, 0<x → 1<realProduct lam x → (mL x 0)^2=realMagnetizationSq lam x
  low_plus_positive : ∀ x, 0<x → 1<realProduct lam x → 0<mL x 0

/-- Complete endpoint contract, including the literal thermodynamic field
response beyond the covariance-only normalization in FullPhysicalConclusion. -/
def FullUniformFieldConclusion (J lam : ℝ)
    (corrH corrL : ℝ → LatticeSite → ℝ) (mH mL : ℝ → ℝ → ℝ) : Prop :=
  FullPhysicalConclusion J lam corrH corrL ∧
    RealUniformFieldIdentification J lam corrH corrL mH mL

theorem realUniformFieldIdentification_of_published {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL) :
    RealUniformFieldIdentification J lam corrH corrL mH mL := by
  have hr := realFieldDerivativeIdentification_of_gibbs hJ hlam hphys
    (fun x hx hp => Classical.choice (hG.high x hx hp))
    (fun x hx hp => Classical.choice (hG.low x hx hp))
  refine ⟨?_,?_,hr.low,hG.low_zero_square,hG.low_plus_positive⟩
  · intro x hx hp
    exact hasDerivAt_of_odd_right_derivative (hG.high_spin_flip x hx hp) (hr.high x hx hp)
  · intro x hx hp
    have hh := hG.high_spin_flip x hx hp 0
    simp only [neg_zero] at hh
    linarith

/-- Assembly only: the full analytic/natural-boundary conclusion must be
supplied by the internal ANISO endpoint proof, not by a physical interface. -/
theorem fullUniformFieldConclusion_of_analytic {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL)
    (hA : FullAnalyticConclusion J lam) :
    FullUniformFieldConclusion J lam corrH corrL mH mL :=
  ⟨⟨hA,realPhysicalIdentification_of_published J hlam hphys⟩,
    realUniformFieldIdentification_of_published hJ hlam hphys hG⟩

end
end IsingBulk.Anisotropic
