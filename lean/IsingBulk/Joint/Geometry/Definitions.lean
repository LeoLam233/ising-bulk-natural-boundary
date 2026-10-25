import IsingBulk.Anisotropic.Geometry.Definitions

/-! # Independent complex coupling geometry
The coordinates of `Coupling` are doubled couplings `(z,w)=(2Kx,2Ky)`.
All sets are literal JOINT definitions, independent of susceptibility or continuation.
-/
namespace IsingBulk.Joint
noncomputable section

abbrev Coupling := ℂ × ℂ

def S (K : Coupling) : ℂ := Complex.sinh K.1
def T (K : Coupling) : ℂ := Complex.sinh K.2
def A (K : Coupling) : ℂ := Complex.cosh K.1 * Complex.cosh K.2
def p (K : Coupling) : ℂ := S K * T K

/-- The unsquared independently defined spectral condition, JOINT (2.1). -/
def spectralSet : Set Coupling :=
  {K | ∃ a ∈ Set.Icc (-1 : ℝ) 1, ∃ b ∈ Set.Icc (-1 : ℝ) 1,
    A K = S K * (a : ℂ) + T K * (b : ℂ)}

def F1 (K : Coupling) : ℝ :=
  Real.cosh K.2.re ^ 2 * Real.cos K.1.im ^ 2 -
    Real.cosh K.1.re ^ 2 * Real.sinh K.2.re ^ 2

def F2 (K : Coupling) : ℝ :=
  Real.cosh K.1.re ^ 2 * Real.cos K.2.im ^ 2 -
    Real.sinh K.1.re ^ 2 * Real.cosh K.2.re ^ 2

/-- The literal high-temperature domain, JOINT (1.1)/(2.10). -/
def highDomain : Set Coupling :=
  {K | |K.1.im| < Real.pi / 2 ∧ |K.2.im| < Real.pi / 2 ∧
    Real.cosh K.1.re * Real.tanh |K.2.re| < Real.cos K.1.im ∧
    Real.cosh K.2.re * Real.tanh |K.1.re| < Real.cos K.2.im}

/-- The literal low-temperature plus domain, JOINT (1.2)/(2.11). -/
def lowDomain : Set Coupling :=
  {K | 0 < K.1.re ∧ 0 < K.2.re ∧
    |Real.cos K.1.im| < Real.cosh K.1.re * Real.tanh K.2.re ∧
    |Real.cos K.2.im| < Real.cosh K.2.re * Real.tanh K.1.re}

/-- Transfer coordinates, JOINT Proposition 2.10. -/
def transferC (K : Coupling) : ℂ := A K / S K
def transferB (K : Coupling) : ℂ := T K / S K
def transferChart (K : Coupling) : ℂ × ℂ := (transferC K, transferB K)

/-- Fixed-ratio line in doubled coordinates. -/
def ratioSlice (lam : ℝ) (z : ℂ) : Coupling := (z, (lam : ℂ) * z)

/-- This equation remains meaningful on the axis `S = 0`. -/
def rootPolynomial (K : Coupling) (q rho : ℂ) : ℂ :=
  S K * rho ^ 2 - 2 * (A K - T K * Complex.cos q) * rho + S K

/-- Regular spectral face, JOINT Definition 2.8. -/
def IsRegularJointEdge (K : Coupling) : Prop :=
  K ∈ (frontier highDomain ∪ frontier lowDomain) ∧
  S K ≠ 0 ∧ T K ≠ 0 ∧ (star (S K) * T K).im ≠ 0 ∧ p K ^ 2 ≠ 1 ∧
  ∃ a ∈ Set.Icc (-1 : ℝ) 1, ∃ b ∈ Set.Icc (-1 : ℝ) 1,
    A K = S K * (a : ℂ) + T K * (b : ℂ) ∧
    ((a = -1 ∨ a = 1) ∧ b ∈ Set.Ioo (-1 : ℝ) 1 ∨
     a ∈ Set.Ioo (-1 : ℝ) 1 ∧ (b = -1 ∨ b = 1))

end
end IsingBulk.Joint
