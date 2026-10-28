import IsingBulk.HT22.Geometry.InverseJets
import IsingBulk.HT22.Algebra.OddBordered
import IsingBulk.HT22.Transport.SourceField
import IsingBulk.Preferred22.Transport

/-! # The actual F001 fixed-v scalar transport

The inverse is unshifted, the right field uses mixed complex covariance,
and the kernel is the odd constant-bordered matrix. Smooth weights are
functions of the original real angles throughout. Definitions here do not
assert estimates or the integral transport identity.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators

/-- Fixed-v derivatives, not the derivatives at fixed moving LT coordinate q. -/
abbrev inverseV := Geometry.inverseV

abbrev inverseT := Geometry.inverseT

def sourceCoordinate {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  sumCoordinate t (deformedAngles τ p m θ i)

/-- The sole right residual field is the manuscript's mixed covariance. -/
abbrev residualField {N : ℕ} (t : ℂ) (v : Fin N → ℂ) : Fin N → ℂ :=
  sourceResidual t v

def angularField {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  let v := sourceCoordinate τ p m t θ
  preferredAngularRepresentative (preferredContourMatrix τ p m θ)
    (fun i => inverseT t (v i)) (fun i => inverseV t (v i)) (residualField t v)

/-- The commuting-coordinate candidate frame has no inverse inverseV pole. -/
def coordinateFrame {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Fin N)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i, (preferredContourMatrix τ p m θ)⁻¹ i a *
    inverseV t (sourceCoordinate τ p m t θ a) *
      deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i)

def parameterFrame {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  deriv (fun s : ℂ => F s θ) t +
    ∑ i, ((preferredContourMatrix τ p m θ)⁻¹.mulVec
      (fun a => inverseT t (sourceCoordinate τ p m t θ a))) i *
        deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i)

def regularDivergence {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ a, coordinateFrame τ p m a
    (fun s x => residualField s (sourceCoordinate τ p m s x) a) t θ

def regularTransportStep {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  parameterFrame τ p m F t θ +
    (∑ a, residualField t (sourceCoordinate τ p m t θ) a *
      coordinateFrame τ p m a F t θ) + regularDivergence τ p m t θ * F t θ

/-- The exact scalar generator with the original real angular derivatives. -/
theorem regularTransportStep_eq {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ) :
    regularTransportStep τ p m F t θ = deriv (fun s => F s θ) t -
      (∑ i, angularField τ p m t θ i *
        deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i)) +
      regularDivergence τ p m t θ * F t θ := by
  let M := preferredContourMatrix τ p m θ
  let u := fun a => inverseT t (sourceCoordinate τ p m t θ a)
  let v := fun a => inverseV t (sourceCoordinate τ p m t θ a)
  let B := residualField t (sourceCoordinate τ p m t θ)
  let g := fun i => deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i)
  have hb : (∑ a, B a*(∑ i, M⁻¹ i a*v a*g i)) =
      ∑ i, (M⁻¹.mulVec (fun a => v a*B a)) i*g i := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold regularTransportStep
  congr 1
  change deriv (fun s => F s θ) t+(∑ i, (M⁻¹.mulVec u) i*g i)+
    (∑ a, B a*(∑ i, M⁻¹ i a*v a*g i)) =
      deriv (fun s => F s θ) t-(∑ i, -(M⁻¹.mulVec (fun a => u a+v a*B a)) i*g i)
  rw [hb]
  change deriv (fun s => F s θ) t+(∑ i, (M⁻¹.mulVec u) i*g i)+
    (∑ i, (M⁻¹.mulVec (fun a => v a*B a)) i*g i) =
      deriv (fun s => F s θ) t-(∑ i, -(M⁻¹.mulVec (u+(fun a => v a*B a))) i*g i)
  simp only [Matrix.mulVec_add,Pi.add_apply,neg_mul,Finset.sum_neg_distrib,sub_neg_eq_add,
    add_mul,Finset.sum_add_distrib]
  ring

/-- The ordinary block is the rational L, not the LT half-angle kernel. -/
def regularOrdinaryKernel {N : ℕ} (t : ℂ) (v : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => Algebra.ordinaryEntry
    (Complex.exp (Complex.I*regularInverse t (v i)))
    (Complex.exp (Complex.I*regularInverse t (v j)))
    (Complex.exp (-Complex.I*regularPhase t (v i)))
    (Complex.exp (-Complex.I*regularPhase t (v j)))

def regularBorderedKernel {N : ℕ} (t : ℂ) (v : Fin N → ℂ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  Algebra.constantBorderFirst (fun i => Complex.exp (Complex.I*regularInverse t (v i)))
    (fun i => Complex.exp (-Complex.I*regularPhase t (v i)))

def sourceBorderedKernel {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  regularBorderedKernel t (sourceCoordinate τ p m t θ)

def regularOneBody (t v : ℂ) : ℂ := inverseV t v/Complex.sinh (Complex.I*regularPhase t v)

def regularProductPhase {N : ℕ} (t : ℂ) (v : Fin N → ℂ) : ℂ :=
  Complex.exp (-Complex.I*∑ i, regularPhase t (v i))

/-- Exact normalization, including N! and only N−1 Haar angle factors. -/
def regularSeedCoefficient {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight .right η p m r θ:ℂ) *
    (∏ i, regularOneBody t (sourceCoordinate τ p m t θ i)) /
      ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

def regularSeed {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  regularSeedCoefficient τ η p m r t θ * (sourceBorderedKernel τ p m t θ).det

def regularTransportedScalar {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ) :
    ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => regularSeed τ η p m r
  | j+1 => regularTransportStep τ p m (regularTransportedScalar τ η p m r j)

/-- The scalar includes the full ambient Jacobian; identification with the
actual source derivative recurrence is a separate Piola theorem. -/
def coordinateJacobian {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredContourMatrix τ p m θ).det *
    ∏ i, (inverseV t (sourceCoordinate τ p m t θ i))⁻¹

def reconstructedDensity {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (j : ℕ) (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let Z := regularProductPhase t (sourceCoordinate τ p m t θ)
  coordinateJacobian τ p m t θ * ((1+σ*Z)/(1-σ*Z)) *
    regularTransportedScalar τ η p m r j t θ

/-- The full original density, before extraction of any regular factors. -/
def physicalSeed {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let w := deformedAngles τ p m θ
  let z := fun i => physicalRoot (temperatureTrace t-Complex.cos (w i))
  let y := fun i => Complex.exp (Complex.I*w i)
  let Z := ∏ i, z i
  (preferredCellWeight .right η p m r θ:ℂ)*(preferredContourMatrix τ p m θ).det *
    ((1+σ*Z)/(1-σ*Z))*(Algebra.constantBorderFirst y z).det *
    (∏ i, oneBody (z i))/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

def transportedDensity {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ) :
    ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => physicalSeed σ τ η p m r
  | j+1 => preferredTransportStep (angularField τ p m) (transportedDensity σ τ η p m r j)

end
end IsingBulk.HT22.Tail
