import IsingBulk.Joint.FormFactors.NormalizedRestriction
import IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbs
import IsingBulk.Anisotropic.PhysicalField.SymmetryDerivative

/-! Real-only physical data for one common two-coupling realization.

The same correlation functions occur at every positive ratio, rather than an
unrelated choice of functions for each ray. The sole imported spin identities
are the literal real-temperature site form factors of Bugrij--Lisovyy
0708.3643 (35)--(39), proved at finite circumference by Iorgov--Lisovyy
1012.2856, Theorem 6.1 and Remark 6.2. Raoufi 1710.07608, Theorem 1 with
(C1)--(C4), identifies translation-invariant cylinder limits: translations,
not the full square-lattice rotation group, preserve unequal couplings.

The field conditions are the baseline real Gibbs marginals, local tilts,
monotonicity, pinned-volume comparison, and thermodynamic limits. Their
concavity input is Camia--Garban--Newman 1205.6612v4, Theorem 1.5 and
Corollary 1.6 for arbitrary nonnegative interactions and site fields.
No summability, field derivative, joint holomorphy or boundary conclusion is
part of this interface. In particular it does not assume analytic dependence
of the real family on either coupling. -/
namespace IsingBulk.Joint.PhysicalField
noncomputable section
open IsingBulk.Anisotropic.FormFactors

abbrev RealCoupling := ℝ × ℝ
abbrev CorrelationFamily := RealCoupling → LatticeSite → ℝ
/-- Energy couplings Jx,Jy, inverse temperature, and energy field h. -/
abbrev MagnetizationFamily := ℝ → ℝ → ℝ → ℝ → ℝ

def realSlice (lam x : ℝ) : RealCoupling := (x,lam*x)
def complexify (K : RealCoupling) : Coupling := ((K.1:ℂ),(K.2:ℂ))
def realProduct (K : RealCoupling) : ℝ := Real.sinh K.1*Real.sinh K.2
def magnetizationSq (K : RealCoupling) : ℝ := (1-(realProduct K)⁻¹^2)^(1/4:ℝ)
def highCovarianceSum (corr : CorrelationFamily) (K : RealCoupling) : ℝ := ∑' v, corr K v
def lowCovarianceSum (corr : CorrelationFamily) (K : RealCoupling) : ℝ :=
  ∑' v, (corr K v-magnetizationSq K)

/-- Uniform over all positive finite anisotropies, with a common real family. -/
def PublishedRealSpinFamily (corrH corrL : CorrelationFamily) : Prop :=
  ∀ lam : ℝ, 0 < lam → PublishedRealSpinFormFactors lam
    (fun x => corrH (realSlice lam x)) (fun x => corrL (realSlice lam x))

/-- Real field representation for the same correlations and the same physical
energy-coupling magnetizations. The inverse temperature is only on real rays. -/
def PublishedRealGibbsFamily (corrH corrL : CorrelationFamily)
    (mH mL : MagnetizationFamily) : Prop :=
  ∀ J lam : ℝ, 0 < J → 0 < lam →
    Anisotropic.PhysicalField.PublishedRealGibbsFields J lam
      (fun x => corrH (realSlice lam x)) (fun x => corrL (realSlice lam x))
      (fun x => mH J (lam*J) (x/(2*J))) (fun x => mL J (lam*J) (x/(2*J)))

@[simp] theorem complexify_realSlice (lam x : ℝ) :
    complexify (realSlice lam x) = ratioSlice lam (x:ℂ) := by
  simp [complexify,realSlice,ratioSlice]

@[simp] theorem realProduct_realSlice (lam x : ℝ) :
    realProduct (realSlice lam x) = Anisotropic.FormFactors.realProduct lam x := rfl

@[simp] theorem magnetizationSq_realSlice (lam x : ℝ) :
    magnetizationSq (realSlice lam x) = realMagnetizationSq lam x := rfl

theorem realSlice_ratio {x : ℝ} (hx : x ≠ 0) (y : ℝ) : realSlice (y/x) x = (x,y) := by
  simp [realSlice,div_mul_cancel₀ y hx]

end
end IsingBulk.Joint.PhysicalField
