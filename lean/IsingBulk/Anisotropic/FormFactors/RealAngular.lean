import IsingBulk.HT.Contour.PhysicalAngular

/-! Literal anisotropic real-temperature coefficients, ANISO (1.6),(1.13).
The two independent real parameters are B=T/S and C=A/S, not the coupling ratio.
The coefficient's index is the actual particle number (lattice) or one less
than that number (constrained angular). No convergence assertion is built into
a definition, and no complex-temperature assertion is an external input. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour
open scoped BigOperators

def gamma (B C q : ℝ) : ℝ := Real.arcosh (C-B*Real.cos q)
def root (B C q : ℝ) : ℝ := Real.exp (-gamma B C q)
def rootProduct {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) : ℝ := ∏ i, root B C (q i)
def pairProduct {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (Real.sin ((q i-q j)/2) / Real.sinh ((gamma B C (q i)+gamma B C (q j))/2))^2
/-- The N²/2 exponent is retained as a real exponent, also for odd N. -/
def anisotropyPower (N : ℕ) (B : ℝ) : ℝ := B ^ ((N:ℝ)^2/2)
def angularWeight {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) : ℝ :=
  anisotropyPower N B * (∏ i, (Real.sinh (gamma B C (q i)))⁻¹) * pairProduct B C q

def latticeCoefficient (N : ℕ) (B C : ℝ) (v : ℤ × ℤ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^N *
    multiAngleIntegral N (fun q =>
      ((angularWeight B C q * (rootProduct B C q)^v.1.natAbs:ℝ):ℂ) *
        Complex.exp (Complex.I*(v.2:ℂ)*(∑ i, (q i:ℂ))))

def angularCoefficient (n : ℕ) (B C : ℝ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun q =>
      let psi := physicalDependentAngles n q
      ((angularWeight B C psi * ((1+rootProduct B C psi)/(1-rootProduct B C psi)):ℝ):ℂ))

theorem dispersion_gt_one {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    1 < C-B*Real.cos q := by
  have h := mul_le_mul_of_nonneg_left (Real.cos_le_one q) hB
  linarith

theorem gamma_pos {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    0 < gamma B C q := Real.arcosh_pos (dispersion_gt_one hB hgap q)

theorem gamma_cosh {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    Real.cosh (gamma B C q) = C-B*Real.cos q :=
  Real.cosh_arcosh (dispersion_gt_one hB hgap q).le

theorem root_bounds {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    0 < root B C q ∧ root B C q < 1 := by
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos (gamma_pos hB hgap q))⟩

@[simp] theorem gamma_isotropic (t q : ℝ) : gamma 1 (t+t⁻¹) q = physicalGamma t q := by
  simp [gamma, physicalGamma]
@[simp] theorem root_isotropic (t q : ℝ) : root 1 (t+t⁻¹) q = physicalRoot t q := by
  simp [root, physicalRoot]
@[simp] theorem anisotropyPower_one (N : ℕ) : anisotropyPower N 1 = 1 := by
  simp [anisotropyPower]
@[simp] theorem angularWeight_isotropic {N : ℕ} (t : ℝ) (q : Fin N → ℝ) :
    angularWeight 1 (t+t⁻¹) q = physicalAngularWeight t q := by
  simp [angularWeight, physicalAngularWeight, pairProduct, physicalPairProduct]
@[simp] theorem rootProduct_isotropic {N : ℕ} (t : ℝ) (q : Fin N → ℝ) :
    rootProduct 1 (t+t⁻¹) q = physicalZ t q := by
  simp [rootProduct, physicalZ]

/-- Exact matching of every site, including the origin and either axis. -/
theorem latticeCoefficient_isotropic (N : ℕ) (t : ℝ) (v : ℤ × ℤ) :
    latticeCoefficient N 1 (t+t⁻¹) v = physicalFullLatticeCoefficient N t v := by
  simp [latticeCoefficient, physicalFullLatticeCoefficient, physicalLatticeCoefficient]
/-- Exact matching at every particle number; no parity or truncation shortcut. -/
theorem angularCoefficient_isotropic (n : ℕ) (t : ℝ) :
    angularCoefficient n 1 (t+t⁻¹) = physicalAngularCoefficient n t := by
  simp [angularCoefficient, physicalAngularCoefficient]

/-- Reflection of the transfer displacement only, not an illicit axis swap. -/
theorem latticeCoefficient_reflect_first (N : ℕ) (B C : ℝ) (m l : ℤ) :
    latticeCoefficient N B C (-m,l) = latticeCoefficient N B C (m,l) := by
  simp [latticeCoefficient]
end
end IsingBulk.Anisotropic.FormFactors
