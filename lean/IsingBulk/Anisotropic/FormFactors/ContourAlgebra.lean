import IsingBulk.Anisotropic.FormFactors.RealAngular
import IsingBulk.HT.Contour.PhysicalAngularPairs

/-! Exact scalar identities for the anisotropic contour bridge.
These are not a contour-deformation theorem. In particular no equality of
infinite lattice sums is asserted before absolute summability is established. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour

def dispersionPolynomial (S T A x y : ℂ) : ℂ :=
  A-S/2*(x+x⁻¹)-T/2*(y+y⁻¹)

theorem dispersion_axis_exchange (S T A x y : ℂ) :
    dispersionPolynomial S T A x y = dispersionPolynomial T S A y x := by
  unfold dispersionPolynomial
  ring

/-- Equation (1.12), with all four denominators explicitly protected. -/
theorem full_site_multiplier (X Y : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hX1 : 1-X ≠ 0) (hY1 : 1-Y ≠ 0) :
    (1+X)*(1+Y)/(X*Y*(1-X)*(1-Y)) =
      1/(X*Y)+2*(X⁻¹+Y⁻¹)/((1-X)*(1-Y)) := by
  field_simp
  ring

theorem root_trace {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    root B C q + (root B C q)⁻¹ = 2*(C-B*Real.cos q) := by
  have he := Real.cosh_eq (gamma B C q)
  rw [gamma_cosh hB hgap, Real.exp_neg] at he
  unfold root
  rw [Real.exp_neg, inv_inv]
  linarith

/-- The anisotropic one-body identity, before multiplying sqrt(B)/S. -/
theorem residue_factor {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (q : ℝ) :
    residueFactor (root B C q:ℂ) = (root B C q / Real.sinh (gamma B C q):ℝ) := by
  have hpos := root_bounds hB hgap q
  have hE : Real.exp (gamma B C q) ≠ 0 := (Real.exp_pos _).ne'
  have hg : Real.sinh (gamma B C q) ≠ 0 := (Real.sinh_pos_iff.mpr (gamma_pos hB hgap q)).ne'
  have hgap' : 1-(root B C q)^2 ≠ 0 := by nlinarith [hpos.1,hpos.2]
  have hid : 2*(root B C q)*Real.sinh (gamma B C q) = 1-(root B C q)^2 := by
    rw [Real.sinh_eq, root, Real.exp_neg]
    field_simp [hE]
  have hreal : 2*(root B C q)^2/(1-(root B C q)^2) = root B C q/Real.sinh (gamma B C q) := by
    apply (div_eq_div_iff hgap' hg).mpr
    nlinarith [hid]
  unfold residueFactor
  exact_mod_cast hreal

/-- The collision-regular pair identity remains valid at reciprocal angles. -/
theorem canceled_pair {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (a b : ℝ) :
    canceledPair (limitingAngle a) (limitingAngle b)
      (root B C a:ℂ) (root B C b:ℂ) =
      ((Real.sin ((a-b)/2) / Real.sinh ((gamma B C a+gamma B C b)/2))^2:ℝ) := by
  have hratio := physical_pair_root_ratio (gamma_pos hB hgap a) (gamma_pos hB hgap b)
  have hratioC : ((root B C a:ℂ)*(root B C b:ℂ))/(1-(root B C a:ℂ)*(root B C b:ℂ))^2 =
      ((4*Real.sinh ((gamma B C a+gamma B C b)/2)^2)⁻¹:ℝ) := by
    exact_mod_cast hratio
  calc
    _ = (-(limitingAngle a-limitingAngle b)^2/(limitingAngle a*limitingAngle b))*
        (((root B C a:ℂ)*(root B C b:ℂ))/(1-(root B C a:ℂ)*(root B C b:ℂ))^2) := by
      unfold canceledPair
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by
      rw [physical_unit_pair_numerator,hratioC]
      push_cast
      simp only [div_eq_mul_inv,mul_inv_rev]
      norm_num
      ring

/-- The explicit B in (1.11) is a pair factor, not a constant full-sum prefactor. -/
theorem scaled_canceled_pair {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C-B) (a b : ℝ) :
    (B:ℂ)*canceledPair (limitingAngle a) (limitingAngle b)
      (root B C a:ℂ) (root B C b:ℂ) =
      (B*(Real.sin ((a-b)/2) / Real.sinh ((gamma B C a+gamma B C b)/2))^2:ℝ) := by
  rw [canceled_pair hB hgap]
  push_cast
  rfl

/-- Correct anisotropic power accounting before any limit or particle sum. -/
theorem anisotropy_exponent (N : ℕ) :
    (N:ℝ)/2 + (N:ℝ)*((N:ℝ)-1)/2 = (N:ℝ)^2/2 := by ring

theorem anisotropy_power_factorization (N : ℕ) {B : ℝ} (hB : 0 < B) :
    B^((N:ℝ)/2) * B^((N:ℝ)*((N:ℝ)-1)/2) = anisotropyPower N B := by
  rw [← Real.rpow_add hB, anisotropy_exponent]
  rfl
end
end IsingBulk.Anisotropic.FormFactors
