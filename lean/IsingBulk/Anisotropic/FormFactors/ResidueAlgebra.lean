import IsingBulk.Anisotropic.FormFactors.FullLatticeContour
import IsingBulk.First.ResidueIntegral

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First
open scoped BigOperators

/-- The unsquared dispersion relation determines the actual enclosed root. -/
def RootEquation (lam : ℝ) (z y u : ℂ) : Prop :=
  spectralA lam z - spectralT lam z / 2 * (y+y⁻¹) = spectralS z / 2 * (u+u⁻¹)

theorem dispersion_factorization {lam : ℝ} {z x y u : ℂ}
    (hx : x ≠ 0) (hu : u ≠ 0) (he : RootEquation lam z y u) :
    sliceDispersion lam z x y = spectralS z * (x-u)*(1-x*u)/(2*x*u) := by
  unfold sliceDispersion dispersionPolynomial
  have hr : spectralA lam z - spectralT lam z / 2*(y+y⁻¹) =
      spectralS z / 2*(u+u⁻¹) := he
  calc
    _ = spectralS z / 2*(u+u⁻¹) - spectralS z/2*(x+x⁻¹) := by rw [← hr]; ring
    _ = _ := by field_simp; ring

def latticeClearedNumerator {N : ℕ} (_lam : ℝ) (z : ℂ)
    (y u x : Fin N → ℂ) (v : ℤ × ℤ) : ℂ :=
  IsingBulk.First.pairProduct x * IsingBulk.First.pairProduct y *
    (∏ i, 2*u i/(spectralS z*y i*(1-x i*u i))) *
    (coordinateProduct x)^v.1.natAbs * (coordinateProduct y)^v.2.natAbs

theorem latticeDensity_eq_cauchy {N : ℕ} {lam : ℝ} {z : ℂ}
    {x y u : Fin N → ℂ} (hx : ∀ i,x i ≠ 0)
    (hu : ∀ i,u i ≠ 0)
    (he : ∀ i,RootEquation lam z (y i) (u i)) (v : ℤ × ℤ) :
    onsiteDensity lam z x y * (coordinateProduct x)^v.1.natAbs *
      (coordinateProduct y)^v.2.natAbs =
    (∏ i,(x i-u i)⁻¹)*latticeClearedNumerator lam z y u x v := by
  have hd (i) : (x i*y i)⁻¹*(sliceDispersion lam z (x i) (y i))⁻¹ =
      (x i-u i)⁻¹*(2*u i/(spectralS z*y i*(1-x i*u i))) := by
    rw [dispersion_factorization (hx i) (hu i) (he i)]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    field_simp [hx i]
  have hp : (coordinateProduct x*coordinateProduct y)⁻¹ *
      (∏ i,(sliceDispersion lam z (x i) (y i))⁻¹) =
      (∏ i,(x i-u i)⁻¹)*(∏ i,2*u i/(spectralS z*y i*(1-x i*u i))) := by
    simp only [coordinateProduct,← Finset.prod_mul_distrib,← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i _ => hd i)
  unfold onsiteDensity commonDensity latticeClearedNumerator
  calc
    _ = IsingBulk.First.pairProduct x * IsingBulk.First.pairProduct y *
      ((coordinateProduct x*coordinateProduct y)⁻¹*(∏ i,(sliceDispersion lam z (x i) (y i))⁻¹))*
      (coordinateProduct x)^v.1.natAbs*(coordinateProduct y)^v.2.natAbs := by ring
    _ = _ := by rw [hp]; ring
end
end IsingBulk.Anisotropic.FormFactors
