import IsingBulk.Anisotropic.FormFactors.UnitDensity

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

theorem temperatureScale_pair_power (N : ℕ) {B S : ℝ} (hB : 0 < B) (hS : S ≠ 0) :
    (S*Real.sqrt B)^N*B^(N.choose 2)*(S^N)⁻¹ = anisotropyPower N B := by
  have hsqrt : (Real.sqrt B)^N = B^((N:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hB.le]
    congr 1
    ring
  calc
    _ = (Real.sqrt B)^N*B^(N.choose 2) := by
      rw [mul_pow]
      field_simp
    _ = _ := by rw [hsqrt]; exact anisotropy_choose_power N hB

theorem scaled_canceledLatticeDensity_unit {N : ℕ} {B C S : ℝ} (hB : 0 < B)
    (hgap : 1 < C-B) (hS : S ≠ 0) (q : Fin N → ℝ) (v : ℤ × ℤ) :
    ((S*Real.sqrt B)^N:ℝ)*coordinateProduct (fun i => limitingAngle (q i))*
      canceledLatticeDensity B C (S:ℂ) (fun i => limitingAngle (q i)) v =
    (angularWeight B C q*(rootProduct B C q)^v.1.natAbs:ℝ)*
      Complex.exp (Complex.I*(v.2.natAbs:ℂ)*(∑ i,(q i:ℂ))) := by
  rw [mul_assoc, canceledLatticeDensity_unit hB.le hgap]
  have hscale := temperatureScale_pair_power N hB hS
  have hscaleC : (((S*Real.sqrt B)^N:ℝ):ℂ)*(B:ℂ)^(N.choose 2)*((S:ℂ)^N)⁻¹ =
      (anisotropyPower N B:ℂ) := by exact_mod_cast hscale
  unfold angularWeight
  push_cast at hscaleC ⊢
  linear_combination (∏ i,(Complex.sinh (gamma B C (q i):ℂ))⁻¹)*(pairProduct B C q:ℂ)*
    (rootProduct B C q:ℂ)^v.1.natAbs*
    Complex.exp (Complex.I*(v.2.natAbs:ℂ)*(∑ i,(q i:ℂ)))*hscaleC

theorem latticeCoefficient_natAbs_eq_unit_contour (N : ℕ) {B C S : ℝ} (hB : 0 < B)
    (hgap : 1 < C-B) (hS : S ≠ 0) (v : ℤ × ℤ) :
    latticeCoefficient N B C (v.1,(v.2.natAbs:ℤ)) =
      ((S*Real.sqrt B)^N:ℝ)*(N.factorial:ℂ)⁻¹ *
        multiCircleIntegral 1 N (fun y => canceledLatticeDensity B C (S:ℂ) y v) := by
  have hpoint (q : Fin N → ℝ) :
      (((S*Real.sqrt B)^N:ℝ):ℂ)*(angleProductJacobian 1 q *
        canceledLatticeDensity B C (S:ℂ) (angleTuple 1 q) v) =
      ((2*(Real.pi:ℂ))⁻¹)^N *
        ((angularWeight B C q*(rootProduct B C q)^v.1.natAbs:ℝ)*
          Complex.exp (Complex.I*(v.2.natAbs:ℂ)*(∑ i,(q i:ℂ)))) := by
    rw [physical_angleProductJacobian,physical_angleTuple_one]
    have hh := scaled_canceledLatticeDensity_unit hB hgap hS q v
    calc
      _ = ((2*(Real.pi:ℂ))⁻¹)^N *
          ((((S*Real.sqrt B)^N:ℝ):ℂ)*coordinateProduct (fun i => limitingAngle (q i))*
            canceledLatticeDensity B C (S:ℂ) (fun i => limitingAngle (q i)) v) := by
        simp only [div_eq_mul_inv,inv_pow]
        ring
      _ = _ := by rw [hh]
  rw [multiCircleIntegral_eq_angle]
  -- Move the constant temperature scale, keeping the factorial outside.
  have he : ((S*Real.sqrt B)^N:ℝ)*(N.factorial:ℂ)⁻¹ *
      multiAngleIntegral N (fun q => angleProductJacobian 1 q *
        canceledLatticeDensity B C (S:ℂ) (angleTuple 1 q) v) =
      (N.factorial:ℂ)⁻¹ * multiAngleIntegral N (fun q =>
        (((S*Real.sqrt B)^N:ℝ):ℂ)*(angleProductJacobian 1 q *
        canceledLatticeDensity B C (S:ℂ) (angleTuple 1 q) v)) := by
    rw [physical_multiAngleIntegral_const_mul]
    ring
  rw [he]
  simp_rw [hpoint]
  rw [physical_multiAngleIntegral_const_mul]
  unfold latticeCoefficient
  simp only [Int.cast_natCast]
  ring
end
end IsingBulk.Anisotropic.FormFactors
