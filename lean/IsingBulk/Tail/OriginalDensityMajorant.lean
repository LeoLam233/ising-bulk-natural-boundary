import IsingBulk.Tail.ExteriorReducedMajorant
import IsingBulk.Tail.OriginalPfaffianIntegral
import IsingBulk.First.SourceAngularPeriodicity

/-! The true global denominator and inverse-product numerator are kept,
while the original residue weights are retained for L2 matching integration. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped BigOperators Topology

theorem reducedDensity_weighted_bound {N : ℕ} (hN : 2 ≤ N) {r A : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A)
    (z y : Fin N → ℂ) (hz : ∀ i, ‖z i‖ ≤ r) (hy : ∀ i, ‖y i‖=r)
    (hzi : ∀ i, ‖(z i)⁻¹‖ ≤ A) (hpairz : ‖First.pairProduct z‖ ≤ 1) :
    ‖reducedDensity z y‖ ≤
      (2*(max A r⁻¹)^N/(1-r^2)^2)*
        ((∏ i, ‖residueFactor (z i)‖)*‖First.pairProduct y‖) := by
  have hg : 0 < 1-r^2 := by nlinarith
  have hnum := inverse_global_numerator_norm_le hA (inv_nonneg.mpr hr.le) hzi
    (fun i => show ‖(y i)⁻¹‖ ≤ r⁻¹ by rw [norm_inv,hy i])
  have hdz := coordinateProduct_gap hN hr.le hr1 hz
  have hdy := coordinateProduct_gap hN hr.le hr1 (fun i => (hy i).le)
  have hden : (1-r^2)^2 ≤ ‖(1-coordinateProduct z)*(1-coordinateProduct y)‖ := by
    rw [norm_mul,pow_two]
    exact mul_le_mul hdz hdy hg.le (norm_nonneg _)
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct z)*(1-coordinateProduct y))‖ ≤ 2*(max A r⁻¹)^N/(1-r^2)^2 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hg) hden
  simp only [reducedDensity,norm_mul,norm_prod]
  calc
    _ ≤ (2*(max A r⁻¹)^N/(1-r^2)^2)*1*‖First.pairProduct y‖*
        (∏ i, ‖residueFactor (z i)‖) := by gcongr
    _ = _ := by ring

theorem circle_pairProduct_eq_labelPfaffian (n : ℕ) {r : ℝ} (hr1 : r < 1)
    (y : Fin (2*n) → ℂ) (hy : ∀ i, ‖y i‖≤r) :
    First.pairProduct y = labelPfaffian (fun a b => pairKernel (y a) (y b)) n
      (List.finRange (2*n)) := by
  rw [labelPfaffian_source,← List.ofFn_eq_map,pairProduct_eq_schur]
  exact (Schur.schur_compact_exterior n y hr1 hy).symm

theorem norm_angleProductJacobian {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (theta : Fin N → ℝ) :
    ‖angleProductJacobian r theta‖ = (r/(2*Real.pi))^N := by
  simp only [angleProductJacobian,norm_prod,angleJacobian,norm_div,
    anglePoint_norm hr,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  simp [div_pow]


theorem angleBox_restrict_pi (N : ℕ) :
    volume.restrict (angleBox N) =
      Measure.pi (fun _ : Fin N => volume.restrict (Icc (0:ℝ) (2*Real.pi))) := by
  rw [angleBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]

theorem source_angular_integral_identity (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    doubleFormFactor N r s = (N.factorial:ℂ)⁻¹ *
      ∫ x in angleBox N, sourceReducedAngularDensity r s x := by
  have ha := globalRoot_admissible hr hr1 hm
  rw [residue_reduction N hN r hr s (globalRoot s)
    (fun y hy => ha.toTuple N y hy)]
  rw [reducedFormFactor,multiCircleIntegral_eq_angle]
  change (N.factorial:ℂ)⁻¹ * multiAngleIntegral N (sourceReducedAngularDensity r s) = _
  rw [multiAngleIntegral_eq_box N _ (sourceReducedAngularDensity_continuous N hN hr hr1 hm)]


end
end IsingBulk.Tail
