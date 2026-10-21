import IsingBulk.HT.Final.OnsiteResidue
import IsingBulk.HT.Tail.OddExteriorMajorant

/-! A genuine odd onsite residue majorant. It uses the same odd matching
bound as the offsite term, but no artificial global geometric poles. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail
open scoped BigOperators

theorem reducedOnsiteDensity_upper_bound {N : ℕ} {r A P : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (z y : Fin N → ℂ) (hz : ∀ i, ‖z i‖ ≤ r) (hy : ∀ i, ‖y i‖ = r)
    (hzi : ∀ i, ‖(z i)⁻¹‖ ≤ A)
    (hpairz : ‖pairProduct z‖ ≤ 1) (hpairy : ‖pairProduct y‖ ≤ P) :
    ‖reducedOnsiteDensity z y‖ ≤
      (A*r⁻¹)^N * P * (2*r^2/(1-r^2))^N := by
  have hzInv : ‖(coordinateProduct z)⁻¹‖ ≤ A^N := by
    rw [coordinateProduct, ← Finset.prod_inv_distrib, norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, A :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hzi i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hyInv : ‖(coordinateProduct y)⁻¹‖ = (r⁻¹)^N := by
    simp [coordinateProduct, norm_inv, norm_prod, hy]
  have hres : ‖∏ i,residueFactor (z i)‖ ≤ (2*r^2/(1-r^2))^N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, (2*r^2/(1-r^2)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => subdisk_residueFactor_bound hr.le hr1 (hz i))
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [reducedOnsiteDensity, mul_inv_rev, norm_mul]
  rw [hyInv]
  calc
    _ ≤ (r⁻¹)^N*A^N*1*P*(2*r^2/(1-r^2))^N := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem odd_onsite_matching_majorant_identity (n : ℕ) (r H D E : ℝ) :
    ((2*n+1).factorial:ℝ)⁻¹ *
      (r^(2*n+1)*(H^(2*n+1)*
        ((matchingCount (n+1):ℝ)*D^(n+1))*E^(2*n+1))) =
      (r*H*E*D)*(((r*H*E)^2*D/2)^n/(n.factorial:ℝ)) := by
  have hh := odd_matching_majorant_identity n r H D E 1
  norm_num only [one_pow, div_one] at hh
  nlinarith [hh]

/-- Uniform in all odd particle orders, including the physical N=1 term. -/
theorem odd_onsiteFormFactor_exponential_bound (n : ℕ)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im)
    (hi : ∀ y : ℂ, ‖y‖=r → ‖(globalRoot s y)⁻¹‖ ≤ A) :
    let D := max 1 (2*r/(1-r^2))
    let X := r*(A*r⁻¹)*(2*r^2/(1-r^2))
    ‖onsiteFormFactor (2*n+1) r s‖ ≤
      (X*D)*((X^2*D/2)^n/(n.factorial:ℝ)) := by
  dsimp only
  have ha := globalRoot_admissible hr hr1 hm
  rw [onsite_residue_reduction (2*n+1) r hr s (globalRoot s)
    (fun y hy => ha.toTuple (2*n+1) y hy)]
  have hb := multiCircleIntegral_norm_le (2*n+1) hr.le
    (fun y => reducedOnsiteDensity (fun i => globalRoot s (y i)) y) (by
      intro y hy
      exact reducedOnsiteDensity_upper_bound hr hr1 hA (by positivity)
        _ y (fun i => (globalRoot_inside_radius hr hr1 hm (hy i)).le) hy
        (fun i => hi (y i) (hy i)) (original_root_pairProduct_norm hr hr1 hm y hy)
        (odd_circle_pairProduct_matching_bound n hr.le hr1 y hy))
  have hnorm := mul_le_mul_of_nonneg_left hb
    (inv_nonneg.mpr (Nat.cast_nonneg (2*n+1).factorial))
  simp only [reducedOnsiteFormFactor, norm_mul, norm_inv, Complex.norm_natCast]
  rw [odd_onsite_matching_majorant_identity] at hnorm
  exact hnorm

end
end IsingBulk.HT.Final
