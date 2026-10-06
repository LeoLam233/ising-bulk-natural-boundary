import IsingBulk.Tail.WeightedAngularPfaffian

/-! The actual original-contour weighted y-Pfaffian, at every even order,
with constants chosen before N and epsilon on a common source disk. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set IsingBulk.First IsingBulk.Branch
open scoped Topology

theorem original_y_pair_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun p : ℝ × ℝ => pairKernel (anglePoint r p.1) (anglePoint r p.2)) := by
  have hx : Continuous (fun p : ℝ × ℝ => anglePoint r p.1) := (continuous_circleMap 0 r).comp continuous_fst
  have hy : Continuous (fun p : ℝ × ℝ => anglePoint r p.2) := (continuous_circleMap 0 r).comp continuous_snd
  apply (hx.sub hy).div (continuous_const.sub (hx.mul hy))
  intro p
  exact one_sub_mul_ne_zero_of_norm_lt_one (by rw [anglePoint_norm hr]; exact hr1)
    (by rw [anglePoint_norm hr]; exact hr1)

def originalWeightedPfaffianIntegral (d : LocalBranchData) (n : ℕ) (e : ℝ) (s : ℂ) : ℝ :=
  ∫ x : Fin (2*n) → ℝ,
    ((List.finRange (2*n)).map (fun a => ‖originalResidueAngle d e s (x a)‖)).prod *
    ‖labelPfaffian (fun a b => pairKernel (anglePoint (Real.exp (-d.c₀*e)) (x a))
      (anglePoint (Real.exp (-d.c₀*e)) (x b))) n (List.finRange (2*n))‖
    ∂Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))

theorem original_weighted_pfaffian_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ C delta e0 : ℝ, 0 < C ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ n : ℕ, ∀ e : ℝ, 0 < e → e < e0 → ∀ s : ℂ,
        ‖s-radialParameter d.theta e‖ ≤ delta*e →
        originalWeightedPfaffianIntegral d n e s ≤
          (matchingCount n:ℝ)*(C*(Real.log (1/e)+1)^2)^n := by
  obtain ⟨C,deltaP,eP,hC,hdP,heP,heP1,hpair⟩ :=
    original_weighted_pair_logarithmic_square d hcsmall
  obtain ⟨_,_,deltaR,eR,_,_,hdR,heR,_,hR⟩ := original_residue_square_pointwise d hcsmall
  refine ⟨C,min deltaP deltaR,min eP eR,hC,lt_min hdP hdR,lt_min heP heR,
    (min_le_left _ _).trans heP1,?_⟩
  intro n e he heSmall s hs
  have heP' := heSmall.trans_le (min_le_left eP eR)
  have heR' := heSmall.trans_le (min_le_right eP eR)
  have hsP := hs.trans (mul_le_mul_of_nonneg_right (min_le_left deltaP deltaR) he.le)
  have hsR := hs.trans (mul_le_mul_of_nonneg_right (min_le_right deltaP deltaR) he.le)
  have hcont := (hR e he heR' s hsR).1.norm
  have hr : 0 ≤ Real.exp (-d.c₀*e) := (Real.exp_pos _).le
  have hr1 : Real.exp (-d.c₀*e) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hp := weighted_angular_pfaffian_integral n (2*Real.pi)
    (fun theta => ‖originalResidueAngle d e s theta‖) hcont (fun _ => norm_nonneg _)
    (fun theta phi => pairKernel (anglePoint (Real.exp (-d.c₀*e)) theta)
      (anglePoint (Real.exp (-d.c₀*e)) phi)) (original_y_pair_continuous hr hr1)
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀
  · apply setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    intro p hp
    positivity
  · exact hpair e he heP' s hsP

end
end IsingBulk.Tail
