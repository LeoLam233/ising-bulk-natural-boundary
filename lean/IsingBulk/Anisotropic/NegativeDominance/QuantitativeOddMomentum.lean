import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedAngles
import IsingBulk.Anisotropic.NegativeDominance.OddMomentum
import IsingBulk.Anisotropic.RegularEdges.ProductGap

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

/-- Telescoping product estimate with no loss exponential in the index. -/
theorem norm_prod_sub_one_le_sum {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i∈s, ‖z i‖≤1) : ‖∏ i∈s,z i - 1‖≤∑ i∈s,‖z i-1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    have hs := ih (fun i hi => hz i (Finset.mem_insert_of_mem hi))
    have hza := hz a (Finset.mem_insert_self a s)
    calc
      ‖z a*(∏ i∈s,z i)-1‖ = ‖z a*((∏ i∈s,z i)-1)+(z a-1)‖ := by congr 1; ring
      _ ≤ ‖z a‖*‖(∏ i∈s,z i)-1‖+‖z a-1‖ := by simpa only [norm_mul] using norm_add_le (z a*((∏ i∈s,z i)-1)) (z a-1)
      _ ≤ ‖(∏ i∈s,z i)-1‖+‖z a-1‖ := by nlinarith [norm_nonneg ((∏ i∈s,z i)-1)]
      _ ≤ ‖z a-1‖+∑ i∈s,‖z i-1‖ := by linarith

theorem phase_product_neg_one_norm_lower {N : ℕ} (q : Fin N → ℝ)
    (hp : (∏ i,limitingAngle (q i))= -1) : 2≤(N : ℝ)*‖q‖ := by
  have h := norm_prod_sub_one_le_sum Finset.univ (fun i => limitingAngle (q i))
    (fun i _ => (limitingAngle_norm (q i)).le)
  rw [hp] at h
  have hnorm : ‖(-1 : ℂ)-1‖=(2 : ℝ) := by norm_num
  rw [hnorm] at h
  apply h.trans
  calc
    ∑ i,‖limitingAngle (q i)-1‖ ≤ ∑ i,‖q i‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [limitingAngle,mul_comm] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := q i))
    _ ≤ ∑ _i : Fin N,‖q‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm q i)
    _ = (N : ℝ)*‖q‖ := by simp

theorem limitingAngle_sub_pi (q : ℝ) : limitingAngle (q-Real.pi)= -limitingAngle q := by
  simp [limitingAngle,Complex.ofReal_sub,sub_mul,Complex.exp_sub,Complex.exp_pi_mul_I,div_neg]

theorem odd_shifted_phase_product {n : ℕ} (hn : Odd (n+1)) (v : Fin n → ℝ) :
    (∏ i,limitingAngle (negativeShiftedAngles n v i))= -1 := by
  have hp : (∏ i,limitingAngle (physicalDependentAngles n (fun k => v k+Real.pi) i))=1 := by
    simp only [limitingAngle,←Complex.exp_sum,←Finset.sum_mul,←Complex.ofReal_sum,
      physicalDependentAngles_sum_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero]
  simp only [negativeShiftedAngles,limitingAngle_wrapAngle,limitingAngle_sub_pi,
    Finset.prod_neg,Finset.card_univ,Fintype.card_fin,hn.neg_one_pow,hp,mul_one]

/-- Quantitative exclusion of the full collision on every odd constrained
angular torus. This works for every particle number, including growing indices. -/
theorem odd_shifted_angles_norm_lower {n : ℕ} (hn : Odd (n+1)) (v : Fin n → ℝ) :
    2≤((n+1 : ℕ) : ℝ)*‖negativeShiftedAngles n v‖ :=
  phase_product_neg_one_norm_lower _ (odd_shifted_phase_product hn v)

end
end IsingBulk.Anisotropic.NegativeDominance
