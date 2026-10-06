import IsingBulk.Tail.ExteriorCutoffJetBounds

/-! The broad far-region cutoff cost after literal exponential scales.
This lemma is not used for the sharper near-collision radial powers. -/
namespace IsingBulk.Tail
noncomputable section

def exteriorCutoffCost (J N : ℕ) (C K b R rho : ℝ) : ℝ :=
  (2:ℝ)^J*(C^N*(b⁻¹)^J)*(1+J.factorial*K*(branchShapeJetCost N R rho)^J)

theorem exterior_cutoff_scale_cost (J : ℕ) {A B c C K R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hC : 1 ≤ C) (hK : 1 ≤ K) (hR : 0 ≤ R) :
    ∃ M D : ℝ, 0 < M ∧ 0 < D ∧ ∀ N : ℕ, 1 ≤ N →
      exteriorCutoffCost J N C K (allBranchMicroRadius A c N) R (allBranchEqualityRadius B N) ≤
        M*Real.exp (D*(N:ℝ))*(N:ℝ)^(2*J) := by
  let T : ℝ := 1+8*(1+R)^2/3
  have hT : 1 ≤ T := by dsimp [T]; nlinarith [sq_nonneg (1+R)]
  let M : ℝ := (2:ℝ)^J*(c⁻¹)^J*(1+J.factorial*K*T^J)
  let D : ℝ := C+(A+4+2*B)*(J:ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨M,D,hM,hD,?_⟩
  intro N hN
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  have he : 1 ≤ Real.exp (2*B*(N:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hshape : branchShapeJetCost N R (allBranchEqualityRadius B N) ≤
      T*(N:ℝ)*Real.exp (2*B*(N:ℝ)) := by
    have hden : (allBranchEqualityRadius B N)^2 = Real.exp (-2*B*(N:ℝ)) := by
      unfold allBranchEqualityRadius
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    unfold branchShapeJetCost
    rw [hden,show -2*B*(N:ℝ)= -(2*B*(N:ℝ)) by ring,Real.exp_neg]
    have he0 : Real.exp (2*B*(N:ℝ)) ≠ 0 := (Real.exp_pos _).ne'
    have heq : 8*(N:ℝ)*(1+R)^2/(3*(Real.exp (2*B*(N:ℝ)))⁻¹) =
        (8*(1+R)^2/3)*(N:ℝ)*Real.exp (2*B*(N:ℝ)) := by field_simp
    rw [heq]
    dsimp [T]
    nlinarith
  have hshape0 : 0 ≤ branchShapeJetCost N R (allBranchEqualityRadius B N) := by
    unfold branchShapeJetCost
    positivity
  have hp := pow_le_pow_left₀ hshape0 hshape J
  rw [mul_pow,mul_pow,← Real.exp_nat_mul] at hp
  have he1 : 1 ≤ (N:ℝ)^J*Real.exp ((J:ℝ)*(2*B*(N:ℝ))) := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn)
      (Real.one_le_exp_iff.mpr (by positivity))
  have hpoly : 1+J.factorial*K*(branchShapeJetCost N R (allBranchEqualityRadius B N))^J ≤
      (1+J.factorial*K*T^J)*(N:ℝ)^J*Real.exp ((J:ℝ)*(2*B*(N:ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (J.factorial:ℝ)*K by positivity)
    nlinarith
  have hbase : (allBranchMicroRadius A c N)⁻¹ =
      c⁻¹*(N:ℝ)*Real.exp ((A+4)*(N:ℝ)) := by
    unfold allBranchMicroRadius
    rw [inv_div,div_eq_mul_inv,mul_inv_rev,← Real.exp_neg]
    rw [show - (-(A+4)*(N:ℝ))=(A+4)*(N:ℝ) by ring]
    ring
  have hCb : C ≤ Real.exp C := by linarith [Real.add_one_le_exp C]
  have hCN := pow_le_pow_left₀ (show 0 ≤ C by positivity) hCb N
  rw [← Real.exp_nat_mul] at hCN
  unfold exteriorCutoffCost
  rw [hbase,mul_pow,mul_pow,← Real.exp_nat_mul]
  calc
    _ ≤ (2:ℝ)^J*(Real.exp ((N:ℝ)*C)*
          ((c⁻¹)^J*(N:ℝ)^J*Real.exp ((J:ℝ)*((A+4)*(N:ℝ)))))*
          ((1+J.factorial*K*T^J)*(N:ℝ)^J*Real.exp ((J:ℝ)*(2*B*(N:ℝ)))) := by
      gcongr
    _ = M*Real.exp (D*(N:ℝ))*(N:ℝ)^(2*J) := by
      dsimp [M,D]
      rw [show 2*J=J+J by omega,pow_add]
      have heq : Real.exp ((C+(A+4+2*B)*(J:ℝ))*(N:ℝ)) =
          Real.exp ((N:ℝ)*C)*Real.exp ((J:ℝ)*((A+4)*(N:ℝ)))*Real.exp ((J:ℝ)*(2*B*(N:ℝ))) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      rw [heq]
      ring

end
end IsingBulk.Tail
