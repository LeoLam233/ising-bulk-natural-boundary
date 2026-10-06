import IsingBulk.Tail.GlobalAnalytic
import Mathlib.Data.Nat.Choose.Cast

namespace IsingBulk.Tail
noncomputable section

/-- The exact scalar budget of the all-branch numerator jets at q=1/2. -/
def allBranchNumeratorJetBudget (N J : ℕ) (C : ℝ) : ℝ :=
  (2:ℝ)^J*((2:ℝ)^J*((2^J*C)^N+(2^J*C)^N)*
    (C^J*((N.choose 2:ℝ)+1)^J*(1/2:ℝ)^((N.choose 2:ℤ)-(J:ℤ))))*(2^J*C)^N

lemma half_zpow_choose (N J : ℕ) :
    (1/2:ℝ)^((N.choose 2:ℤ)-(J:ℤ)) =
      Real.exp (-Real.log 2*((N:ℝ)*((N:ℝ)-1)/2-J)) := by
  rw [← Real.rpow_intCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<1/2)]
  congr 1
  rw [one_div,Real.log_inv]
  simp only [Int.cast_sub,Int.cast_natCast,Nat.cast_choose_two]

 theorem allBranchNumeratorJetBudget_gaussian (J : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 2 ≤ N →
      allBranchNumeratorJetBudget N J C ≤
        (N:ℝ)^(2*J)*Real.exp (A*N-(Real.log 2/2)*(N:ℝ)^2) := by
  let B := (2:ℝ)^J*C
  let K := (2:ℝ)^(2*J+1)*C^J
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2*B+K+L*(J+1),by positivity,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : 2 ≤ (N:ℝ) := by exact_mod_cast hN
  have hm : (N.choose 2:ℝ)+1 ≤ (N:ℝ)^2 := by rw [Nat.cast_choose_two]; nlinarith
  have hpoly : ((N.choose 2:ℝ)+1)^J ≤ (N:ℝ)^(2*J) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hm J
  have hp : B^N ≤ Real.exp (B*N) := by
    have he : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    simpa only [← Real.exp_nat_mul,mul_comm] using pow_le_pow_left₀ hB.le he N
  have hk : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have heq : allBranchNumeratorJetBudget N J C =
      K*(B^N)^2*((N.choose 2:ℝ)+1)^J*
        Real.exp (-L*((N:ℝ)*((N:ℝ)-1)/2-J)) := by
    unfold allBranchNumeratorJetBudget
    rw [half_zpow_choose]
    dsimp [K,B,L]
    rw [pow_add,show (2:ℝ)^(2*J)=(2^J)^2 by rw [mul_comm 2 J,pow_mul]]
    ring
  rw [heq]
  calc
    _ ≤ Real.exp K*(Real.exp (B*N))^2*(N:ℝ)^(2*J)*
        Real.exp (-L*((N:ℝ)*((N:ℝ)-1)/2-J)) := by gcongr
    _ = (N:ℝ)^(2*J)*Real.exp (K+2*(B*N)-L*((N:ℝ)*((N:ℝ)-1)/2-J)) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      rw [mul_comm _ ((N:ℝ)^(2*J)),mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      have hKN : K ≤ K*(N:ℝ) := by nlinarith
      have hJN : (J:ℝ) ≤ (J:ℝ)*(N:ℝ) := by nlinarith
      dsimp [L] at *
      nlinarith

end
end IsingBulk.Tail
