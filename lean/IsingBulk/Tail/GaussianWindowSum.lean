import IsingBulk.Tail.GlobalAnalytic
import IsingBulk.Tail.SummationGrowth

/-! Actual scalar summation of a Gaussian order budget on the high-order
window. Geometric sector estimates must be attached separately. -/
namespace IsingBulk.Tail
noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology

def gaussianWindowTail (C kappa D H : ℝ) : ℝ :=
  ∑' N : ℕ, if D*Real.sqrt H ≤ (N:ℝ) then C^N*Real.exp (-kappa*(N:ℝ)^2) else 0

theorem gaussian_window_tail_bound {C kappa D : ℝ} (hC : 0 ≤ C)
    (hk : 0 < kappa) (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∀ H : ℝ, 0 ≤ H →
      gaussianWindowTail C kappa D H ≤ B*Real.exp (-(kappa/2)*D^2*H) := by
  let f : ℕ → ℝ := fun N => C^N*Real.exp (-(kappa/2)*(N:ℝ)^2)
  have hf : Summable f := by
    simpa only [pow_zero,mul_one] using summable_source_gaussian hC (show 0 < kappa/2 by positivity) 0
  let B := (∑' N, f N)+1
  have hb0 : 0 ≤ ∑' N, f N := tsum_nonneg (fun _ => by dsimp [f]; positivity)
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro H hH
  let E := Real.exp (-(kappa/2)*D^2*H)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hpoint (N : ℕ) :
      (if D*Real.sqrt H ≤ (N:ℝ) then C^N*Real.exp (-kappa*(N:ℝ)^2) else 0) ≤ E*f N := by
    split_ifs with hN
    · have hs : (Real.sqrt H)^2=H := Real.sq_sqrt hH
      have hn2 : D^2*H ≤ (N:ℝ)^2 := by
        have ht := mul_self_le_mul_self (mul_nonneg hD (Real.sqrt_nonneg _)) hN
        nlinarith
      have he : Real.exp (-kappa*(N:ℝ)^2) ≤
          Real.exp (-(kappa/2)*D^2*H)*Real.exp (-(kappa/2)*(N:ℝ)^2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hm := mul_le_mul_of_nonneg_left he (pow_nonneg hC N)
      simpa only [E,f,mul_left_comm] using hm
    · dsimp [E,f]
      positivity
  have hg := (hf.mul_left E).of_nonneg_of_le (fun N => by split_ifs <;> positivity) hpoint
  have hh := hg.tsum_le_tsum hpoint (hf.mul_left E)
  rw [tsum_mul_left] at hh
  exact hh.trans (by dsimp only [B]; nlinarith)

theorem gaussian_window_tail_isLittleO {C kappa D : ℝ} (hC : 0 ≤ C)
    (hk : 0 < kappa) (hD : 0 ≤ D) (a b : ℝ)
    (hexp : a-(kappa/2)*D^2 < b) :
    (fun H : ℝ => Real.exp (a*H)*gaussianWindowTail C kappa D H) =o[atTop]
      (fun H : ℝ => Real.exp (b*H)) := by
  obtain ⟨B,hB,hbound⟩ := gaussian_window_tail_bound hC hk hD
  have hb : (fun H : ℝ => Real.exp (a*H)*gaussianWindowTail C kappa D H) =O[atTop]
      (fun H : ℝ => Real.exp ((a-(kappa/2)*D^2)*H)) := by
    apply IsBigO.of_bound B
    filter_upwards [eventually_ge_atTop (0:ℝ)] with H hH
    have hn : 0 ≤ gaussianWindowTail C kappa D H := by
      apply tsum_nonneg
      intro N
      split_ifs <;> positivity
    have hm := mul_le_mul_of_nonneg_left (hbound H hH) (Real.exp_pos (a*H)).le
    have heq : Real.exp (a*H)*Real.exp (-(kappa/2)*D^2*H) =
        Real.exp ((a-(kappa/2)*D^2)*H) := by rw [← Real.exp_add]; congr 1; ring
    have hp : 0 ≤ Real.exp (a*H)*gaussianWindowTail C kappa D H := mul_nonneg (Real.exp_pos _).le hn
    simp only [Real.norm_eq_abs,abs_of_nonneg hp,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (a*H)*(B*Real.exp (-(kappa/2)*D^2*H)) := hm
      _ = _ := by rw [← mul_assoc,mul_comm (Real.exp (a*H)) B,mul_assoc,heq]
  exact hb.trans_isLittleO (fixed_linear_exp_isLittleO hexp)

end
end IsingBulk.Tail
