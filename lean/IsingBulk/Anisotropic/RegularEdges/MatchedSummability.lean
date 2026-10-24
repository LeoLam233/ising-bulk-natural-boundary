import IsingBulk.Anisotropic.RegularEdges.NumeratorJets
import IsingBulk.Anisotropic.RegularEdges.GaussianSummability

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.Tail

theorem gaussian_linear_log_summable (a : ℝ) {k C : ℝ}
    (hk : 0<k) (hC : 0≤C) (j : ℕ) :
    Summable (fun n : ℕ => (n:ℝ)^j*Real.exp (a*n-k*(n:ℝ)^2+C*n*Real.log ((n:ℝ)+1))) := by
  let d : ℝ := k/(2*(C+1))
  have hd : 0<d := by dsimp [d]; positivity
  have hde : 2*(C+1)*d=k := by dsimp [d]; field_simp
  have hCd : C*d≤k/2 := by nlinarith
  apply (summable_polynomial_gaussian (a+C*(d-1-Real.log d))
    (by positivity : 0<k/2) j).of_nonneg_of_le (fun n => by positivity)
  intro n
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hh := mul_le_mul_of_nonneg_left (logarithm_linear_majorant hd n)
    (mul_nonneg hC (Nat.cast_nonneg n))
  have hq := mul_le_mul_of_nonneg_right hCd (sq_nonneg (n:ℝ))
  nlinarith

private theorem nat_pow_eq_exp_log {x : ℝ} (hx : 0<x) (n : ℕ) :
    x^n=Real.exp ((n:ℝ)*Real.log x) := by
  rw [Real.exp_nat_mul,Real.exp_log hx]

theorem evenEdgeMajorant_exp_bound {r C M : ℝ} (hr : 0<r) (hC : 0<C) (hM : 0<M) (n : ℕ) :
    evenEdgeMajorant r C M n ≤ Real.exp
      ((Real.log (2*M^2*C)-2*Real.log r)*n-(-2*Real.log r)*(n:ℝ)^2+
        n*Real.log ((n:ℝ)+1)) := by
  have hm : (matchingCount n:ℝ)≤(2*((n:ℝ)+1))^n := by
    have hh := (matchingCount_le_pow n).trans
      (Nat.pow_le_pow_left (show 2*n≤2*(n+1) by omega) n)
    exact_mod_cast hh
  have hE : 0<2*M^2*C := by positivity
  have hn : 0<(n:ℝ)+1 := by positivity
  have hexp : ((2*n*(n-1):ℕ):ℝ)=2*(n:ℝ)^2-2*n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]; ring
  calc
    evenEdgeMajorant r C M n = (matchingCount n:ℝ)*(M^2*C)^n*r^(2*n*(n-1)) := by
      unfold evenEdgeMajorant
      rw [mul_pow,pow_mul]
      ring
    _ ≤ (2*((n:ℝ)+1))^n*(M^2*C)^n*r^(2*n*(n-1)) := by gcongr
    _ = (2*M^2*C*((n:ℝ)+1))^n*r^(2*n*(n-1)) := by rw [← mul_pow]; congr 2; ring
    _ = _ := by
      rw [nat_pow_eq_exp_log (mul_pos hE hn),nat_pow_eq_exp_log hr,← Real.exp_add,
        Real.log_mul hE.ne' hn.ne',hexp]
      congr 1
      ring

theorem evenEdgeMajorant_polynomial_summable {r C M : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (j : ℕ) :
    Summable (fun n : ℕ => (n:ℝ)^j*evenEdgeMajorant r C M n) := by
  have hk : 0< -2*Real.log r := by nlinarith [Real.log_neg hr hr1]
  apply (gaussian_linear_log_summable (Real.log (2*M^2*C)-2*Real.log r) hk
    (by norm_num : (0:ℝ)≤1) j).of_nonneg_of_le
    (fun n => by unfold evenEdgeMajorant; positivity)
  intro n
  simpa only [one_mul] using mul_le_mul_of_nonneg_left
    (evenEdgeMajorant_exp_bound hr hC hM n) (pow_nonneg (Nat.cast_nonneg n) j)

theorem oddEdgeMajorant_le_even {r C M : ℝ}
    (hr : 0≤r) (hr1 : r≤1) (hC : 0≤C) (hM : 0≤M) (n : ℕ) :
    oddEdgeMajorant r C M n ≤ M*(2*(n:ℝ)+1)*evenEdgeMajorant r C M n := by
  have he : 2*n*(n-1)+2*n=2*n*n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  have hp : r^(2*n*n)≤r^(2*n*(n-1)) := by
    rw [← he,pow_add]
    exact mul_le_of_le_one_right (pow_nonneg hr _) (pow_le_one₀ hr hr1)
  unfold oddEdgeMajorant evenEdgeMajorant
  rw [matchingCount,Nat.cast_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
  calc
    _ ≤ M^(2*n)*M*((2*(n:ℝ)+1)*(matchingCount n:ℝ))*C^n*r^(2*n*(n-1)) := by gcongr
    _ = _ := by ring

theorem oddEdgeMajorant_polynomial_summable {r C M : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (j : ℕ) :
    Summable (fun n : ℕ => (n:ℝ)^j*oddEdgeMajorant r C M n) := by
  have ha := evenEdgeMajorant_polynomial_summable hr hr1 hC hM j
  have hb := evenEdgeMajorant_polynomial_summable hr hr1 hC hM (j+1)
  apply ((hb.mul_left 2).add ha |>.mul_left M).of_nonneg_of_le
    (fun n => by unfold oddEdgeMajorant; positivity)
  intro n
  have hh := mul_le_mul_of_nonneg_left (oddEdgeMajorant_le_even hr.le hr1.le hC.le hM.le n)
    (pow_nonneg (Nat.cast_nonneg n) j)
  convert hh using 1
  rw [pow_succ]
  ring
end
end IsingBulk.Anisotropic.RegularEdges
