import IsingBulk.Preferred22.Arithmetic
import IsingBulk.Preferred22.Coordinates

/-! Concrete physical branch data for every member of the manuscript's
prime-root family, including the exact first-order resonance. -/
namespace IsingBulk.Preferred22
noncomputable section
open IsingBulk.PrimeFamily

def preferredBranchAt (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi/2) :
    PreferredBranchData where
  alpha := α
  b := Real.arccos (2*Real.cos α-1)
  alpha_pos := hα
  alpha_lt := hαπ
  b_pos := by
    apply Real.arccos_pos.mpr
    have hc : Real.cos α<1 := by
      simpa using Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := 0)
        (by norm_num) hαπ.le hα
    linarith
  b_lt := by
    apply Real.arccos_lt_pi.mpr
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hαπ⟩
    linarith
  angle_relation := by
    apply Real.cos_arccos
    · have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hαπ⟩
      linarith
    · linarith [Real.cos_le_one α]

def preferredPrimeBranchData {p : ℕ} {a : ℤ} (ha : Admissible p a) :
    PreferredBranchData := preferredBranchAt (angle p a) ha.1 ha.2

theorem preferred_prime_branch_parameter {p : ℕ} {a : ℤ} (ha : Admissible p a) :
    (preferredPrimeBranchData ha).alpha=angle p a := rfl

theorem preferred_prime_branch_root {p : ℕ} {a : ℤ} (ha : Admissible p a) :
    Complex.exp (-((preferredPrimeBranchData ha).b:ℂ)*Complex.I)=primeBranch p a := rfl

theorem preferred_prime_first_resonance {p : ℕ} (hp : 0<p) (a : ℤ) :
    Complex.exp (-((2*p:ℕ):ℂ)*(angle p a:ℂ)*Complex.I)=1 := by
  have hp0 : p≠0 := hp.ne'
  have h : IsingBulk.PrimeFamily.angleRoot p a^(2*p)=1 := by
    rw [Nat.mul_comm 2 p,pow_mul,angleRoot_pow hp0 a,one_pow]
  have he : Complex.exp (((2*p:ℕ):ℂ)*((angle p a:ℂ)*Complex.I))=1 := by
    rw [Complex.exp_nat_mul]
    exact h
  rw [show -((2*p:ℕ):ℂ)*(angle p a:ℂ)*Complex.I=
    -(((2*p:ℕ):ℂ)*((angle p a:ℂ)*Complex.I)) by ring,Complex.exp_neg,he,inv_one]

theorem preferred_prime_critical_derivative {p : ℕ} (hp : 0<p) :
    2*((2*p)^2/2-1)+2=(2*p)^2 := by
  have hsq : (2*p)^2=2*(2*p^2) := by ring
  rw [hsq,Nat.mul_div_right _ (by norm_num)]
  have hpos : 1≤2*p^2 := by nlinarith
  omega

end
end IsingBulk.Preferred22
