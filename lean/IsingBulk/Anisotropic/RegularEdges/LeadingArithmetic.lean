import IsingBulk.Anisotropic.RegularEdges.LeadingFull

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First MeasureTheory

lemma odd_first_balance {q j : ℕ} (h : 2*j+1=(2*q+1)^2) :
    2*q+2+(2*q+1)*(2*q)=2*(j+1) := by nlinarith

lemma odd_first_degree {q j : ℕ} (hq : 1≤q) (h : 2*j+1=(2*q+1)^2) :
    1≤j ∧ (2*q)-1+(2*q+1)*(2*q)=2*(j-1)+1 := by
  have hj : 1≤j := by nlinarith
  have hb := odd_first_balance h
  constructor
  · exact hj
  · omega

lemma odd_higher_degree {q j i : ℕ} (h : 2*j+1=(2*q+1)^2) (hi : q < i) :
    1≤2*i ∧ 2*(j+1)≤(2*i+1)*(2*i) := by
  constructor
  · omega
  · have hm : (2*q+3)*(2*q+2)≤(2*i+1)*(2*i) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

lemma odd_first_majorant_integrable {q j : ℕ} (hq : 1≤q) (h : 2*j+1=(2*q+1)^2) :
    Integrable (@shapeMajorant (2*q) j) := by
  obtain ⟨hj,hdegree⟩ := odd_first_degree hq h
  simpa [Nat.sub_add_cancel hj] using shapeMajorant_odd_integrable (by omega : 1≤2*q) hdegree

lemma even_first_balance {q j : ℕ} (h : 2*(j+1)=(2*q+2)^2) :
    (2*q+1)+1+(2*q+1+1)*(2*q+1)=2*(j+1) := by nlinarith

lemma even_first_degree {q j : ℕ} (h : 2*(j+1)=(2*q+2)^2) :
    (2*q+1)-1+(2*q+1+1)*(2*q+1)=2*j := by
  have hb := even_first_balance h
  omega

lemma even_higher_degree {q j i : ℕ} (h : 2*(j+1)=(2*q+2)^2) (hi : q < i) :
    1≤2*i+1 ∧ 2*(j+1)≤(2*i+1+1)*(2*i+1) := by
  constructor
  · omega
  · have hm : (2*q+4)*(2*q+3)≤(2*i+1+1)*(2*i+1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

lemma even_first_majorant_integrable {q j : ℕ} (h : 2*(j+1)=(2*q+2)^2) :
    Integrable (@shapeMajorant (2*q+1) j) :=
  shapeMajorant_integrable (by omega) (even_first_degree h)

end
end IsingBulk.Anisotropic.RegularEdges
