import IsingBulk.Anisotropic.NegativeDominance.HighPoleEntropy

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- All actual integer winding sectors (at most N+1) cost only a further
N² term, preserving the high-range entropy suppression. -/
theorem finite_winding_entropy {ι : Type*} (S : Finset ι) (N j : ℕ) (hN : 1≤N)
    (hcard : S.card≤N+1) (C : ℝ) (z : ι→ℂ)
    (hz : ∀k∈S,‖z k‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+C*(N : ℝ)^2)) :
    ∑k∈S,‖z k‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+(C+1)*(N : ℝ)^2) := by
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hcardR : (S.card : ℝ)≤(N : ℝ)+1 := by exact_mod_cast hcard
  have hcount : (S.card : ℝ)≤Real.exp ((N : ℝ)^2) := by
    apply hcardR.trans
    have hh := Real.add_one_le_exp ((N : ℝ)^2)
    nlinarith only [hh,hNR]
  calc
    _ ≤ ∑_k∈S,Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+C*(N : ℝ)^2) :=
      Finset.sum_le_sum hz
    _ = (S.card : ℝ)*Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+C*(N : ℝ)^2) := by simp
    _ ≤ Real.exp ((N : ℝ)^2)*Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+C*(N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end
end IsingBulk.Anisotropic.NegativeDominance
