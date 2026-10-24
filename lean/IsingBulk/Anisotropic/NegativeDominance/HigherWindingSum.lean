import IsingBulk.Anisotropic.NegativeDominance.HigherWindingMiddle

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped BigOperators Topology

/-- Summing all higher winding sectors preserves the exponential loss. -/
theorem finite_higher_winding_envelope {ι : Type*} (S : Finset ι) (N j : ℕ) (hN : 1≤N)
    (hcard : S.card≤N+1) (C P : ℝ) (hP : 0≤P) (z : ι→ℂ)
    (hz : ∀k∈S,‖z k‖≤Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)*P) :
    ∑k∈S,‖z k‖≤Real.exp ((C+1)*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)*P := by
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hcardR : (S.card : ℝ)≤(N : ℝ)+1 := by exact_mod_cast hcard
  have hcount : (S.card : ℝ)≤Real.exp ((N : ℝ)^2) := by
    apply hcardR.trans
    have hh := Real.add_one_le_exp ((N : ℝ)^2)
    nlinarith only [hh,hNR]
  calc
    _ ≤ ∑_k∈S,Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)*P := Finset.sum_le_sum hz
    _ = (S.card : ℝ)*(Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)*P) := by simp
    _ ≤ Real.exp ((N : ℝ)^2)*(Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)*P) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      rw [←mul_assoc,←mul_assoc,←Real.exp_add]
      congr 2
      congr 1
      ring

/-- Uniform middle-range suppression of the sum of every higher winding.
Neither a selected winding nor a finite particle-index surrogate is used. -/
theorem eventually_finite_higher_winding_middle (C : ℝ) (hC : 0<C) :
    ∀ᶠ j : ℕ in atTop,∀N : ℕ,1≤N →
      (N : ℝ)^2≤(j : ℝ)/Real.sqrt (Real.log j) →
      ∀(ι : Type*) (S : Finset ι),S.card≤N+1 → ∀(P : ℝ),0≤P → ∀z : ι→ℂ,
      (∀k∈S,‖z k‖≤Real.exp (C*(N : ℝ)^2)*(1/2 : ℝ)^(j/2)*P) →
      ∑k∈S,‖z k‖≤Real.exp (-(j : ℝ)*Real.log 2/4)*P := by
  filter_upwards [eventually_higher_winding_middle (C+1) (by linarith)] with j hj
  intro N hN hcut ι S hcard P hP z hz
  exact (finite_higher_winding_envelope S N j hN hcard C P hP z hz).trans
    (mul_le_mul_of_nonneg_right (hj N hcut).2 hP)

end
end IsingBulk.Anisotropic.NegativeDominance
