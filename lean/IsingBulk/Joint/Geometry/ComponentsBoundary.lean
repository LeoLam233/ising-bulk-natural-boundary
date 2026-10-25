import IsingBulk.Joint.Geometry.ExactSpectrum
import IsingBulk.Joint.Geometry.LowTopology

namespace IsingBulk.Joint
noncomputable section
open Set

@[fun_prop] theorem continuous_F1 : Continuous F1 := by unfold F1; fun_prop
@[fun_prop] theorem continuous_F2 : Continuous F2 := by unfold F2; fun_prop

private theorem closure_le {f g : Coupling → ℝ} (hf : Continuous f) (hg : Continuous g)
    {D : Set Coupling} (h : ∀ K ∈ D, f K < g K) :
    ∀ K ∈ closure D, f K ≤ g K :=
  closure_minimal (fun K hK => (h K hK).le) (isClosed_le hf hg)

theorem closure_high_bounds {K : Coupling} (hK : K ∈ closure highDomain) :
    |K.1.im| ≤ Real.pi/2 ∧ |K.2.im| ≤ Real.pi/2 ∧ 0 ≤ F1 K ∧ 0 ≤ F2 K := by
  refine ⟨closure_le (by fun_prop) continuous_const (fun _ h => h.1) K hK,
    closure_le (by fun_prop) continuous_const (fun _ h => h.2.1) K hK,?_,?_⟩
  · exact closure_le continuous_const continuous_F1
      (fun _ h => (positive_signs_of_mem_highDomain h).1) K hK
  · exact closure_le continuous_const continuous_F2
      (fun _ h => (positive_signs_of_mem_highDomain h).2) K hK

theorem closure_low_bounds {K : Coupling} (hK : K ∈ closure lowDomain) :
    0 ≤ K.1.re ∧ 0 ≤ K.2.re ∧ F1 K ≤ 0 ∧ F2 K ≤ 0 := by
  refine ⟨closure_le continuous_const (by fun_prop) (fun _ h => h.1) K hK,
    closure_le continuous_const (by fun_prop) (fun _ h => h.2.1) K hK,?_,?_⟩
  · exact closure_le continuous_F1 continuous_const
      (fun _ h => (negative_signs_of_mem_lowDomain h).1) K hK
  · exact closure_le continuous_F2 continuous_const
      (fun _ h => (negative_signs_of_mem_lowDomain h).2) K hK

private theorem positive_edge_inequality {x u y : ℝ} (hy : |y| < Real.pi/2)
    (h : 0 < Real.cosh u^2 * Real.cos y^2 - Real.cosh x^2 * Real.sinh u^2) :
    Real.cosh x * Real.tanh |u| < Real.cos y := by
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hy)
  have hu := Real.cosh_pos u
  have ha : Real.cosh |u| = Real.cosh u := by
    rcases le_total 0 u with hh | hh
    · rw [abs_of_nonneg hh]
    · rw [abs_of_nonpos hh, Real.cosh_neg]
  rw [Real.tanh_eq_sinh_div_cosh,ha,←mul_div_assoc,div_lt_iff₀ hu]
  have hs : Real.sinh |u|^2 = Real.sinh u^2 := by rw [← Real.abs_sinh,sq_abs]
  have hn : 0 ≤ Real.cosh x * Real.sinh |u| := by positivity
  have hp : 0 < Real.cos y * Real.cosh u := mul_pos hc hu
  nlinarith [sq_nonneg (Real.cosh x*Real.sinh |u| - Real.cos y*Real.cosh u)]

private theorem negative_edge_inequality {x u y : ℝ} (hu : 0 < u)
    (h : Real.cosh u^2 * Real.cos y^2 - Real.cosh x^2 * Real.sinh u^2 < 0) :
    |Real.cos y| < Real.cosh x * Real.tanh u := by
  rw [Real.tanh_eq_sinh_div_cosh,←mul_div_assoc,lt_div_iff₀ (Real.cosh_pos u)]
  have hp : 0 < Real.cosh x * Real.sinh u := mul_pos (Real.cosh_pos x) (Real.sinh_pos_iff.mpr hu)
  have hn : 0 ≤ |Real.cos y| * Real.cosh u := by positivity
  have hs := sq_abs (Real.cos y)
  nlinarith [sq_nonneg (|Real.cos y| * Real.cosh u - Real.cosh x * Real.sinh u)]

theorem frontier_high_subset_spectralSet : frontier highDomain ⊆ spectralSet := by
  intro K hK
  by_contra hs
  have hp : 0 < F1 K * F2 K := lt_of_not_ge (fun h => hs ((mem_spectralSet_iff_signs K).mpr h))
  obtain ⟨hy,hv,h₁,h₂⟩ := closure_high_bounds (frontier_subset_closure hK)
  have hf : 0 < F1 K := by nlinarith
  have hg : 0 < F2 K := by nlinarith
  have hy' : |K.1.im| < Real.pi/2 := by
    apply lt_of_le_of_ne hy
    intro he
    have hc : Real.cos K.1.im = 0 := by rw [← Real.cos_abs,he,Real.cos_pi_div_two]
    dsimp [F1] at hf
    rw [hc] at hf
    nlinarith [mul_nonneg (sq_nonneg (Real.cosh K.1.re)) (sq_nonneg (Real.sinh K.2.re))]
  have hv' : |K.2.im| < Real.pi/2 := by
    apply lt_of_le_of_ne hv
    intro he
    have hc : Real.cos K.2.im = 0 := by rw [← Real.cos_abs,he,Real.cos_pi_div_two]
    dsimp [F2] at hg
    rw [hc] at hg
    nlinarith [mul_nonneg (sq_nonneg (Real.cosh K.2.re)) (sq_nonneg (Real.sinh K.1.re))]
  have hm : K ∈ highDomain := ⟨hy',hv',positive_edge_inequality hy' hf,
    positive_edge_inequality hv' (by simpa [F2,mul_comm] using hg)⟩
  rw [highDomain_isOpen.frontier_eq] at hK
  exact hK.2 hm

theorem frontier_low_subset_spectralSet : frontier lowDomain ⊆ spectralSet := by
  intro K hK
  by_contra hs
  have hp : 0 < F1 K * F2 K := lt_of_not_ge (fun h => hs ((mem_spectralSet_iff_signs K).mpr h))
  obtain ⟨hx,hu,h₁,h₂⟩ := closure_low_bounds (frontier_subset_closure hK)
  have hf : F1 K < 0 := by nlinarith
  have hg : F2 K < 0 := by nlinarith
  have hx' : 0 < K.1.re := by
    apply lt_of_le_of_ne hx
    intro he
    dsimp [F2] at hg
    rw [← he,Real.sinh_zero,Real.cosh_zero] at hg
    nlinarith [sq_nonneg (Real.cos K.2.im)]
  have hu' : 0 < K.2.re := by
    apply lt_of_le_of_ne hu
    intro he
    dsimp [F1] at hf
    rw [← he,Real.sinh_zero,Real.cosh_zero] at hf
    nlinarith [sq_nonneg (Real.cos K.1.im)]
  have hm : K ∈ lowDomain := ⟨hx',hu',negative_edge_inequality hu' hf,
    negative_edge_inequality hx' (by simpa [F2,mul_comm] using hg)⟩
  rw [lowDomain_isOpen.frontier_eq] at hK
  exact hK.2 hm

end
end IsingBulk.Joint
