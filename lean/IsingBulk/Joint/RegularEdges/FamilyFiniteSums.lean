import IsingBulk.Joint.RegularEdges.FamilyFiniteCoefficients

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem finite_common_bound {I : Type*} [DecidableEq I] (F : Finset I)
    (Q : Set E) (f : I→E→ℝ→ℂ)
    (h : ∀i∈F,∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ‖f i eta t‖≤C) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ∀i∈F,‖f i eta t‖≤C := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1,0,by norm_num,le_refl _,by simp⟩
  | @insert i F hi ih =>
    obtain ⟨a,A,ha,hA,hb⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨d,D,hd,hD,hF⟩ := ih (fun k hk=>h k (Finset.mem_insert_of_mem hk))
    refine ⟨min a d,A+D,lt_min ha hd,add_nonneg hA hD,?_⟩
    intro eta heta t ht htd k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (hb eta heta t ht (htd.trans_le (min_le_left _ _))).trans (le_add_of_nonneg_right hD)
    · exact (hF eta heta t ht (htd.trans_le (min_le_right _ _)) k hk).trans (le_add_of_nonneg_left hA)

/-- All lower nonresonant and higher post-first-resonant terms in an arbitrary
finite set, and all derivatives up to J, share one family radius and bound. -/
theorem compact_family_finite_coefficient_bounds {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (F : Finset ℕ) (J : ℕ)
    (hF : ∀n∈F,continuedRoot (b:ℂ)^(n+1)≠1 ∨ (1≤n ∧ 2*(J+1)≤(n+1)*n)) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ∀n∈F,∀j≤J,
      ‖iteratedDeriv j (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
        (Complex.I*(t:ℂ)^2)‖≤C := by
  let f := fun (v : ℕ × ℕ) (eta : E) (t : ℝ) =>
    iteratedDeriv v.2 (angularCoefficient v.1 b (fun u=>B (u,eta)) (fun u=>S (u,eta))) (Complex.I*(t:ℂ)^2)
  have hall : ∀v∈F ×ˢ Finset.range (J+1),∃δ C : ℝ,0<δ ∧ 0≤C ∧
      ∀eta∈Q,∀t : ℝ,0<t → t<δ → ‖f v eta t‖≤C := by
    intro v hv
    obtain ⟨hn,hj⟩ := Finset.mem_product.mp hv
    have hjJ : v.2≤J := by simpa using hj
    rcases hF v.1 hn with hnr|hh
    · obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_family_nonresonant_coefficient_bound B S hb hQ hB hBi hS hS0 hnr v.2
      refine ⟨Real.sqrt δ,C,Real.sqrt_pos.mpr hδ,hC,?_⟩
      intro eta heta t ht htd
      have htsq : t^2<δ := by nlinarith [Real.sq_sqrt hδ.le]
      have hi : 0<(Complex.I*(t:ℂ)^2).im := by
        simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
          Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
        positivity
      exact hbound eta heta _ (by simpa using htsq) hi
    · exact compact_family_higher_coefficient_bound hh.1 (by omega) B S hb hQ hB hBi hS hS0
  obtain ⟨δ,C,hδ,hC,hbound⟩ := finite_common_bound (F ×ˢ Finset.range (J+1)) Q f hall
  exact ⟨δ,C,hδ,hC,fun eta heta t ht htd n hn j hj =>
    hbound eta heta t ht htd (n,j) (Finset.mem_product.mpr ⟨hn,Finset.mem_range.mpr (by omega)⟩)⟩

/-- The COMPLETE finite regular remainder, not only each summand, is uniformly
bounded together with every derivative through the selected order. -/
theorem compact_family_finite_derivative_sum_bound {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (F : Finset ℕ) (J : ℕ)
    (hF : ∀n∈F,continuedRoot (b:ℂ)^(n+1)≠1 ∨ (1≤n ∧ 2*(J+1)≤(n+1)*n)) :
    ∃δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ → ∀j≤J,
      (∑n∈F,‖iteratedDeriv j (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
        (Complex.I*(t:ℂ)^2)‖)≤C := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_family_finite_coefficient_bounds B S hb hQ hB hBi hS hS0 F J hF
  refine ⟨δ,(F.card:ℝ)*C,hδ,by positivity,?_⟩
  intro eta heta t ht htd j hj
  simpa using Finset.sum_le_sum (fun n hn=>hbound eta heta t ht htd n hn j hj)

end
end IsingBulk.Joint.RegularEdges
