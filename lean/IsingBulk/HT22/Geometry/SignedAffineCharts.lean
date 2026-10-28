import IsingBulk.HT22.Geometry.FiniteComplementPartition
import IsingBulk.Preferred22.FiniteEquality

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set IsingBulk.Preferred22 IsingBulk.First
open scoped BigOperators

/-- Translating the actual free variables gives the exact zero-sum shape
chart, including the eliminated last angle and the signed total. -/
theorem constrainedAtTotal_translate_mean (n : ℕ) (c : ℝ) (u : Fin n → ℝ) :
    constrainedAtTotal c (fun i => c/((n+1:ℕ):ℝ)+u i)=
      fun j => c/((n+1:ℕ):ℝ)+shapeExtend u j := by
  have hN : ((n+1:ℕ):ℝ)≠0 := by positivity
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [constrainedAtTotal,shapeExtend,Fin.snoc_last,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    field_simp
    ring
  · simp only [constrainedAtTotal,shapeExtend,Fin.snoc_castSucc]

/-- The balanced contour fixes every equality center exactly, for every
signed constraint and every occupancy bump. -/
theorem signed_balanced_chart_center (n : ℕ) (a τ : ℝ) (l : ℤ) (p m : ℝ → ℝ) :
    deformedAngles τ p m
      (constrainedAtTotal (a+2*Real.pi*(l:ℝ))
        (fun _ : Fin n => (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ))) =
      fun _ => ((a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ):ℂ) := by
  have he := constrainedAtTotal_translate_mean n (a+2*Real.pi*(l:ℝ)) (0:Fin n → ℝ)
  have hz : shapeExtend (0:Fin n → ℝ)=0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [shapeExtend]
  simp only [hz,Pi.zero_apply,add_zero] at he
  rw [he]
  funext i
  simp only [deformedAngles,balancedShift_at_equality,Complex.ofReal_zero,mul_zero,sub_zero,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_intCast,Complex.ofReal_natCast]

end
end IsingBulk.HT22.Geometry
