import IsingBulk.Tail.ScaledAnalyticProductJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Tail
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem squared_linear_jet_norm (L : E →L[ℂ] ℂ) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun y => (L y)^2) x‖ ≤
      ((2).descFactorial k : ℝ)*‖L x‖^(2-k)*‖L‖^k := by
  have he := L.iteratedFDeriv_comp_right (contDiff_id.pow 2) x (i := k) (n := ⊤) (by simp)
  change iteratedFDeriv ℂ k (fun y => (L y)^2) x = _ at he
  rw [he]
  have hh := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℂ k (fun z : ℂ => z^2) (L x)) (fun _ : Fin k => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  apply hh.trans_eq
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_pow,norm_mul,norm_pow]
  simp

theorem squared_linear_scaled_jets (L : E →L[ℂ] ℂ) (x : E) (R : ℝ)
    (hR : 0 < R) (hL : ‖L‖ ≤ 2) (hx : ‖L x‖ ≤ 2*R) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun y => (L y)^2) x‖ ≤ 8*R^((2:ℤ)-(k:ℤ)) := by
  have hh := squared_linear_jet_norm L x k
  rcases k with _|_|_|k
  · norm_num at hh ⊢
    nlinarith [norm_nonneg (L x),sq_nonneg R]
  · norm_num at hh ⊢
    nlinarith [norm_nonneg L,norm_nonneg (L x),mul_le_mul hx hL (norm_nonneg L) (by positivity : 0 ≤ 2*R)]
  · norm_num at hh ⊢
    nlinarith [sq_nonneg (‖L‖-2),norm_nonneg L]
  · have hz : (2).descFactorial (k+3)=0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hz,Nat.cast_zero,zero_mul,zero_mul] at hh
    exact hh.trans (by positivity)

end
end IsingBulk.Tail
