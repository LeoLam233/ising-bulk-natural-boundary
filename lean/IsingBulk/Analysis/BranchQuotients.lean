import IsingBulk.Analysis.BranchSeparated

namespace IsingBulk.Branch
noncomputable section

theorem separated_quotient_algebra (A B D s t c C : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < s) (ht : 0 < t) (hc : 0 < c) (hC : 0 < C)
    (hAb : A ≤ C/s) (hBb : B ≤ C/t) (hD : c/s ≤ D) :
    0 < D ∧ A*B/D ≤ (C^2/c)/t := by
  have hDp : 0 < D := (div_pos hc hs).trans_le hD
  refine ⟨hDp,?_⟩
  have hprod : A*B ≤ (C/s)*(C/t) := mul_le_mul hAb hBb hB (by positivity)
  calc
    _ ≤ ((C/s)*(C/t))/(c/s) := div_le_div₀ (by positivity) hprod (div_pos hc hs) hD
    _ = _ := by field_simp

theorem OriginalQuotientData.separated_quotient {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hm : 0 ≤ m)
    (hmM : m ≤ M/2) (hMr : M < B.r) (hsep : B.separationThreshold*ε ≤ M) :
    0 < deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M ∧
    ‖deriv (originalPhase d ε) m*deriv (originalPhase d ε) M‖ /
      (deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M) ≤
      (B.C^2/min (B.k/4) (B.a/2))/Real.sqrt M := by
  have hM : 0 < M := (mul_pos B.separationThreshold_pos hε).trans_le hsep
  have hme : 0 < m+ε := by linarith
  have hMe : 0 < M+ε := by linarith
  have hk := B.k_pos
  have ha := B.a_pos
  have hdiff := B.separated_difference ε m M hε hεr hm hmM hMr hsep
  have hm_bound := B.magnitude ε m hε hεr hm (by linarith)
  have hM_bound := B.magnitude ε M hε hεr hM.le hMr
  obtain ⟨hpos,hbound⟩ := separated_quotient_algebra _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (Real.sqrt_pos.mpr hme) (Real.sqrt_pos.mpr hMe) (by positivity) B.C_pos hm_bound hM_bound hdiff
  refine ⟨hpos,?_⟩
  rw [norm_mul]
  exact hbound.trans (div_le_div₀ (by positivity) le_rfl (Real.sqrt_pos.mpr hM)
    (Real.sqrt_le_sqrt (by linarith)))

theorem OriginalQuotientData.comparable_quotient {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hscale : B.C₀*ε ≤ m)
    (hmhalf : M/2 < m) (hmM : m < M) (hMr : M < B.r) :
    0 < deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M ∧
    ‖deriv (originalPhase d ε) m*deriv (originalPhase d ε) M‖ /
      (deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M) ≤
      (2*B.C^2/B.k)*Real.sqrt M/(M-m) := by
  have hm : 0 < m := (mul_pos B.C₀_pos hε).trans_le hscale
  have hM : 0 < M := hm.trans hmM
  have hme : 0 < m+ε := by linarith
  have hMe : 0 < M+ε := by linarith
  have hC := B.C_pos
  have hk := B.k_pos
  have hdrop := B.slope_drop ε m M hε hεr hscale hmM hMr
  have hdrop_pos : 0 < B.k*(M-m)/(M*Real.sqrt M) := by positivity
  have hpos := hdrop_pos.trans_le hdrop
  have hm_bound := B.magnitude ε m hε hεr hm.le (hmM.trans hMr)
  have hM_bound := B.magnitude ε M hε hεr hM.le hMr
  have hsM := Real.sqrt_pos.mpr hM
  have hsme := Real.sqrt_pos.mpr hme
  have hsqrt : Real.sqrt M ≤ 2*Real.sqrt (m+ε) := by
    nlinarith [Real.sq_sqrt hM.le,Real.sq_sqrt hme.le]
  have hmb : ‖deriv (originalPhase d ε) m‖ ≤ 2*B.C/Real.sqrt M := by
    apply hm_bound.trans
    apply (div_le_div_iff₀ hsme hsM).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hC.le]
  have hMb : ‖deriv (originalPhase d ε) M‖ ≤ B.C/Real.sqrt M :=
    hM_bound.trans (div_le_div₀ hC.le le_rfl hsM (Real.sqrt_le_sqrt (by linarith)))
  have hprod : ‖deriv (originalPhase d ε) m*deriv (originalPhase d ε) M‖ ≤ 2*B.C^2/M := by
    rw [norm_mul]
    have h := mul_le_mul hmb hMb (norm_nonneg _) (by positivity)
    have he : (2*B.C/Real.sqrt M)*(B.C/Real.sqrt M) = 2*B.C^2/M := by
      calc
        _ = 2*B.C^2/(Real.sqrt M)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hM.le]
    exact h.trans_eq he
  refine ⟨hpos,?_⟩
  calc
    _ ≤ (2*B.C^2/M)/(B.k*(M-m)/(M*Real.sqrt M)) :=
      div_le_div₀ (by positivity) hprod hdrop_pos hdrop
    _ = _ := by field_simp

end
end IsingBulk.Branch
