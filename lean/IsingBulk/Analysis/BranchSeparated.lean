import IsingBulk.Analysis.BranchQuotientData

/-! The full separated-extremes range, including m below the concavity scale. -/
namespace IsingBulk.Branch
noncomputable section

theorem OriginalQuotientData.slope_antitone {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hscale : B.C₀*ε ≤ m)
    (hmM : m ≤ M) (hMr : M < B.r) :
    deriv (originalRealPhase d ε) M ≤ deriv (originalRealPhase d ε) m := by
  rcases hmM.eq_or_lt with rfl | hmM
  · exact le_rfl
  have hm : 0 < m := (mul_pos B.C₀_pos hε).trans_le hscale
  have hM : 0 < M := hm.trans hmM
  have h := B.slope_drop ε m M hε hεr hscale hmM hMr
  have hp : 0 ≤ B.k*(M-m)/(M*Real.sqrt M) := by have := B.k_pos; positivity
  linarith

theorem OriginalQuotientData.large_separation {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hscale : B.C₀*ε ≤ m)
    (hmM : m ≤ M/2) (hMr : M < B.r) :
    (B.k/4)/Real.sqrt (m+ε) ≤
      deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M := by
  have hm : 0 < m := (mul_pos B.C₀_pos hε).trans_le hscale
  have hm2r : 2*m < B.r := by linarith
  have hd := B.slope_drop ε m (2*m) hε hεr hscale (by linarith) hm2r
  have ha := B.slope_antitone ε (2*m) M hε hεr (by linarith) (by linarith) hMr
  have hsm := Real.sqrt_pos.mpr hm
  have hsm2 := Real.sqrt_pos.mpr (show 0 < 2*m by linarith)
  have hsq : Real.sqrt (2*m) ≤ 2*Real.sqrt m := by
    nlinarith [Real.sq_sqrt hm.le,Real.sq_sqrt (show 0 ≤ 2*m by linarith)]
  have he : B.k*(2*m-m)/((2*m)*Real.sqrt (2*m)) = B.k/(2*Real.sqrt (2*m)) := by field_simp; ring
  rw [he] at hd
  have hlo : B.k/(4*Real.sqrt m) ≤ B.k/(2*Real.sqrt (2*m)) :=
    div_le_div₀ B.k_pos.le le_rfl (by positivity) (by linarith)
  have hs : Real.sqrt m ≤ Real.sqrt (m+ε) := Real.sqrt_le_sqrt (by linarith)
  have hlo' : (B.k/4)/Real.sqrt (m+ε) ≤ B.k/(4*Real.sqrt m) := by
    rw [div_div]
    exact div_le_div₀ B.k_pos.le le_rfl (by positivity) (by nlinarith)
  linarith

def OriginalQuotientData.separationThreshold {d : LocalBranchData} (B : OriginalQuotientData d) : ℝ :=
  4*B.C^2*(B.C₀+1)/B.a^2

theorem OriginalQuotientData.separationThreshold_pos {d : LocalBranchData} (B : OriginalQuotientData d) :
    0 < B.separationThreshold := by
  have := B.a_pos
  have := B.C_pos
  have := B.C₀_pos
  dsimp [separationThreshold]
  positivity

theorem OriginalQuotientData.small_separation {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hm : 0 ≤ m)
    (hscale : m ≤ B.C₀*ε) (hmM : m ≤ M) (hMr : M < B.r)
    (hsep : B.separationThreshold*ε ≤ M) :
    (B.a/2)/Real.sqrt (m+ε) ≤
      deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M := by
  have ha := B.a_pos
  have hC := B.C_pos
  have hM : 0 < M := (mul_pos B.separationThreshold_pos hε).trans_le hsep
  have hme : 0 < m+ε := by linarith
  have hMe : 0 < M+ε := by linarith
  have hmlo := (B.slope ε m hε hεr hm (hmM.trans_lt hMr)).1
  have hMhi := (B.slope ε M hε hεr hM.le hMr).2
  have hR : B.a^2*B.separationThreshold = 4*B.C^2*(B.C₀+1) := by
    dsimp [separationThreshold]
    field_simp
  have hbig : 4*B.C^2*(B.C₀+1)*ε ≤ B.a^2*M := by
    have h := mul_le_mul_of_nonneg_left hsep (sq_nonneg B.a)
    rw [← mul_assoc,hR] at h
    exact h
  have hsquare : (2*B.C*Real.sqrt (m+ε))^2 ≤ (B.a*Real.sqrt (M+ε))^2 := by
    have hs₁ := Real.sq_sqrt hme.le
    have hs₂ := Real.sq_sqrt hMe.le
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : m+ε ≤ (B.C₀+1)*ε) (by positivity : 0 ≤ 4*B.C^2),
      mul_nonneg (sq_nonneg B.a) hε.le]
  have hs : 2*B.C*Real.sqrt (m+ε) ≤ B.a*Real.sqrt (M+ε) :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare
  have hhalf : B.C/Real.sqrt (M+ε) ≤ (B.a/2)/Real.sqrt (m+ε) :=
    (div_le_div_iff₀ (Real.sqrt_pos.mpr hMe) (Real.sqrt_pos.mpr hme)).mpr (by nlinarith)
  have he : B.a/Real.sqrt (m+ε) = 2*((B.a/2)/Real.sqrt (m+ε)) := by ring
  linarith

theorem OriginalQuotientData.separated_difference {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hm : 0 ≤ m)
    (hmM : m ≤ M/2) (hMr : M < B.r) (hsep : B.separationThreshold*ε ≤ M) :
    (min (B.k/4) (B.a/2))/Real.sqrt (m+ε) ≤
      deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M := by
  by_cases hs : B.C₀*ε ≤ m
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)).trans
      (B.large_separation ε m M hε hεr hs hmM hMr)
  · exact (div_le_div_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)).trans
      (B.small_separation ε m M hε hεr hm (le_of_not_ge hs) (by linarith) hMr hsep)

end
end IsingBulk.Branch
