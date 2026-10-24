import IsingBulk.Anisotropic.NegativeNormalForm.ComplexPeriodLoss

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance

theorem positive_period_norm_eq_complex_mul_loss {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    (j : ℕ) (haj : alpha p≤j) (h : ℂ) (hh : 0<h.re) :
    ‖shapePeriod (p-1) j (tau p) ((h.re/(2*(p:ℝ)):ℝ):ℂ)‖=
      ‖shapePeriod (p-1) j (tau p) (h/(2*(p:ℂ)))‖*(‖h‖/h.re)^(alpha p) := by
  have hn : h≠0 := by intro he; simp [he] at hh
  have hnr : ‖h‖≠0 := norm_ne_zero_iff.mpr hn
  have hc : ((h.re/(2*(p:ℝ)):ℝ):ℂ)=(h.re:ℂ)/(2*(p:ℂ)) := by push_cast; rfl
  rw [hc,negativeEdge_complex_period hp hp3 j haj (h.re:ℂ) (by simpa using hh),
    negativeEdge_complex_period hp hp3 j haj h hh]
  simp only [zpow_neg,zpow_natCast,norm_mul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hh,div_pow]
  field_simp [hnr,hh.ne']

end
end IsingBulk.Anisotropic.NegativeNormalForm
