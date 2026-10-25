import IsingBulk.Joint.FormFactors.Normalized
import IsingBulk.Joint.Geometry.Basic

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set

/-- The physical principal branch remains analytic at every noncritical boundary
point. This is proved from the literal domain modulus inequality. -/
theorem one_sub_sq_slit_of_norm_le {v : ℂ} (hv : ‖v‖≤1) (hp : v^2≠1) :
    1-v^2∈Complex.slitPlane := by
  have hn : ‖v^2‖≤1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg v) hv
  by_cases hi : (v^2).im=0
  · have hr : (v^2).re<1 := lt_of_le_of_ne ((Complex.re_le_norm _).trans hn) (by
      intro he
      apply hp
      apply Complex.ext
      · simpa using he
      · simpa using hi)
    exact Or.inl (by simpa using sub_pos.mpr hr)
  · exact Or.inr (by simpa using hi)

theorem norm_p_le_one_of_closure_high {K : Coupling} (hK : K∈closure highDomain) : ‖p K‖≤1 := by
  have hc : IsClosed {L : Coupling | ‖p L‖≤1} := isClosed_le continuous_p.norm continuous_const
  exact closure_minimal (fun L hL => (norm_p_lt_one hL).le) hc hK

theorem one_le_norm_p_of_closure_low {K : Coupling} (hK : K∈closure lowDomain) : 1≤‖p K‖ := by
  have hc : IsClosed {L : Coupling | 1≤‖p L‖} := isClosed_le continuous_const continuous_p.norm
  exact closure_minimal (fun L hL => (one_lt_norm_p hL).le) hc hK

theorem highPrefactor_boundary_analyticAt {K : Coupling}
    (hK : K∈closure highDomain) (hp : p K^2≠1) :
    AnalyticAt ℂ FormFactors.highPrefactor K :=
  (FormFactors.fourthRoot_analyticAt
    (one_sub_sq_slit_of_norm_le (norm_p_le_one_of_closure_high hK) hp)).comp
      (f := fun L => 1-p L^2)
      (analyticAt_const.sub ((FormFactors.p_analyticAt_normalized K).pow 2))

theorem lowPrefactor_boundary_analyticAt {K : Coupling}
    (hK : K∈closure lowDomain) (hp : p K^2≠1) :
    AnalyticAt ℂ FormFactors.lowPrefactor K := by
  have hn := one_le_norm_p_of_closure_low hK
  have hp0 : p K≠0 := norm_pos_iff.mp (zero_lt_one.trans_le hn)
  have hi : ‖(p K)⁻¹‖≤1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hn
  have hi2 : ((p K)⁻¹)^2≠1 := by
    intro he
    apply hp
    have hh := congrArg Inv.inv he
    simpa only [inv_pow,inv_inv,inv_one] using hh
  exact (FormFactors.fourthRoot_analyticAt (one_sub_sq_slit_of_norm_le hi hi2)).comp
    (f := fun L => 1-(p L)⁻¹^2)
    (analyticAt_const.sub (((FormFactors.p_analyticAt_normalized K).inv hp0).pow 2))

end
end IsingBulk.Joint.RegularEdges
