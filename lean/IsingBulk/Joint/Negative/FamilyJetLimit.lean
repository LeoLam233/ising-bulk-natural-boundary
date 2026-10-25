import IsingBulk.Joint.Negative.FamilySeriesLimit
import IsingBulk.Joint.Negative.CompactAnalyticBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open IsingBulk.First
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Joint analyticity gives genuinely uniform finite-term approach, including
all fixed transverse jets, on a compact complex parameter set. -/
theorem compact_analytic_negative_real_limit (f : ℂ × E→ℂ) {Q : Set E}
    (hQ : IsCompact Q) (hf : ∀eta∈Q,AnalyticAt ℂ f (0,eta)) :
    TendstoUniformlyOn (fun ε : ℝ=>fun eta=>f (-(ε:ℂ),eta))
      (fun eta=>f (0,eta)) (𝓝[>] 0) Q := by
  obtain ⟨r,L,M,hr,hL,_hM,_hb,hLip⟩ := compact_analytic_uniform_lipschitz f hQ hf
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0<min r (ε/L) := lt_min hr (div_pos hε hL)
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht eta heta
  have htn : ‖-(t:ℂ)‖=t := by simp only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
  have hh := hLip eta heta (-(t:ℂ)) 0 (by rw [htn]; exact ht.2.trans_le (min_le_left _ _))
    (by simpa only [norm_zero] using hr)
  rw [sub_zero,htn] at hh
  rw [dist_comm,dist_eq_norm]
  apply hh.trans_lt
  have htε := ht.2.trans_le (min_le_right r (ε/L))
  exact (mul_lt_mul_of_pos_left htε hL).trans_eq (mul_div_cancel₀ ε hL.ne')

theorem compact_analytic_negative_real_jet_limit (f : ℂ × E→ℂ) {Q : Set E}
    (hQ : IsCompact Q) (hf : ∀eta∈Q,AnalyticAt ℂ f (0,eta)) (j : ℕ) :
    TendstoUniformlyOn (fun ε : ℝ=>fun eta=>iteratedDeriv j (fun t=>f (t,eta)) (-(ε:ℂ)))
      (fun eta=>iteratedDeriv j (fun t=>f (t,eta)) 0) (𝓝[>] 0) Q := by
  simpa only [jointParameterJet_eq,iteratedDeriv_eq_iterate] using
    compact_analytic_negative_real_limit (jointParameterJet f j) hQ
      (fun eta heta=>jointParameterJet_analyticAt (hf eta heta) j)

end
end IsingBulk.Joint.Negative
