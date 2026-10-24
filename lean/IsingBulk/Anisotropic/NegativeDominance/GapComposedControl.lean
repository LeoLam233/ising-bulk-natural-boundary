import IsingBulk.Anisotropic.NegativeDominance.GapFullDiskControl
import IsingBulk.Anisotropic.NegativeDominance.AnalyticCoordinateControl

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set

/-- The a/N disk and complete density estimate survive the actual analytic
paper-to-edge reparametrization, without identifying the two coordinates. -/
theorem composed_fullIntegrand_disk_of_boundary_gap {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃a r C M K : ℝ,0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,(∀i,q i∈Icc (-Real.pi) Real.pi) →
      κ≤‖1-edgeRootProduct b B 0 q‖ → ∀u : ℂ,‖u‖<a/(N : ℝ) →
      AnalyticAt ℂ (fun w=>edgeFullIntegrand b B S (f w) q) u ∧
        ‖edgeFullIntegrand b B S (f u) q‖≤K*particleEdgeMajorant r C M N := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ := fullIntegrand_disk_of_boundary_gap hb hB hBa hSa hS0 κ hκ
  obtain ⟨δ,L,hδ,hL,hcoord⟩ := analytic_zero_uniform_linear_bound hf hf0
  let a' := min δ (a/L)
  have ha' : 0<a' := lt_min hδ (by positivity)
  refine ⟨a',r,C,M,K,ha',hr,hr1,hC,hM,hK,?_⟩
  intro N hN q hq hgap u hu
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have huδ : ‖u‖<δ := by
    have hh : a'/(N : ℝ)≤a' := (div_le_iff₀ hNp).mpr (by nlinarith)
    exact hu.trans_le (hh.trans (min_le_left _ _))
  obtain ⟨hfa,hfnorm⟩ := hcoord u huδ
  have hfu : ‖f u‖<a/(N : ℝ) := by
    have hh := mul_lt_mul_of_pos_left hu hL
    have hLa : L*a'≤a := by have h := (le_div_iff₀ hL).mp (min_le_right δ (a/L)); nlinarith
    have hscaled := div_le_div_of_nonneg_right hLa hNp.le
    have he : L*(a'/(N : ℝ))=L*a'/(N : ℝ) := by ring
    rw [he] at hh
    exact hfnorm.trans_lt (hh.trans_le hscaled)
  obtain ⟨hA,hbound⟩ := hcontrol N hN q hq hgap (f u) hfu
  exact ⟨hA.comp hfa,hbound⟩

end
end IsingBulk.Anisotropic.NegativeDominance
