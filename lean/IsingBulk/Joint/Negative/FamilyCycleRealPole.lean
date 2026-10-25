import IsingBulk.Joint.Negative.FamilyCycleHomotopy
import IsingBulk.Anisotropic.NegativeCycles.RealPolePositivity

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_real_pole_positive (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hBn : ∀ eta∈Q, B (0,eta)≠0)
    (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ : ℝ,0<ρ ∧ ∀ eta∈Q, ∀n : ℕ,n≠0 → ∀d : ℝ,|d|<ρ → d≠0 →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi n (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness (familyMember B eta) phi hphi n (d:ℂ) r C P R,
      ∀v : Fin n→ℝ, ‖fun i => (v i:ℂ)‖≤ρ → (∑i,v i)=0 →
      0<1-Real.cos d ∧ 1-Real.cos d≤(P.T (fun i => (v i:ℂ))).re := by
  obtain ⟨a,ha,_har,hsec⟩ := compact_family_actualHomotopy_pole_sector B phi hphi hQ hB hBn r C R hr hR hRr
  let ρ := min a (Real.pi/2)
  have hρ : 0<ρ := lt_min ha (by positivity)
  have hρa : ρ≤a := min_le_left _ _
  have hρpi : ρ≤Real.pi/2 := min_le_right _ _
  refine ⟨ρ,hρ,?_⟩
  intro eta heta n hn d hd hd0 P J v hv hm
  let B := familyMember B eta
  have htau : 0<1-Real.cos d := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by norm_num)
      (show |d|≤Real.pi by linarith) (abs_pos.mpr hd0)
    simpa only [Real.cos_abs,Real.cos_zero,sub_pos] using hh
  have hh := hsec eta heta n hn d (by simpa using hd.trans_le hρa) P J v (hv.trans hρa) hm 0
    (by constructor <;> norm_num)
  simp only [correctedHomotopy,Complex.ofReal_zero,zero_smul,add_zero] at hh
  refine ⟨htau,?_⟩
  have hnon : 0≤(∑i,v i^2)/(8*n) := by positivity
  linarith

end
end IsingBulk.Joint.Negative
