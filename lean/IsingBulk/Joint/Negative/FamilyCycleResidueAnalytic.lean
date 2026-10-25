import IsingBulk.Joint.Negative.FamilyCycleDensityAnalytic
import IsingBulk.Joint.Negative.FamilyWindingSlope
import IsingBulk.Anisotropic.NegativeCycles.ActualResidueAnalytic

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_cycle_residue_analytic (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) :
    ∃r : ℝ,0<r ∧ ∀ eta∈Q, ∀m : ℕ, ∀d : ℂ, ∀T : Config (2*m+1)→ℂ,
      ∀v : Config (2*m+1), AnalyticAt ℂ T v → ‖T v‖<r →
      (∀i, ‖d+v i‖<r) → AnalyticAt ℂ (poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi d T) v := by
  obtain ⟨a,ha,hjoint⟩ := compact_family_cycle_density_joint_analytic B rootB phi hphi hQ hB hroot
  obtain ⟨b,c,hb,hc,hslope⟩ := compact_family_pole_derivative_lower B phi hphi hQ hB hBn
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro eta heta m d T v hT ht hv
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  obtain ⟨hN,hF⟩ := hjoint eta heta m d (T v) v (ht.trans_le (min_le_left _ _))
    (fun i => (hv i).trans_le (min_le_left _ _))
  have hD := poleParameterDerivative_joint_analyticAt B phi hphi d (T v) v hF
  have hg : AnalyticAt ℂ (fun w => (w,T w)) v := analyticAt_id.prod hT
  have hn : 2*m+1≠0 := by omega
  have hbnd := hslope eta heta (2*m+1) hn d (T v) v (ht.trans_le (min_le_right _ _))
    (fun i => (hv i).trans_le (min_le_right _ _))
  have hDn : poleParameterDerivative B phi hphi d (T v) v≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le (mul_pos hc (by positivity)) hbnd)
  have hNc : AnalyticAt ℂ (fun w => formFactorNumerator B rootB phi hphi d (T w) w) v :=
    hN.comp_of_eq (f := fun w : Config (2*m+1) => (w,T w)) hg rfl
  have hDc : AnalyticAt ℂ (fun w => poleParameterDerivative B phi hphi d (T w) w) v :=
    hD.comp_of_eq (f := fun w : Config (2*m+1) => (w,T w)) hg rfl
  exact (analyticAt_const.mul hNc).div hDc hDn


theorem compact_family_actualResidue_analyticOnNhd (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C : ℝ) (hr : 0<r) :
    ∃δ : ℝ,0<δ ∧ δ≤r ∧ ∀ eta∈Q, ∀m : ℕ, ∀d : ℂ, ‖d‖<δ →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) d r C,
      AnalyticOnNhd ℂ (poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi d P.T) (ball 0 δ) := by
  obtain ⟨a,ha,hres⟩ := compact_family_cycle_residue_analytic B rootB phi hphi hQ hB hroot hBn
  have ht : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
  have he : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<a/2 :=
    ht.norm.eventually_lt continuousAt_const (by simpa using half_pos ha)
  obtain ⟨b,hb,hbs⟩ := Metric.mem_nhds_iff.mp he
  let δ := min r (min (a/4) b)
  have hδ : 0<δ := lt_min hr (lt_min (by positivity) hb)
  have hδr : δ≤r := min_le_left _ _
  have hδa : δ≤a/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ≤b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,hδr,?_⟩
  intro eta heta m d hd P v hv
  have hv' : ‖v‖<δ := by simpa using hv
  have hvR : ‖v‖<2*r := by linarith
  have htau := hbs (show d∈ball (0:ℂ) b by simpa using hd.trans_le hδb)
  change ‖1-Complex.cos d‖<a/2 at htau
  have hl := P.t_lip v 0 hvR (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hr)
  rw [P.t_zero,sub_zero] at hl
  have htA : ‖P.T v‖<a := by
    have hh := norm_add_le (P.T v-(1-Complex.cos d)) (1-Complex.cos d)
    rw [sub_add_cancel] at hh
    linarith
  apply hres eta heta m d P.T v (P.t_analytic v (by simpa using hvR)) htA
  intro i
  have hh := norm_add_le d (v i)
  have hi := norm_le_pi_norm v i
  linarith


end
end IsingBulk.Joint.Negative
