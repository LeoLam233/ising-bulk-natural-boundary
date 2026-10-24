import IsingBulk.Anisotropic.NegativeCycles.JointResidueAnalytic
import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedWitness

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped Topology

/-- Full-ball residue holomorphy for every actually constructed pole, uniformly in N. -/
theorem actualResidue_uniform_analyticOnNhd (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C : ℝ) (hr : 0<r) :
    ∃δ : ℝ,0<δ ∧ δ≤r ∧ ∀m : ℕ, ∀d : ℂ, ‖d‖<δ →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) d r C,
      AnalyticOnNhd ℂ (poleResidue B rootB phi hphi d P.T) (ball 0 δ) := by
  obtain ⟨a,ha,hres⟩ := poleResidue_local_uniform_analytic B rootB phi hphi hB hroot hBn
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
  intro m d hd P v hv
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
  apply hres m d P.T v (P.t_analytic v (by simpa using hvR)) htA
  intro i
  have hh := norm_add_le d (v i)
  have hi := norm_le_pi_norm v i
  linarith

end IsingBulk.Anisotropic.NegativeCycles
