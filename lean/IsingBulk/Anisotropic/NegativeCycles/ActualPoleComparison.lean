import IsingBulk.Anisotropic.NegativeCycles.QuadraticPoleComparison
import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedWitness

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped BigOperators Topology

/-- The constructed actual pole satisfies the quadratic comparison on a common ball. -/
theorem actualPole_quadratic_comparison_uniform (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (r C : ℝ) (hr : 0<r) :
    ∃δ : ℝ,0<δ ∧ δ≤r ∧ ∀n : ℕ, n≠0 → ∀d : ℂ, ‖d‖<δ →
      ∀P : UniformProjectedWitness B phi hphi n d r C,
      ∀v : Config n, ‖v‖<δ → ZeroMean v →
      ‖P.T v-(1-Complex.cos d)-quadratic v/(2*n)‖≤absoluteEnergy v/(64*n) := by
  obtain ⟨a,ha,hcmp⟩ := pole_quadratic_comparison_uniform B phi hphi hB hBn
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
  intro n hn d hd P v hv hm
  have hvR : ‖v‖<2*r := by linarith
  have htau := hbs (show d∈ball (0:ℂ) b by simpa using hd.trans_le hδb)
  change ‖1-Complex.cos d‖<a/2 at htau
  have hl := P.t_lip v 0 hvR (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hr)
  rw [P.t_zero,sub_zero] at hl
  have htA : ‖P.T v‖<a := by
    have hn := norm_add_le (P.T v-(1-Complex.cos d)) (1-Complex.cos d)
    rw [sub_add_cancel] at hn
    linarith
  apply hcmp n hn d (P.T v) v (by linarith) htA
  · intro i
    exact (norm_le_pi_norm v i).trans_lt (by linarith)
  · exact hm
  · exact (P.t_pole v hvR).1

end IsingBulk.Anisotropic.NegativeCycles
