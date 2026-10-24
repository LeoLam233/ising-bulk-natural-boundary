import IsingBulk.Anisotropic.NegativeNormalForm.TripleScalarIdentity
import IsingBulk.Anisotropic.NegativeNormalForm.PoleNewton

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

 theorem phaseFirstFactor_origin (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) :
    phaseFirstFactor B phi hphi 0 0 0=0 := by
  simp [phaseFirstFactor,cosineFirstFactor,zeroSlope_zero,Complex.deriv_cos]

/-- The actual angular phase has arbitrarily small Lipschitz constant near the origin. -/
 theorem negativePhase_uniform_angular_small (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t d x y : ℂ,
      ‖t‖<δ → ‖d‖<δ → ‖x‖<δ → ‖y‖<δ →
      ‖negativePhase B phi hphi t (d+x)-negativePhase B phi hphi t (d+y)‖≤ε*‖x-y‖ := by
  have hs : ∀ᶠ p : ScalarTriple in 𝓝 0, ‖phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2‖<ε :=
    (phaseFirstFactor_triple_analyticAt B phi hphi hB).continuousAt.norm.eventually_lt
      continuousAt_const (by simpa [phaseFirstFactor_origin] using hε)
  have he : ∀ᶠ p : ScalarTriple in 𝓝 0,
      phaseIncrement B phi hphi p.2.1 p.1 p.2.2=p.2.2*phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2 ∧
      ‖phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2‖<ε := by
    filter_upwards [phase_factors_triple_eventually B phi hphi hB,hs] with p hp hps using ⟨hp.1,hps⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/4,by positivity,?_⟩
  intro t d x y ht hd hx hy
  have hinput : ‖(t,(d+y,x-y))‖<r := by
    change max ‖t‖ (max ‖d+y‖ ‖x-y‖)<r
    have hdy := norm_add_le d y
    have hxy := norm_sub_le x y
    exact max_lt (by linarith) (max_lt (by linarith) (by linarith))
  have hh := hball (show (t,(d+y,x-y))∈ball (0:ScalarTriple) r by simpa using hinput)
  have hid : d+y+(x-y)=d+x := by ring
  have hid' := hh.1
  simp only [phaseIncrement,hid] at hid'
  rw [hid',norm_mul]
  exact (mul_le_mul_of_nonneg_left hh.2.le (norm_nonneg _)).trans_eq (mul_comm _ _)

 theorem poleAverage_difference_eq_mean {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v w : Config n) :
    poleAverage B phi hphi d t v-poleAverage B phi hphi d t w=
      mean (fun i => negativePhase B phi hphi t (d+v i)-negativePhase B phi hphi t (d+w i)) := by
  unfold poleAverage poleEquation mean
  rw [← sub_div,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem poleAverage_angular_bound {n : ℕ} (hn : n≠0) (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v w : Config n) (ε : ℝ) (hε : 0≤ε)
    (he : ∀ i, ‖negativePhase B phi hphi t (d+v i)-negativePhase B phi hphi t (d+w i)‖≤ε*‖v i-w i‖) :
    ‖poleAverage B phi hphi d t v-poleAverage B phi hphi d t w‖≤ε*‖v-w‖ := by
  rw [poleAverage_difference_eq_mean]
  apply (norm_mean_le hn _).trans
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact (he i).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (v-w) i) hε)

end
end IsingBulk.Anisotropic.NegativeNormalForm
