import IsingBulk.Anisotropic.NegativeNormalForm.TripleScalarAnalytic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology

theorem analytic_scalarTriple_uniform_lipschitz {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ScalarTriple → F} (hf : AnalyticAt ℂ f 0) :
    ∃ r L M : ℝ, 0<r ∧ 0<L ∧ 0<M ∧
      (∀ p : ScalarTriple, ‖p‖<r → AnalyticAt ℂ f p ∧ ‖f p‖≤M) ∧
      (∀ p q : ScalarTriple, ‖p‖<r → ‖q‖<r → ‖f p-f q‖≤L*‖p-q‖) := by
  obtain ⟨L,s,hs,hL⟩ := (hf.contDiffAt (n := 1)).exists_lipschitzOnWith
  have hb : ∀ᶠ p in 𝓝 (0:ScalarTriple), ‖f p‖<‖f 0‖+1 :=
    hf.continuousAt.norm.eventually_lt continuousAt_const (by linarith)
  have he : ∀ᶠ p in 𝓝 (0:ScalarTriple), p∈s ∧ AnalyticAt ℂ f p ∧ ‖f p‖<‖f 0‖+1 := by
    filter_upwards [hs,hf.eventually_analyticAt,hb] with p hp ha hb
    exact ⟨hp,ha,hb⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r,(L:ℝ)+1,‖f 0‖+1,hr,by positivity,by positivity,?_,?_⟩
  · intro p hp
    have hh := hball (show p∈ball (0:ScalarTriple) r by simpa using hp)
    exact ⟨hh.2.1,hh.2.2.le⟩
  · intro p q hp hq
    have hp' := (hball (show p∈ball (0:ScalarTriple) r by simpa using hp)).1
    have hq' := (hball (show q∈ball (0:ScalarTriple) r by simpa using hq)).1
    have hh := hL.dist_le_mul p hp' q hq'
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

theorem phaseFactors_uniform_triple_bounds (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ r L M : ℝ, 0<r ∧ 0<L ∧ 0<M ∧
      (∀ p : ScalarTriple, ‖p‖<r →
        AnalyticAt ℂ (fun x : ScalarTriple => phaseFirstFactor B phi hphi x.2.1 x.1 x.2.2) p ∧
        AnalyticAt ℂ (fun x : ScalarTriple => phaseSecondFactor B phi hphi x.2.1 x.1 x.2.2) p ∧
        ‖phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2‖≤M ∧
        ‖phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2‖≤M) ∧
      (∀ p q : ScalarTriple, ‖p‖<r → ‖q‖<r →
        ‖phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2-
          phaseFirstFactor B phi hphi q.2.1 q.1 q.2.2‖≤L*‖p-q‖ ∧
        ‖phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2-
          phaseSecondFactor B phi hphi q.2.1 q.1 q.2.2‖≤L*‖p-q‖) := by
  let F : ScalarTriple → ℂ × ℂ := fun p =>
    (phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2,
      phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2)
  have ha : AnalyticAt ℂ F 0 :=
    (phaseFirstFactor_triple_analyticAt B phi hphi hB).prod
      (phaseSecondFactor_triple_analyticAt B phi hphi hB)
  obtain ⟨r,L,M,hr,hL,hM,hf,hlip⟩ := analytic_scalarTriple_uniform_lipschitz ha
  refine ⟨r,L,M,hr,hL,hM,?_,?_⟩
  · intro p hp
    have hh := hf p hp
    exact ⟨analyticAt_fst.comp hh.1,analyticAt_snd.comp hh.1,
      (norm_fst_le (F p)).trans hh.2,(norm_snd_le (F p)).trans hh.2⟩
  · intro p q hp hq
    have hh := hlip p q hp hq
    exact ⟨(norm_fst_le (F p-F q)).trans hh,(norm_snd_le (F p-F q)).trans hh⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
