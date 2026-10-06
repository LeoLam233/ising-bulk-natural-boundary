import IsingBulk.First.ComplementNormalizedJets
import IsingBulk.First.OnsiteInactiveNeighborhood
import IsingBulk.First.ComplementSourceNormalizedJets

/-! Generated compact-parameter jet amplitudes for the actual localized
normalized double-contour density. -/
namespace IsingBulk.First
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff

def onsiteNormalizedAmplitude {N : ℕ} (ρ v : ℂ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (u : DoubleAngularVector N) : ℂ :=
  normalizedParameterJet (fun z => onsiteRegularAmplitude r z w J u)
    sourceTemperaturePhase ρ v j s

/-- Parameter differentiation cannot enlarge the support of a fixed angular
weight. This is proved for the generated coefficients themselves. -/
theorem onsiteNormalizedAmplitude_eq_zero {N : ℕ} (ρ v : ℂ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (u : DoubleAngularVector N) (hw : w u = 0) :
    onsiteNormalizedAmplitude ρ v r s w J j u = 0 := by
  have ha : (fun z => onsiteRegularAmplitude r z w J u) = fun _ => 0 := by
    funext z
    simp [onsiteRegularAmplitude, hw]
  unfold onsiteNormalizedAmplitude
  rw [ha, normalizedParameterJet_zero]

theorem onsiteNormalizedAmplitude_tsupport_subset {N : ℕ} (ρ v : ℂ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N)) (j : ℕ) :
    tsupport (onsiteNormalizedAmplitude ρ v r s w J j) ⊆ tsupport w := by
  apply closure_mono
  intro u hu
  by_contra hwu
  exact hu (onsiteNormalizedAmplitude_eq_zero ρ v r s w J j u (not_not.mp hwu))

/-- Joint smoothness of the literal generated source amplitude, including
inverse auxiliary radius and normalized dispersion mass as free parameters. -/
theorem onsiteNormalizedAmplitude_joint_contDiffAt {N : ℕ}
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (ρ v : ℂ) (r : ℝ) (s : ℂ)
    (u : DoubleAngularVector N) (hdom : ((r,s),u) ∈ onsiteInactiveDomain J) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun q : ((ℂ × ℂ) × (ℝ × DoubleAngularVector N)) × ℂ =>
      onsiteNormalizedAmplitude q.1.1.1 q.1.1.2 q.1.2.1 q.2 w J j q.1.2.2)
      (((ρ,v),(r,u)),s) := by
  let A : SourceNormalizedParameter N × ℂ → ℂ := fun q => onsiteRegularAmplitude q.1.2.1 q.2 w J q.1.2.2
  let B : SourceNormalizedParameter N × ℂ → ℂ := fun q => sourceTemperaturePhase q.2
  let F : SourceNormalizedParameter N × ℂ → (ℝ × ℂ) × DoubleAngularVector N := fun q => ((q.1.2.1,q.2),q.1.2.2)
  have hF : ContDiff ℝ ∞ F := by unfold F; fun_prop
  have hAA := onsiteRegularAmplitude_joint_contDiffAt w hw J r s u hdom.1 hdom.2.1 hdom.2.2
  have hA : ContDiffAt ℝ ∞ A (((ρ,v),(r,u)),s) := by
    have hh := hAA.comp (((ρ,v),(r,u)),s) (f := F) hF.contDiffAt
    exact hh
  have hB : ContDiffAt ℝ ∞ B (((ρ,v),(r,u)),s) := by
    unfold B sourceTemperaturePhase sourceS
    exact contDiffAt_const.mul (contDiffAt_snd.add (contDiffAt_snd.inv hdom.2.1))
  have hnear : ∀ᶠ q : SourceNormalizedParameter N × ℂ in 𝓝 (((ρ,v),(r,u)),s), F q ∈ onsiteInactiveDomain J :=
    hF.continuous.continuousAt.preimage_mem_nhds (onsiteInactiveDomain_isOpen J |>.mem_nhds hdom)
  have hholA : ∀ᶠ q : SourceNormalizedParameter N × ℂ in 𝓝 (((ρ,v),(r,u)),s),
      AnalyticAt ℂ (fun z => A (q.1,z)) q.2 := by
    filter_upwards [hnear] with q hq
    dsimp only [onsiteInactiveDomain, Set.mem_ofPred_eq, F] at hq
    dsimp only [A]
    exact onsiteRegularAmplitude_analyticAt q.1.2.1 w J q.1.2.2 hq.2.1 hq.2.2
  have hholB : ∀ᶠ q : SourceNormalizedParameter N × ℂ in 𝓝 (((ρ,v),(r,u)),s),
      AnalyticAt ℂ (fun z => B (q.1,z)) q.2 := by
    filter_upwards [hnear] with q hq
    dsimp only [onsiteInactiveDomain, Set.mem_ofPred_eq, F] at hq
    dsimp only [B]
    exact sourceTemperaturePhase_analyticAt hq.2.1
  exact normalizedParameterJet_joint_contDiffAt A B (fun p : SourceNormalizedParameter N => p.1.1) (fun p : SourceNormalizedParameter N => p.1.2)
    ((ρ,v),(r,u)) s hA hB (by fun_prop) (by fun_prop) hholA hholB j

end
end IsingBulk.First
