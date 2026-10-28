import IsingBulk.HT22.Tail.PuncturedTransport
import IsingBulk.HT22.Tail.PuncturedCurrentGeometry

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem punctured_transport_identity_Ioc {N : ℕ} (hN : 0<N)
    (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (ε R : ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hreg : θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ) :
    deriv (fun t : ℂ => puncturedDensity σ d B τ R rcut j t θ)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      puncturedDensity σ d B τ R rcut (j+1) (IsingBulk.Branch.radialParameter d.alpha ε) θ+
      preferredAngularDivergence
        (puncturedCurrent σ d B τ R rcut j (IsingBulk.Branch.radialParameter d.alpha ε)) θ-
      punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε) R θ := by
  classical
  by_cases hi : ∀ i,θ i<Real.pi-B.delta
  · exact punctured_transport_identity_period hN σ hσ d B rcut hcut j ε R θ
      (fun i => ⟨(hθ i).1,hi i⟩) hreg
  · obtain ⟨a,ha⟩ := not_forall.mp hi
    have he : θ a=Real.pi-B.delta := le_antisymm (hθ a).2 (le_of_not_gt ha)
    have hp : 1/2<B.p (θ a) := by
      rw [he,B.plateau _ ⟨by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos],le_rfl⟩]
      norm_num
    let s := IsingBulk.Branch.radialParameter d.alpha ε
    have hP (k : ℕ) (t : ℂ) :
        transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut k t θ=0 :=
      transportedDensity_zero_of_upper_particle σ d B τ rcut k t θ a hp
    have hpar : (fun t : ℂ => puncturedDensity σ d B τ R rcut j t θ)=fun _ => 0 := by
      funext t
      simp only [puncturedDensity,hP j t,mul_zero]
    have hdiv (i : Fin N) : deriv (fun u : ℝ => puncturedCurrent σ d B τ R rcut j s
        (Function.update θ i u) i) (θ i)=0 := by
      have hg := preferredUpperParticle_zero_germ d B
        (fun z => puncturedCurrent σ d B τ R rcut j z.1 z.2 i)
        (fun t x k hk => puncturedCurrent_upper_zero σ d B τ R rcut j t x k hk i)
        s θ a hp
      have ht : Tendsto (fun u : ℝ => (s,Function.update θ i u)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
        simpa only [Function.update_eq_self] using
          (show Continuous (fun u : ℝ => (s,Function.update θ i u)) by fun_prop).tendsto (θ i)
      simpa only [Function.comp_def,deriv_const] using (hg.comp_tendsto ht).deriv_eq
    rw [hpar,deriv_const]
    change 0=puncturedDensity σ d B τ R rcut (j+1) s θ+
      preferredAngularDivergence (puncturedCurrent σ d B τ R rcut j s) θ-
      punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε) R θ
    have hfl : punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha ε) R θ=0 := by
      unfold punctureFlux
      simp_rw [hP j (IsingBulk.Branch.radialParameter d.alpha ε)]
      simp
    simp only [puncturedDensity,hP (j+1) s,mul_zero,zero_add,
      preferredAngularDivergence,hfl,sub_zero]
    simp_rw [hdiv]
    simp


end
end IsingBulk.HT22.Tail
