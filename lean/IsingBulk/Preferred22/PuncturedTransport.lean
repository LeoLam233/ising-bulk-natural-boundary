import IsingBulk.Preferred22.PuncturedDensitySmooth
import IsingBulk.Preferred22.PunctureFlux

/-! Exact scalar transport of the actual smooth punctured physical density.
Every derivative is taken before integrating, including the genuine real
cutoff derivative. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Outside the closed right support and away from the modulo seam, all
actual descendants vanish as joint parameter/angular germs. -/
theorem preferredTransportedDensity_outside_zero_germ {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta))
    (hn : θ∉preferredRightAngularBox d B.delta δB N) :
    (fun z : ℂ × (Fin N → ℝ) =>
      preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2)
      =ᶠ[𝓝 (s,θ)] fun _ => 0 := by
  have hclosed : IsClosed (preferredRightAngularBox d B.delta δB N) := by
    have he : preferredRightAngularBox d B.delta δB N=
        ⋂ i : Fin N,{x : Fin N → ℝ | x i∈Icc (-d.b-δB) B.delta} := by ext x; simp [preferredRightAngularBox]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))
  have hn' : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,x∉preferredRightAngularBox d B.delta δB N :=
    hclosed.isOpen_compl.mem_nhds hn
  have hi : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually (isOpen_Ioo.mem_nhds (hθ i))
  filter_upwards [continuousAt_snd.tendsto.eventually (hn'.and hi)] with z hz
  exact preferredTransportedDensity_right_support d B τ rcut hcut j z.1 z.2
    (fun i => ⟨(hz.2 i).1,(hz.2 i).2.le⟩) hz.1

/-- Exact punctured scalar recurrence on every point inside the chosen
period interval, including the totalized full-equality values. -/
theorem preferred_punctured_transport_identity {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (ε R : ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta))
    (hreg : θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈preferredPhysicalRegularDomain τ B.p B.m) :
    deriv (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredPuncturedDensity d B τ R rcut (j+1) (IsingBulk.Branch.radialParameter d.alpha ε) θ+
      preferredAngularDivergence
        (preferredPuncturedCurrent d B τ R rcut j (IsingBulk.Branch.radialParameter d.alpha ε)) θ-
      preferredRightPunctureFlux d B τ rcut j ε R θ := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let P : ℂ → (Fin N → ℝ) → ℂ := preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
  let V : ℂ → (Fin N → ℝ) → Fin N → ℂ := preferredSourceAngularField .right τ B.p B.m
  by_cases hd : 0<preferredAngularDiameter θ
  · have hdiff : DifferentiableAt ℂ (fun t => P t θ) s ∧
        ∀ i,DifferentiableAt ℝ (fun u : ℝ => V s (Function.update θ i u) i*P s (Function.update θ i u)) (θ i) := by
      by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
      · have hP := preferredTransportedDensity_mixed_regularDomain hN τ preferredPopulationCutoff B.p B.m rcut
          preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j (s,θ) (hreg hb hd)
        refine ⟨hP.2,?_⟩
        intro i
        have hV := (preferredSourceAngularField_mixed_regularDomain τ B.p B.m B.smooth B.m_smooth i
          (s,θ) (hreg hb hd)).1
        have hm : HasDerivAt (fun u : ℝ => (s,Function.update θ i u)) (0,Pi.single i 1) (θ i) := by
          convert (hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i)) using 1
        exact (((hV.mul hP.1).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (θ i) hm
          (by simp only [Function.update_eq_self])).differentiableAt
      · have he := preferredTransportedDensity_outside_zero_germ d B (τ := τ) rcut hcut j s θ hθ hb
        have hs : (fun t : ℂ => P t θ)=fun _ => 0 := by
          funext t
          exact preferredTransportedDensity_right_support d B τ rcut hcut j t θ
            (fun i => ⟨(hθ i).1,(hθ i).2.le⟩) hb
        refine ⟨by rw [hs]; exact differentiableAt_const _,?_⟩
        intro i
        have hc : Continuous (fun u : ℝ => (s,Function.update θ i u)) := by fun_prop
        have ht : Tendsto (fun u : ℝ => (s,Function.update θ i u)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
          simpa only [Function.update_eq_self] using hc.tendsto (θ i)
        have hf : (fun u : ℝ => V s (Function.update θ i u) i*P s (Function.update θ i u))
            =ᶠ[𝓝 (θ i)] fun _ => 0 := by
          filter_upwards [he.comp_tendsto ht] with u hu
          change P s (Function.update θ i u)=0 at hu
          rw [hu,mul_zero]
        exact (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq hf
    have hω (i : Fin N) : HasDerivAt (fun u : ℝ => preferredEqualityCutoff R (Function.update θ i u))
        (preferredEqualityCutoffPartial R θ i) (θ i) := by
      have hc : ContDiff ℝ ∞ (fun u : ℝ => preferredEqualityCutoff R (Function.update θ i u)) := by
        exact (preferredEqualityCutoff_smooth (N:=N) R).comp (contDiff_update ∞ θ i)
      exact ((hc.differentiable (by simp)).differentiableAt).hasDerivAt
    have hw := preferredTransportStep_weighted V (preferredEqualityCutoff R) P s θ
      (preferredEqualityCutoffPartial R θ) hdiff.1 hω hdiff.2
    have he : (fun x i => V s x i*((preferredEqualityCutoff R x:ℂ)*P s x))=
        preferredPuncturedCurrent d B τ R rcut j s := by
      funext x i
      unfold preferredPuncturedCurrent
      dsimp [V,P]
      ring
    unfold preferredTransportStep at hw
    rw [he] at hw
    change deriv (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ) s-
      preferredAngularDivergence (preferredPuncturedCurrent d B τ R rcut j s) θ=
      preferredPuncturedDensity d B τ R rcut (j+1) s θ-
        preferredRightPunctureFlux d B τ rcut j ε R θ at hw
    linear_combination hw
  · have hz : preferredAngularDiameter θ=0 := le_antisymm (le_of_not_gt hd) Metric.diam_nonneg
    have hg := preferredEqualityCutoff_zero_germ R θ hz
    have hξ : preferredEqualityCutoff R θ=0 := hg.self_of_nhds
    have hp : (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)=fun _ => 0 := by
      funext t
      simp only [preferredPuncturedDensity,hξ,Complex.ofReal_zero,zero_mul]
    have hc (i : Fin N) : deriv (fun u : ℝ => preferredPuncturedCurrent d B τ R rcut j s
        (Function.update θ i u) i) (θ i)=0 := by
      have ht : Tendsto (fun u : ℝ => Function.update θ i u) (𝓝 (θ i)) (𝓝 θ) := by
        simpa only [Function.update_eq_self] using
          (show Continuous (fun u : ℝ => Function.update θ i u) by fun_prop).tendsto (θ i)
      have he : (fun u : ℝ => preferredPuncturedCurrent d B τ R rcut j s (Function.update θ i u) i)
          =ᶠ[𝓝 (θ i)] fun _ => 0 := by
        filter_upwards [hg.comp_tendsto ht] with u hu
        change preferredEqualityCutoff R (Function.update θ i u)=0 at hu
        simp only [preferredPuncturedCurrent,hu,Complex.ofReal_zero,zero_mul]
      simpa only [deriv_const] using he.deriv_eq
    have hpartial (i : Fin N) : preferredEqualityCutoffPartial R θ i=0 := by
      have ht : Tendsto (fun u : ℝ => Function.update θ i u) (𝓝 (θ i)) (𝓝 θ) := by
        simpa only [Function.update_eq_self] using
          (show Continuous (fun u : ℝ => Function.update θ i u) by fun_prop).tendsto (θ i)
      simpa only [Function.comp_def,preferredEqualityCutoffPartial,deriv_const] using (hg.comp_tendsto ht).deriv_eq
    have hdv : preferredAngularDivergence (preferredPuncturedCurrent d B τ R rcut j s) θ=0 := by
      unfold preferredAngularDivergence
      simp_rw [hc]
      simp
    have hfl : preferredRightPunctureFlux d B τ rcut j ε R θ=0 := by
      unfold preferredRightPunctureFlux
      simp_rw [hpartial]
      simp
    rw [hp,deriv_const]
    change 0=preferredPuncturedDensity d B τ R rcut (j+1) s θ+
      preferredAngularDivergence (preferredPuncturedCurrent d B τ R rcut j s) θ-
      preferredRightPunctureFlux d B τ rcut j ε R θ
    simp only [preferredPuncturedDensity,hξ,Complex.ofReal_zero,zero_mul,hdv,hfl,add_zero,sub_zero]

end
end IsingBulk.Preferred22
