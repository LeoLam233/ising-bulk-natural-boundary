import IsingBulk.Preferred22.WeightedTransportRegularity
import IsingBulk.Preferred22.FinitePuncturedMass

/-! Exact equality support and genuine full-torus regularity of a smooth
multiplier transported from the original physical seed. The multiplier is
not placed outside an already differentiated density. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def preferredEqualityMultiplier {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) : ℂ :=
  (preferredEqualityCutoff R θ:ℂ)

theorem preferredEqualityMultiplier_smooth {N : ℕ} (R : ℝ) :
    ContDiff ℝ ∞ (@preferredEqualityMultiplier N R) :=
  Complex.ofRealCLM.contDiff.comp (preferredEqualityCutoff_smooth R)

theorem preferredEqualityMultiplier_zero_germ {N : ℕ} (R : ℝ) (θ : Fin N → ℝ)
    (hd : preferredAngularDiameter θ=0) :
    preferredEqualityMultiplier R=ᶠ[𝓝 θ] fun _ => 0 := by
  filter_upwards [preferredEqualityCutoff_zero_germ R θ hd] with x hx
  simp only [preferredEqualityMultiplier,hx,Complex.ofReal_zero]

theorem preferredEqualityMultiplier_zero_germ_small {N : ℕ} (hN : 0<N)
    {R : ℝ} (hR : 0<R) (θ : Fin N → ℝ)
    (hd : preferredAngularDiameter θ<R/(2*(N:ℝ))) :
    preferredEqualityMultiplier R=ᶠ[𝓝 θ] fun _ => 0 := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hD : 0≤preferredAngularDiameter θ := Metric.diam_nonneg
  have hh := (lt_div_iff₀ (by positivity : 0<2*(N:ℝ))).mp hd
  have hsq : (preferredAngularDiameter θ*(2*(N:ℝ)))^2<R^2 := by
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0<R+preferredAngularDiameter θ*(2*(N:ℝ)) by positivity)]
  have hx : preferredEqualitySize θ/R^2<(1/4:ℝ) := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [preferredEqualitySize_le_diameter_sq θ]
  have hc : ContinuousAt (fun x : Fin N → ℝ => preferredEqualitySize x/R^2) θ :=
    (preferredEqualitySize_smooth.continuous.div_const _).continuousAt
  filter_upwards [hc.eventually_lt continuousAt_const hx] with x hx
  simp only [preferredEqualityMultiplier,preferredEqualityCutoff,preferredPopulationCutoff_zero hx.le,
    Complex.ofReal_zero]

theorem preferredWeightedPhysicalDensity_equality_support {N : ℕ} (hN : 0<N)
    {R : ℝ} (hR : 0<R) (τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) (s : ℂ)
    (θ : Fin N → ℝ) (hd : preferredAngularDiameter θ<R/(2*(N:ℝ))) :
    preferredWeightedPhysicalDensity (preferredEqualityMultiplier R) τ η p m r j s θ=0 :=
  (preferredWeightedPhysicalDensity_zero_germ _ τ η p m r s θ
    (preferredEqualityMultiplier_zero_germ_small hN hR θ hd) j).self_of_nhds

/-- Interior source smoothness, actual upper support and a genuine equality
zero germ are enough for a global smooth angular representative. -/
theorem preferredSupportedFunction_contDiffAt {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB : ℝ) (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ,(∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) →
      θ∉preferredRightAngularBox d B.delta δB N → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta))
    (hF : ∀ x∈preferredRightAngularBox d B.delta δB N,
      0<preferredAngularDiameter x → ContDiffAt ℝ ∞ F (s,x))
    (heq : preferredAngularDiameter θ=0 → F=ᶠ[𝓝 (s,θ)] fun _ => 0) :
    ContDiffAt ℝ ∞ F (s,θ) := by
  by_cases hd : 0<preferredAngularDiameter θ
  · by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
    · exact hF θ hb hd
    · have hclosed : IsClosed (preferredRightAngularBox d B.delta δB N) := by
        have he : preferredRightAngularBox d B.delta δB N=
            ⋂ i : Fin N,{x : Fin N → ℝ | x i∈Icc (-d.b-δB) B.delta} := by ext x; simp [preferredRightAngularBox]
        rw [he]
        exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))
      have hn : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,x∉preferredRightAngularBox d B.delta δB N :=
        hclosed.isOpen_compl.mem_nhds hb
      have hi : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta) := by
        apply Filter.eventually_all.mpr
        intro i
        exact (continuous_apply i).continuousAt.eventually (isOpen_Ioo.mem_nhds (hθ i))
      have he : F=ᶠ[𝓝 (s,θ)] fun _ => 0 := by
        filter_upwards [continuousAt_snd.tendsto.eventually (hn.and hi)] with z hz
        exact hzero z.1 z.2 (fun i => ⟨(hz.2 i).1,(hz.2 i).2.le⟩) hz.1
      exact contDiffAt_const.congr_of_eventuallyEq he
  · exact contDiffAt_const.congr_of_eventuallyEq
      (heq (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg))

def preferredWeightedRightCurrent {N : ℕ} (ψ : (Fin N → ℝ) → ℂ)
    (τ : ℝ) (p m r : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  preferredSourceAngularField .right τ p m s θ i*
    preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff p m r j s θ

/-- Actual mixed regularity and exact source support discharge every global
smoothness premise, including the full equality locus and the period seam. -/
theorem preferredWeighted_density_current_contDiffAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψzero : ∀ θ : Fin N → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredWeightedRightCurrent ψ τ B.p B.m rcut j z.1 z.2 i) (s,θ) := by
  let P := fun z : ℂ × (Fin N → ℝ) => preferredWeightedPhysicalDensity ψ τ
    preferredPopulationCutoff B.p B.m rcut j z.1 z.2
  have hupper : ∀ t x i,1/2<B.p (x i) → P (t,x)=0 :=
    fun t x i hi => preferredWeightedPhysicalDensity_zero_of_upper_particle d B ψ τ rcut j t x i hi
  have hzero : ∀ t x,(∀ i,x i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) →
      x∉preferredRightAngularBox d B.delta δB N → P (t,x)=0 :=
    fun t x hx hn => preferredWeightedPhysicalDensity_right_support d B ψ τ rcut hcut j t x hx hn
  have hP : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      ContDiffAt ℝ ∞ P (s,x) := by
    intro x hx hd
    exact (preferredWeightedPhysicalDensity_mixed_regularDomain hN ψ hψ τ preferredPopulationCutoff
      B.p B.m rcut preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j
      (s,x) (hreg x hx hd)).1
  have heq : preferredAngularDiameter θ=0 → P=ᶠ[𝓝 (s,θ)] fun _ => 0 :=
    fun hd => preferredWeightedPhysicalDensity_zero_germ ψ τ preferredPopulationCutoff B.p B.m rcut s θ
      (hψzero θ hd) j
  constructor
  · apply preferredPeriodIntervalFunction_contDiffAt d B P hupper s θ hθ
    intro hi
    exact preferredSupportedFunction_contDiffAt d B δB P hzero s θ
      (fun i => ⟨(hθ i).1,hi i⟩) hP heq
  · intro i
    let F := fun z : ℂ × (Fin N → ℝ) => preferredWeightedRightCurrent ψ τ B.p B.m rcut j z.1 z.2 i
    apply preferredPeriodIntervalFunction_contDiffAt d B F
      (fun t x a ha => by change preferredSourceAngularField .right τ B.p B.m t x i*P (t,x)=0; rw [hupper t x a ha,mul_zero]) s θ hθ
    intro hi
    apply preferredSupportedFunction_contDiffAt d B δB F
      (fun t x hx hn => by change preferredSourceAngularField .right τ B.p B.m t x i*P (t,x)=0; rw [hzero t x hx hn,mul_zero])
      s θ (fun a => ⟨(hθ a).1,hi a⟩)
    · intro x hx hd
      exact ((preferredSourceAngularField_mixed_regularDomain τ B.p B.m B.smooth B.m_smooth i
        (s,x) (hreg x hx hd)).1).mul (hP x hx hd)
    · intro hd
      filter_upwards [heq hd] with z hz
      change preferredSourceAngularField .right τ B.p B.m z.1 z.2 i*P z=0
      rw [hz,mul_zero]

/-- The actual modular lift is included. It is affine away from the seam,
and actual upper-population zero germs remove the seam itself. -/
theorem preferredWeighted_density_current_lift_contDiffAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψzero : ∀ θ : Fin N → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j z.1
        (preferredLiftedAngles B.delta z.2)) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredWeightedRightCurrent ψ τ B.p B.m rcut j z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ) := by
  have hx := preferredLiftedAngles_mem_oneSided B.delta θ
  have hc := preferredWeighted_density_current_contDiffAt hN d B ψ hψ hψzero rcut hcut s j hreg
    (preferredLiftedAngles B.delta θ) hx
  have hzero := preferredWeightedPhysicalDensity_zero_of_upper_particle d B ψ τ rcut j
  constructor
  · exact preferredLiftedFunction_contDiffAt d B _
      (fun t x i hi => hzero t x i hi) s θ (fun _ => hc.1)
  · intro i
    apply preferredLiftedFunction_contDiffAt d B _ _ s θ (fun _ => hc.2 i)
    intro t x a ha
    change preferredSourceAngularField .right τ B.p B.m t x i*
      preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j t x=0
    rw [hzero t x a ha,mul_zero]

/-- Complex parameter regularity is checked separately from real angular
smoothness and also holds on the closed one-sided interval. -/
theorem preferredWeighted_parameter_differentiable {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψzero : ∀ θ : Fin N → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    DifferentiableAt ℂ (fun t => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j t θ) s := by
  by_cases hd : 0<preferredAngularDiameter θ
  · by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
    · exact (preferredWeightedPhysicalDensity_mixed_regularDomain hN ψ hψ τ preferredPopulationCutoff
        B.p B.m rcut preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j
        (s,θ) (hreg θ hb hd)).2
    · have he : (fun t => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j t θ)=
          fun _ => 0 := funext (fun t =>
        preferredWeightedPhysicalDensity_right_support d B ψ τ rcut hcut j t θ hθ hb)
      rw [he]
      exact differentiableAt_const _
  · have hz : preferredAngularDiameter θ=0 := le_antisymm (le_of_not_gt hd) Metric.diam_nonneg
    have he : (fun t => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j t θ)=
        fun _ => 0 := funext (fun t =>
      (preferredWeightedPhysicalDensity_zero_germ ψ τ preferredPopulationCutoff B.p B.m rcut t θ
        (hψzero θ hz) j).self_of_nhds)
    rw [he]
    exact differentiableAt_const _

end
end IsingBulk.Preferred22
