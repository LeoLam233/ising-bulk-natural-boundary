import IsingBulk.Preferred22.LiftedTransportCalculus
import IsingBulk.Preferred22.EqualityCutoff
import IsingBulk.Preferred22.PhysicalDensityShell

/-! Genuine smoothness of the punctured physical densities and currents
on the entire lifted angular torus. Singular totalized values are removed
only where the original smooth equality cutoff is locally zero. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The equality size is exactly zero on the full collision locus. -/
theorem preferredEqualitySize_eq_zero_of_diameter {N : ℕ} (θ : Fin N → ℝ)
    (hθ : preferredAngularDiameter θ=0) : preferredEqualitySize θ=0 := by
  unfold preferredEqualitySize
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  have hh := preferredAngularDiameter_pair_le θ a b
  rw [hθ] at hh
  have he : θ a-θ b=0 := abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  rw [he,zero_pow (by norm_num : (2:ℕ)≠0)]

/-- The literal puncture is identically zero near every full collision. -/
theorem preferredEqualityCutoff_zero_germ {N : ℕ} (R : ℝ) (θ : Fin N → ℝ)
    (hθ : preferredAngularDiameter θ=0) :
    preferredEqualityCutoff R =ᶠ[𝓝 θ] fun _ => 0 := by
  have hc : ContinuousAt (fun x : Fin N → ℝ => preferredEqualitySize x/R^2) θ :=
    (preferredEqualitySize_smooth.continuous.div_const _).continuousAt
  have he := hc.eventually_lt continuousAt_const
    (by rw [preferredEqualitySize_eq_zero_of_diameter θ hθ,zero_div]; norm_num :
      preferredEqualitySize θ/R^2<(1/4:ℝ))
  filter_upwards [he] with x hx
  exact preferredPopulationCutoff_zero hx.le

/-- Local support and source smoothness suffice for actual punctured
smoothness throughout the open one-sided angular period. -/
theorem preferredPuncturedFunction_contDiffAt {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB R : ℝ) (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ,(∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) →
      θ∉preferredRightAngularBox d B.delta δB N → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta))
    (hF : ∀ x∈preferredRightAngularBox d B.delta δB N,
      0<preferredAngularDiameter x → ContDiffAt ℝ ∞ F (s,x)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      (preferredEqualityCutoff R z.2:ℂ)*F z) (s,θ) := by
  by_cases hdiam : 0<preferredAngularDiameter θ
  · by_cases hbox : θ∈preferredRightAngularBox d B.delta δB N
    · exact ((Complex.ofRealCLM.contDiff.comp
        ((preferredEqualityCutoff_smooth R).comp contDiff_snd)).contDiffAt).mul (hF θ hbox hdiam)
    · have hclosed : IsClosed (preferredRightAngularBox d B.delta δB N) := by
        have he : preferredRightAngularBox d B.delta δB N=
            ⋂ i : Fin N,{x : Fin N → ℝ | x i∈Icc (-d.b-δB) B.delta} := by ext x; simp [preferredRightAngularBox]
        rw [he]
        exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))
      have hn : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,x∉preferredRightAngularBox d B.delta δB N :=
        hclosed.isOpen_compl.mem_nhds hbox
      have hi : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta) := by
        apply Filter.eventually_all.mpr
        intro i
        exact (continuous_apply i).continuousAt.eventually (isOpen_Ioo.mem_nhds (hθ i))
      have he : (fun z : ℂ × (Fin N → ℝ) => (preferredEqualityCutoff R z.2:ℂ)*F z)
          =ᶠ[𝓝 (s,θ)] fun _ => 0 := by
        filter_upwards [continuousAt_snd.tendsto.eventually (hn.and hi)] with z hz
        rw [hzero z.1 z.2 (fun i => ⟨(hz.2 i).1,(hz.2 i).2.le⟩) hz.1,mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · have hz : preferredAngularDiameter θ=0 :=
      le_antisymm (le_of_not_gt hdiam) Metric.diam_nonneg
    have he : (fun z : ℂ × (Fin N → ℝ) => (preferredEqualityCutoff R z.2:ℂ)*F z)
        =ᶠ[𝓝 (s,θ)] fun _ => 0 := by
      filter_upwards [(preferredEqualityCutoff_zero_germ R θ hz).comp_tendsto continuousAt_snd.tendsto] with z hz
      change preferredEqualityCutoff R z.2=0 at hz
      rw [hz,Complex.ofReal_zero,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- Literal punctured physical density; the original scalar normalization
is already inside the transported density. -/
def preferredPuncturedDensity {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredEqualityCutoff R θ:ℂ)*
    preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s θ

/-- Literal punctured current, with the unchanged physical angular field. -/
def preferredPuncturedCurrent {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ R : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (preferredEqualityCutoff R θ:ℂ)*
    (preferredSourceAngularField .right τ B.p B.m s θ i*
      preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s θ)

/-- Genuine full-torus punctured smoothness from the already proved actual
regular-domain membership. The statement controls every positive order. -/
theorem preferredPuncturedDensity_and_current_lift_contDiffAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredPuncturedDensity d B τ R rcut j z.1 (preferredLiftedAngles B.delta z.2)) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredPuncturedCurrent d B τ R rcut j z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ) := by
  let P := fun z : ℂ × (Fin N → ℝ) =>
    preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2
  have hpzero : ∀ t x,(∀ i,x i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) →
      x∉preferredRightAngularBox d B.delta δB N → P (t,x)=0 := by
    intro t x hx hn
    exact preferredTransportedDensity_right_support d B τ rcut hcut j t x hx hn
  have hP (x : Fin N → ℝ) (hx : x∈preferredRightAngularBox d B.delta δB N)
      (hd : 0<preferredAngularDiameter x) : ContDiffAt ℝ ∞ P (s,x) :=
    (preferredTransportedDensity_mixed_regularDomain hN τ preferredPopulationCutoff B.p B.m rcut
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j (s,x) (hreg x hx hd)).1
  have hpu : ∀ t x i,1/2<B.p (x i) → P (t,x)=0 :=
    fun t x i hi => preferredTransportedDensity_zero_of_upper_particle d B τ rcut j t x i hi
  constructor
  · refine preferredLiftedFunction_contDiffAt d B
      (fun z => preferredPuncturedDensity d B τ R rcut j z.1 z.2) ?_ s θ ?_
    · intro t x i hi
      change (preferredEqualityCutoff R x:ℂ)*P (t,x)=0
      rw [hpu t x i hi,mul_zero]
    · intro hθ
      exact preferredPuncturedFunction_contDiffAt d B δB R P hpzero s _
        (fun i => ⟨(preferredLiftedAngles_mem_oneSided B.delta θ i).1,hθ i⟩) hP
  · intro i
    let F := fun z : ℂ × (Fin N → ℝ) => preferredSourceAngularField .right τ B.p B.m z.1 z.2 i*P z
    refine preferredLiftedFunction_contDiffAt d B
      (fun z => preferredPuncturedCurrent d B τ R rcut j z.1 z.2 i) ?_ s θ ?_
    · intro t x a ha
      change (preferredEqualityCutoff R x:ℂ)*(preferredSourceAngularField .right τ B.p B.m t x i*P (t,x))=0
      rw [hpu t x a ha,mul_zero,mul_zero]
    · intro hθ
      refine preferredPuncturedFunction_contDiffAt d B δB R F ?_ s _
        (fun a => ⟨(preferredLiftedAngles_mem_oneSided B.delta θ a).1,hθ a⟩) ?_
      · intro t x hx hn
        simp only [F,hpzero t x hx hn,mul_zero]
      · intro x hx hd
        exact ((preferredSourceAngularField_mixed_regularDomain τ B.p B.m B.smooth B.m_smooth i
          (s,x) (hreg x hx hd)).1).mul (hP x hx hd)

/-- All thresholds precede every particle and transport order; the exact
actual one-sided torus density and current are smooth after puncturing. -/
theorem preferred_actual_punctured_smooth (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δB τ₀ ε₀ : ℝ,0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ N : ℕ,2≤N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ R : ℝ,∀ j : ℕ,∀ θ : Fin N → ℝ,
      ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
        preferredPuncturedDensity d B τ R rcut j z.1 (preferredLiftedAngles B.delta z.2))
        (IsingBulk.Branch.radialParameter d.alpha ε,θ) ∧
      ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
        preferredPuncturedCurrent d B τ R rcut j z.1 (preferredLiftedAngles B.delta z.2) i)
        (IsingBulk.Branch.radialParameter d.alpha ε,θ) := by
  obtain ⟨cap,hcap,hcapa,hgeom⟩ := preferred_actual_regularDomain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨δB,τ₀,ε₀,hδB,hδBB,hτ₀,hε₀,hreg⟩ := hgeom B hB
  refine ⟨δB,τ₀,ε₀,hδB,hδBB,hτ₀,hε₀,?_⟩
  intro N hN ε τ hε hεr hτ hτr rcut hcut R j θ
  exact preferredPuncturedDensity_and_current_lift_contDiffAt (by omega) d B rcut hcut
    (IsingBulk.Branch.radialParameter d.alpha ε) R j
    (hreg N hN ε τ hε hεr hτ hτr) θ

end
end IsingBulk.Preferred22
