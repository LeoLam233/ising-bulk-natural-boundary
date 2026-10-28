import IsingBulk.HT22.Anchor.ActualScalar
import IsingBulk.Preferred22.TransportSupport
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem transportedDensity_zero_on_open {N : ℕ}
    (anchor : Fin N) (σ : ℂ) (τ : ℝ) (η p m rcut : ℝ → ℝ)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hseed : ∀ s : ℂ,∀ θ∈U,physicalSeed σ τ p m (preferredCellWeight (.anchor anchor) η p m rcut θ) s θ=0) :
    ∀ j : ℕ,∀ s : ℂ,∀ θ∈U,transportedDensity anchor σ τ η p m rcut j s θ=0 := by
  intro j
  induction j with
  | zero => exact hseed
  | succ j ih =>
    intro s θ hθ
    have hs : (fun t : ℂ => transportedDensity anchor σ τ η p m rcut j t θ)=fun _ => 0 :=
      funext (fun t => ih t θ hθ)
    have ha (i : Fin N) :
        deriv (fun x : ℝ => angularField anchor τ p m s (Function.update θ i x) i *
          transportedDensity anchor σ τ η p m rcut j s (Function.update θ i x)) (θ i)=0 := by
      have hc : Continuous (fun x : ℝ => Function.update θ i x) := by fun_prop
      have ht : Tendsto (fun x : ℝ => Function.update θ i x) (𝓝 (θ i)) (𝓝 θ) := by
        simpa only [Function.update_eq_self] using hc.tendsto (θ i)
      have he : (fun x : ℝ => angularField anchor τ p m s (Function.update θ i x) i *
          transportedDensity anchor σ τ η p m rcut j s (Function.update θ i x)) =ᶠ[𝓝 (θ i)] fun _ => 0 := by
        filter_upwards [ht.eventually (hU.mem_nhds hθ)] with x hx
        rw [ih s (Function.update θ i x) hx,mul_zero]
      simpa only [deriv_const] using he.deriv_eq
    simp only [transportedDensity,preferredTransportStep,preferredAngularDivergence,hs,deriv_const]
    simp_rw [ha]
    simp

/-- Upper population exclusion is an open condition. The actual population
cutoff is already identically one before a plateau value can decrease. -/
theorem transportedDensity_zero_of_upper_particle {N : ℕ}
    (anchor : Fin N) (σ : ℂ) (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hp : 1/2<B.p (θ i)) :
    transportedDensity anchor σ τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  let U : Set (Fin N → ℝ) := {x | (1/2:ℝ)<B.p (x i)}
  have hU : IsOpen U := isOpen_lt continuous_const (B.smooth.continuous.comp (continuous_apply i))
  apply transportedDensity_zero_on_open anchor σ τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hp
  intro t x hx
  have hP : 1/2≤occupancy B.p x := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun v _ => B.lower_bound (x v)) (Finset.mem_univ i)
    exact hx.le.trans hh
  have he := preferredPopulationCutoff_one hP
  simp only [physicalSeed,preferredCellWeight,preferredLowerWeight,lowerWeight,he,
    sub_self,zero_mul,zero_div,Complex.ofReal_zero]

theorem transportedDensity_anchor_support {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (σ : ℂ) (a : Fin N) (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (houtside : ¬((∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) ∧ θ a≤ -d.b-δB/2)) :
    transportedDensity a σ τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  classical
  by_cases hcore : ∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta
  · have ha : -d.b-δB/2<θ a := lt_of_not_ge (fun h => houtside ⟨hcore,h⟩)
    by_cases htop : θ a<B.delta
    · let U : Set (Fin N → ℝ) := (fun x => x a) ⁻¹' Ioo
        (max (-Real.pi-B.delta) (-d.b-δB/2)) B.delta
      have hU : IsOpen U := isOpen_Ioo.preimage (continuous_apply a)
      have hz : θ∈U := ⟨max_lt (hθ a).1 ha,htop⟩
      apply transportedDensity_zero_on_open a σ τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hz
      intro t x hx
      have hxl : -Real.pi-B.delta<x a := (le_max_left _ _).trans_lt hx.1
      have hxa : -d.b-δB/2<x a := (le_max_right _ _).trans_lt hx.1
      have hrone : rcut (x a)=1 := (hcut.2.2.2.2.2 (x a) ⟨hxl.le,hx.2.le⟩).2 (by linarith)
      simp only [physicalSeed,preferredCellWeight,preferredAnchorWeight,hrone,sub_self,zero_mul,mul_zero,
        Complex.ofReal_zero,zero_div]
    · have hp : 1/2<B.p (θ a) := by
        rw [B.plateau (θ a) ⟨(le_of_not_gt htop),(hθ a).2⟩]
        norm_num
      exact transportedDensity_zero_of_upper_particle a σ d B τ rcut j s θ a hp
  · obtain ⟨i,hi⟩ := not_forall.mp hcore
    have htop : B.delta<θ i := by
      apply lt_of_not_ge
      intro hh
      exact hi ⟨(hθ i).1.le,hh⟩
    have hp : 1/2<B.p (θ i) := by rw [B.plateau (θ i) ⟨htop.le,(hθ i).2⟩]; norm_num
    exact transportedDensity_zero_of_upper_particle a σ d B τ rcut j s θ i hp

end
end IsingBulk.HT22.Anchor
