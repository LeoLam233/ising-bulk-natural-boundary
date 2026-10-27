import IsingBulk.Preferred22.WeightedTransportCore
import IsingBulk.Preferred22.TransportSupport

/-! Genuine mixed regularity and exact support of weighted physical
transport, with the fixed smooth multiplier differentiated by the literal
recurrence. There is no regularity or norm premise on descendants. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- A seed that vanishes on a genuine open angular set has every transported
descendant zero there, even with an arbitrary ambient angular field. -/
theorem preferredWeightedPhysicalDensity_zero_on_open {N : ℕ}
    (ψ : (Fin N → ℝ) → ℂ) (τ : ℝ) (η p m rcut : ℝ → ℝ)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hseed : ∀ s : ℂ,∀ θ∈U,ψ θ*preferredPhysicalSeed .right τ η p m rcut s θ=0) :
    ∀ j : ℕ,∀ s : ℂ,∀ θ∈U,preferredWeightedPhysicalDensity ψ τ η p m rcut j s θ=0 := by
  intro j
  induction j with
  | zero => exact hseed
  | succ j ih =>
    intro s θ hθ
    have hs : (fun t : ℂ => preferredWeightedPhysicalDensity ψ τ η p m rcut j t θ)=fun _ => 0 :=
      funext (fun t => ih t θ hθ)
    have ha (i : Fin N) :
        deriv (fun x : ℝ => preferredSourceAngularField .right τ p m s (Function.update θ i x) i *
          preferredWeightedPhysicalDensity ψ τ η p m rcut j s (Function.update θ i x)) (θ i)=0 := by
      have hc : Continuous (fun x : ℝ => Function.update θ i x) := by fun_prop
      have ht : Tendsto (fun x : ℝ => Function.update θ i x) (𝓝 (θ i)) (𝓝 θ) := by
        simpa only [Function.update_eq_self] using hc.tendsto (θ i)
      have he : (fun x : ℝ => preferredSourceAngularField .right τ p m s (Function.update θ i x) i *
          preferredWeightedPhysicalDensity ψ τ η p m rcut j s (Function.update θ i x)) =ᶠ[𝓝 (θ i)] fun _ => 0 := by
        filter_upwards [ht.eventually (hU.mem_nhds hθ)] with x hx
        rw [ih s (Function.update θ i x) hx,mul_zero]
      simpa only [deriv_const] using he.deriv_eq
    simp only [preferredWeightedPhysicalDensity,preferredTransportStep,preferredAngularDivergence,hs,deriv_const]
    simp_rw [ha]
    simp

/-- Upper population exclusion is an open condition. The actual population
cutoff is already identically one before a plateau value can decrease. -/
theorem preferredWeightedPhysicalDensity_zero_of_upper_particle {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (ψ : (Fin N → ℝ) → ℂ) (τ : ℝ) (rcut : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hp : 1/2<B.p (θ i)) :
    preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  let U : Set (Fin N → ℝ) := {x | (1/2:ℝ)<B.p (x i)}
  have hU : IsOpen U := isOpen_lt continuous_const (B.smooth.continuous.comp (continuous_apply i))
  apply preferredWeightedPhysicalDensity_zero_on_open ψ τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hp
  intro t x hx
  have hP : 1/2≤occupancy B.p x := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun v _ => B.lower_bound (x v)) (Finset.mem_univ i)
    exact hx.le.trans hh
  have he := preferredPopulationCutoff_one hP
  simp only [preferredPhysicalSeed,preferredCellWeight,preferredLowerWeight,lowerWeight,he,
    sub_self,zero_mul,zero_div,Complex.ofReal_zero,mul_zero]

/-- Every physical transported right density retains its precise closed
right support on the actual one-sided angular lift. -/
theorem preferredWeightedPhysicalDensity_right_support {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (ψ : (Fin N → ℝ) → ℂ) (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (houtside : ¬∀ i,θ i∈Icc (-d.b-δB) B.delta) :
    preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp houtside
  change ¬(-d.b-δB≤θ i ∧ θ i≤B.delta) at hi
  rcases not_and_or.mp hi with hlo|hhi
  · have hlo' : θ i< -d.b-δB := lt_of_not_ge hlo
    rcases hcut with ⟨hδB,_hδBδ,_hsmooth,_hperiod,_hunit,hvalues⟩
    let U : Set (Fin N → ℝ) := (fun x => x i) ⁻¹' Ioo (-Real.pi-B.delta) (min B.delta (-d.b-δB))
    have hU : IsOpen U := isOpen_Ioo.preimage (continuous_apply i)
    have hθU : θ∈U := ⟨(hθ i).1,lt_min (by linarith [d.b_pos,B.delta_pos]) hlo'⟩
    apply preferredWeightedPhysicalDensity_zero_on_open ψ τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hθU
    intro t x hx
    have hlow := hx.1
    have hupp := lt_min_iff.mp hx.2
    have hr := (hvalues (x i) ⟨hlow.le,hupp.1.le⟩).1 (by linarith [hupp.2])
    have hprod : (∏ v,rcut (x v))=0 := Finset.prod_eq_zero (Finset.mem_univ i) hr
    simp only [preferredPhysicalSeed,preferredCellWeight,preferredRightWeight,hprod,mul_zero,
      Complex.ofReal_zero,zero_mul,zero_div]
  · have hhi' : B.delta<θ i := lt_of_not_ge hhi
    have hp : B.p (θ i)=1 := B.plateau (θ i) ⟨hhi'.le,(hθ i).2⟩
    exact preferredWeightedPhysicalDensity_zero_of_upper_particle d B ψ τ rcut j s θ i (by rw [hp]; norm_num)

/-- The angular multiplier is a true smooth real function; it is constant
in the complex physical parameter. All mixed regularity follows from the
original physical seed and actual ambient source field. -/
theorem preferredWeightedPhysicalDensity_mixed_regularDomain {N : ℕ} (hN : 0<N)
    (ψ : (Fin N → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (τ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) (j : ℕ) :
    PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) =>
      preferredWeightedPhysicalDensity ψ τ η p m r j z.1 z.2)
      (preferredPhysicalRegularDomain τ p m) := by
  induction j with
  | zero =>
    have hmψ : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => ψ z.2)
        (preferredPhysicalRegularDomain τ p m) := by
      intro z _
      refine ⟨(hψ.comp contDiff_snd).contDiffAt,?_⟩
      change DifferentiableAt ℂ (fun _ : ℂ => ψ z.2) z.1
      exact differentiableAt_const _
    exact hmψ.mul (preferredTransportedDensity_mixed_regularDomain hN τ η p m r hη hp hm hr 0)
  | succ j ih =>
    exact preferredTransportStep_mixed _ _ _
      (preferredPhysicalRegularDomain_isOpen τ p m hp hm)
      (preferredSourceAngularField_mixed_regularDomain τ p m hp hm) ih

/-- A multiplier that vanishes on an angular neighborhood gives a true
joint zero germ for every physical descendant, even at totalized field poles. -/
theorem preferredWeightedPhysicalDensity_zero_germ {N : ℕ}
    (ψ : (Fin N → ℝ) → ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hψ : ψ=ᶠ[𝓝 θ] fun _ => 0) (j : ℕ) :
    (fun z : ℂ × (Fin N → ℝ) => preferredWeightedPhysicalDensity ψ τ η p m r j z.1 z.2)
      =ᶠ[𝓝 (s,θ)] fun _ => 0 := by
  obtain ⟨U,hsub,hU,hθ⟩ := mem_nhds_iff.mp hψ
  have hz : ∀ t : ℂ,∀ x∈U,preferredWeightedPhysicalDensity ψ τ η p m r j t x=0 :=
    preferredWeightedPhysicalDensity_zero_on_open ψ τ η p m r U hU
      (fun _ x hx => by rw [hsub hx,zero_mul]) j
  filter_upwards [continuousAt_snd.tendsto.eventually (hU.mem_nhds hθ)] with z hzU
  exact hz z.1 z.2 hzU

end
end IsingBulk.Preferred22
