import IsingBulk.Preferred22.ShellCover
import IsingBulk.Preferred22.RightCutoff

/-! The true real cutoff support is preserved by every literal transport.
Local vanishing is proved before differentiation, so neither complexifying
cutoffs nor assuming regularity of V outside the support is needed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- A seed that vanishes on a genuine open angular set has every transported
descendant zero there, even with an arbitrary ambient angular field. -/
theorem preferredTransportedDensity_zero_on_open {N : ℕ}
    (cell : PreferredTransportCell N) (τ : ℝ) (η p m rcut : ℝ → ℝ)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hseed : ∀ s : ℂ,∀ θ∈U,preferredPhysicalSeed cell τ η p m rcut s θ=0) :
    ∀ j : ℕ,∀ s : ℂ,∀ θ∈U,preferredTransportedDensity cell τ η p m rcut j s θ=0 := by
  intro j
  induction j with
  | zero => exact hseed
  | succ j ih =>
    intro s θ hθ
    have hs : (fun t : ℂ => preferredTransportedDensity cell τ η p m rcut j t θ)=fun _ => 0 :=
      funext (fun t => ih t θ hθ)
    have ha (i : Fin N) :
        deriv (fun x : ℝ => preferredSourceAngularField cell τ p m s (Function.update θ i x) i *
          preferredTransportedDensity cell τ η p m rcut j s (Function.update θ i x)) (θ i)=0 := by
      have hc : Continuous (fun x : ℝ => Function.update θ i x) := by fun_prop
      have ht : Tendsto (fun x : ℝ => Function.update θ i x) (𝓝 (θ i)) (𝓝 θ) := by
        simpa only [Function.update_eq_self] using hc.tendsto (θ i)
      have he : (fun x : ℝ => preferredSourceAngularField cell τ p m s (Function.update θ i x) i *
          preferredTransportedDensity cell τ η p m rcut j s (Function.update θ i x)) =ᶠ[𝓝 (θ i)] fun _ => 0 := by
        filter_upwards [ht.eventually (hU.mem_nhds hθ)] with x hx
        rw [ih s (Function.update θ i x) hx,mul_zero]
      simpa only [deriv_const] using he.deriv_eq
    simp only [preferredTransportedDensity_succ,preferredAngularDivergence,hs,deriv_const]
    simp_rw [ha]
    simp

/-- Upper population exclusion is an open condition. The actual population
cutoff is already identically one before a plateau value can decrease. -/
theorem preferredTransportedDensity_zero_of_upper_particle {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) (hp : 1/2<B.p (θ i)) :
    preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  let U : Set (Fin N → ℝ) := {x | (1/2:ℝ)<B.p (x i)}
  have hU : IsOpen U := isOpen_lt continuous_const (B.smooth.continuous.comp (continuous_apply i))
  apply preferredTransportedDensity_zero_on_open .right τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hp
  intro t x hx
  have hP : 1/2≤occupancy B.p x := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun v _ => B.lower_bound (x v)) (Finset.mem_univ i)
    exact hx.le.trans hh
  have he := preferredPopulationCutoff_one hP
  simp only [preferredPhysicalSeed,preferredCellWeight,preferredLowerWeight,lowerWeight,he,
    sub_self,zero_mul,zero_div,Complex.ofReal_zero]

/-- Every physical transported right density retains its precise closed
right support on the actual one-sided angular lift. -/
theorem preferredTransportedDensity_right_support {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (houtside : ¬∀ i,θ i∈Icc (-d.b-δB) B.delta) :
    preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp houtside
  change ¬(-d.b-δB≤θ i ∧ θ i≤B.delta) at hi
  rcases not_and_or.mp hi with hlo|hhi
  · have hlo' : θ i< -d.b-δB := lt_of_not_ge hlo
    rcases hcut with ⟨hδB,_hδBδ,_hsmooth,_hperiod,_hunit,hvalues⟩
    let U : Set (Fin N → ℝ) := (fun x => x i) ⁻¹' Ioo (-Real.pi-B.delta) (min B.delta (-d.b-δB))
    have hU : IsOpen U := isOpen_Ioo.preimage (continuous_apply i)
    have hθU : θ∈U := ⟨(hθ i).1,lt_min (by linarith [d.b_pos,B.delta_pos]) hlo'⟩
    apply preferredTransportedDensity_zero_on_open .right τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hθU
    intro t x hx
    have hlow := hx.1
    have hupp := lt_min_iff.mp hx.2
    have hr := (hvalues (x i) ⟨hlow.le,hupp.1.le⟩).1 (by linarith [hupp.2])
    have hprod : (∏ v,rcut (x v))=0 := Finset.prod_eq_zero (Finset.mem_univ i) hr
    simp only [preferredPhysicalSeed,preferredCellWeight,preferredRightWeight,hprod,mul_zero,
      Complex.ofReal_zero,zero_mul,zero_div]
  · have hhi' : B.delta<θ i := lt_of_not_ge hhi
    have hp : B.p (θ i)=1 := B.plateau (θ i) ⟨hhi'.le,(hθ i).2⟩
    exact preferredTransportedDensity_zero_of_upper_particle d B τ rcut j s θ i (by rw [hp]; norm_num)

theorem preferredLiftedAngles_mem_oneSided {N : ℕ} (δ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    preferredLiftedAngles δ θ i∈Ioc (-Real.pi-δ) (Real.pi-δ) := by
  have hh := toIocMod_mem_Ioc (by positivity : 0<2*Real.pi) (-Real.pi-δ) (θ i)
  simpa only [preferredLiftedAngles,show -Real.pi-δ+2*Real.pi=Real.pi-δ by ring] using hh

/-- The complete actual right transported integral is exactly over the
closed right region. This is a proved support identity for every order. -/
theorem preferredTransportedIntegral_eq_rightRegion {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) :
    preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut j s=
      ∫ (θ : Fin n → ℝ) in preferredRightRegion d B δB,
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
          (preferredLiftedAngles B.delta (constrainedAngles θ)) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)) (fun θ hθ => hθ.1)
  intro θ hθ
  apply preferredTransportedDensity_right_support d B τ rcut hcut j s _
    (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
  intro hh
  exact hθ.2 ⟨hθ.1,hh⟩

/-- The unchanged full actual nonnegative right mass equals the region
mass, without any assumed integrability or a hidden support condition. -/
theorem preferredTransportedNorm_lintegral_eq_rightRegion {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) :
    (∫⁻ θ in angularBox n,ENNReal.ofReal ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
      (preferredLiftedAngles B.delta (constrainedAngles θ))‖)=
    ∫⁻ (θ : Fin n → ℝ) in preferredRightRegion d B δB,ENNReal.ofReal ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
      (preferredLiftedAngles B.delta (constrainedAngles θ))‖ := by
  let f := fun θ : Fin n → ℝ => ENNReal.ofReal ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hsupp : Function.support ((angularBox n).indicator f)⊆preferredRightRegion d B δB := by
    intro θ hθ
    by_contra hn
    by_cases hb : θ∈angularBox n
    · have hz := preferredTransportedDensity_right_support d B τ rcut hcut j s _
        (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
        (by intro hh; exact hn ⟨hb,hh⟩)
      have hf : f θ=0 := by dsimp [f]; rw [hz,norm_zero,ENNReal.ofReal_zero]
      exact hθ (by rw [Set.indicator_of_mem hb,hf])
    · exact hθ (Set.indicator_of_notMem hb _)
  apply le_antisymm
  · calc
      _ = ∫⁻ θ,(angularBox n).indicator f θ := (lintegral_indicator hbox f).symm
      _ = ∫⁻ (θ : Fin n → ℝ) in preferredRightRegion d B δB,(angularBox n).indicator f θ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)
  · exact lintegral_mono_set (fun θ hθ => hθ.1)

end
end IsingBulk.Preferred22
