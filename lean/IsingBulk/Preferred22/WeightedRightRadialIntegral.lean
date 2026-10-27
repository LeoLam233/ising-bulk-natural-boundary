import IsingBulk.Preferred22.WeightedRightAnalytic
import IsingBulk.Preferred22.ActualTangency
import IsingBulk.Preferred22.DerivativePartition

/-! Actual fixed-multiplier transport on the complete angular torus.
The multiplier is differentiated inside the physical recurrence, so there
is no missing annular flux term. True periodic Stokes proves each step. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredWeightedRightCurrent_tangent {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (ψ : (Fin N → ℝ) → ℂ)
    (hψzero : ∀ θ : Fin N → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (j : ℕ)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m s x i)=0)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (∑ i,preferredWeightedRightCurrent ψ τ B.p B.m rcut j s θ i)=0 := by
  by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
  · by_cases hd : 0<preferredAngularDiameter θ
    · simp only [preferredWeightedRightCurrent,←Finset.sum_mul,htan θ hb hd,zero_mul]
    · have hz := (preferredWeightedPhysicalDensity_zero_germ ψ τ preferredPopulationCutoff B.p B.m rcut
        s θ (hψzero θ (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg)) j).self_of_nhds
      simp only [preferredWeightedRightCurrent,hz,mul_zero,Finset.sum_const_zero]
  · have hz := preferredWeightedPhysicalDensity_right_support d B ψ τ rcut hcut j s θ
      (fun i => ⟨(hθ i).1,(hθ i).2.le⟩) hb
    simp only [preferredWeightedRightCurrent,hz,mul_zero,Finset.sum_const_zero]

/-- Ambient divergence equals the true constrained intrinsic divergence;
its whole-torus integral is exactly zero. -/
theorem preferred_weighted_ambient_divergence {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψzero : ∀ θ : Fin (n+1) → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut) (s : ℂ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m s x i)=0) :
    Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence (preferredWeightedRightCurrent ψ τ B.p B.m rcut j s)
      (preferredLiftedAngles B.delta (constrainedAngles θ))) ∧
    (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence (preferredWeightedRightCurrent ψ τ B.p B.m rcut j s)
      (preferredLiftedAngles B.delta (constrainedAngles θ)))=0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := preferredWeightedRightCurrent ψ τ B.p B.m rcut j s
  have hzero : ∀ x v,1/2<B.p (x v) → ∀ i,F x i=0 := by
    intro x v hv i
    change preferredSourceAngularField .right τ B.p B.m s x i*
      preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j s x=0
    rw [preferredWeightedPhysicalDensity_zero_of_upper_particle d B ψ τ rcut j s x v hv,mul_zero]
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => preferredWeightedRightCurrent_tangent d B ψ hψzero rcut hcut s j htan x hx
  have hχ : ContDiff ℝ ∞ (@constrainedAngles n) := by
    have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ))=constrainedAngles :=
      funext (constrainedAnglesCLM_apply n)
    rw [←he]
    exact (constrainedAnglesCLM n).contDiff
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAngles θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((preferredWeighted_density_current_lift_contDiffAt (by omega) d B ψ hψ hψzero rcut hcut s j hreg
      (constrainedAngles θ)).2 i.castSucc).comp θ (contDiffAt_const.prodMk hχ.contDiffAt)
  have he : (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAngles θ)))=
      fun θ => ∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles x)) i.castSucc)
        θ (Pi.single i 1) := by
    funext θ
    symm
    apply preferred_lifted_intrinsic_divergence_point d B F hzero htan' θ
    intro i
    have hc := (preferredWeighted_density_current_contDiffAt (by omega) d B ψ hψ hψzero rcut hcut s j hreg
      (preferredLiftedAngles B.delta (constrainedAngles θ))
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))).2 i
    exact (hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  constructor
  · change Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAngles θ)))
    rw [he]
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  · change (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAngles θ)))=0
    rw [he]
    exact preferred_lifted_divergence_integral B.delta F hF

/-- The fixed multiplier is part of every transported density. Its full
current is tangent and smooth, hence exact periodic Stokes has no flux. -/
theorem preferred_weighted_integral_radial_hasDerivAt {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψzero : ∀ θ : Fin (n+1) → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut) (j : ℕ)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (preferredWeightedRightRadialIntegral n d B ψ τ rcut j)
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*preferredWeightedRightRadialIntegral n d B ψ τ rcut (j+1) ε) ε := by
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let X := fun θ : Fin n → ℝ => preferredLiftedAngles B.delta (constrainedAngles θ)
  let F := fun z : ℝ × (Fin n → ℝ) => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff
    B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha z.1) (X z.2)
  let H := fun θ : Fin n → ℝ => fderiv ℝ F (ε,θ) (1,0)
  let C := fun θ : Fin n → ℝ => deriv (fun t : ℂ =>
    preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j t (X θ)) s
  let P := fun θ : Fin n → ℝ => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut (j+1) s (X θ)
  let D := fun θ : Fin n → ℝ => preferredAngularDivergence (preferredWeightedRightCurrent ψ τ B.p B.m rcut j s) (X θ)
  have hχ : ContDiff ℝ ∞ (@constrainedAngles n) := by
    have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ))=constrainedAngles :=
      funext (constrainedAnglesCLM_apply n)
    rw [←he]
    exact (constrainedAnglesCLM n).contDiff
  have hrad : ContDiff ℝ ∞ (IsingBulk.Branch.radialParameter d.alpha) := by
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
    exact (hc.comp (contDiff_const.add contDiff_id)).mul contDiff_const
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      (IsingBulk.Branch.radialParameter d.alpha z.1,constrainedAngles z.2)) :=
    (hrad.comp contDiff_fst).prodMk (hχ.comp contDiff_snd)
  have hF (t : ℝ) (ht : t∈Ioo 0 ε₀) (θ : Fin n → ℝ) : ContDiffAt ℝ ∞ F (t,θ) := by
    exact (preferredWeighted_density_current_lift_contDiffAt (by omega) d B ψ hψ hψzero rcut hcut
      (IsingBulk.Branch.radialParameter d.alpha t) j (hreg t ht) (constrainedAngles θ)).1.comp (t,θ) hmap.contDiffAt
  have hHC (θ : Fin n → ℝ) : H θ=ζ*C θ := by
    have hf : HasDerivAt (fun t : ℝ => F (t,θ)) (H θ) ε := by
      have hh := ((hF ε hε θ).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id' ε).prodMk (hasDerivAt_const ε θ))
      simpa only [Function.comp_def,H] using hh
    have hd := (preferredWeighted_parameter_differentiable (by omega) d B ψ hψ hψzero rcut hcut s j
      (hreg ε hε) (X θ) (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))).hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (ε:ℂ) := by
      simpa using ((hasDerivAt_id (ε:ℂ)).const_add 1).mul_const ζ
    have hd' : HasDerivAt (fun t : ℂ => preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff
        B.p B.m rcut j t (X θ)) (C θ) ((1+(ε:ℂ))*ζ) := by
      simpa only [s,C,IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hd
    have hh : HasDerivAt (fun t : ℝ => F (t,θ)) (ζ*C θ) ε := by
      convert! (hd'.comp (ε:ℂ) hp).comp_ofReal using 1 <;>
        simp only [Function.comp_def,F,IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ,mul_comm]
    exact hf.unique hh
  have hP : Continuous P := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact ((preferredWeighted_density_current_lift_contDiffAt (by omega) d B ψ hψ hψzero rcut hcut s (j+1)
      (hreg ε hε) (constrainedAngles θ)).1.comp θ (contDiffAt_const.prodMk hχ.contDiffAt)).continuousAt
  have hD := preferred_weighted_ambient_divergence d B ψ hψ hψzero rcut hcut s j (hreg ε hε) (htan ε hε)
  have hPi := continuous_integrableOn_angularBox hP
  have hDi := continuous_integrableOn_angularBox hD.1
  have hrec (θ : Fin n → ℝ) : C θ=P θ+D θ := by
    change C θ=P θ+preferredAngularDivergence
      (fun x i => preferredSourceAngularField .right τ B.p B.m s x i *
        preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j s x) (X θ)
    dsimp only [C,P]
    rw [preferredWeightedPhysicalDensity,preferredTransportStep]
    exact (sub_add_cancel _ _).symm
  have hi : (∫ θ : Fin n → ℝ in angularBox n,H θ)=
      ζ*preferredWeightedRightRadialIntegral n d B ψ τ rcut (j+1) ε := by
    simp_rw [hHC,hrec]
    rw [integral_const_mul]
    have hadd : (∫ θ : Fin n → ℝ in angularBox n,P θ+D θ)=
        (∫ θ : Fin n → ℝ in angularBox n,P θ)+(∫ θ : Fin n → ℝ in angularBox n,D θ) := by
      convert! integral_add hPi hDi using 1
    rw [hadd,hD.2,add_zero]
    rfl
  have hd := preferred_angular_radial_integral_hasDerivAt F hε hF
  change HasDerivAt (preferredWeightedRightRadialIntegral n d B ψ τ rcut j)
    (∫ θ : Fin n → ℝ in angularBox n,H θ) ε at hd
  rw [hi] at hd
  exact hd

/-- Genuine all-order complex derivatives of the weighted zeroth integral
are exactly the integrals of its literal weighted descendants. -/
theorem preferred_weighted_right_integral_identity {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (hτ : 0≤τ)
    (ψ : (Fin (n+1) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψzero : ∀ θ : Fin (n+1) → ℝ,preferredAngularDiameter θ=0 → ψ=ᶠ[𝓝 θ] fun _ => 0)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0) :
    ∀j : ℕ,∀ε : ℝ,0<ε→ε<ε₀→
      iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredWeightedRightIntegral n d B ψ τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε) := by
  let I := preferredWeightedRightIntegral n d B ψ τ rcut 0
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  have hI (ε : ℝ) (hε : 0<ε) : AnalyticAt ℂ I (IsingBulk.Branch.radialParameter d.alpha ε) :=
    preferredWeightedRightIntegral_zero_analyticAt n d B hτ ψ hψ rcut hcut.2.2.1 (preferredRadialTrace_im_pos d hε)
  intro j
  induction j with
  | zero => intro ε _ _; rfl
  | succ j ih =>
    intro ε hε hεr
    have he : (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        =ᶠ[𝓝 ε] preferredWeightedRightRadialIntegral n d B ψ τ rcut j := by
      filter_upwards [isOpen_Ioo.mem_nhds (show ε∈Ioo 0 ε₀ from ⟨hε,hεr⟩)] with t ht
      exact ih t ht.1 ht.2
    have hf : HasDerivAt (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        (ζ*iteratedDeriv (j+1) I (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
      have ha : AnalyticAt ℂ I ((1+(ε:ℂ))*ζ) := by
        simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hI ε hε
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ]
        using preferred_radial_iterated_hasDerivAt ζ ε j ha
    have hg := preferred_weighted_integral_radial_hasDerivAt d B ψ hψ hψzero rcut hcut j hreg htan ⟨hε,hεr⟩
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    exact hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)

end
end IsingBulk.Preferred22
