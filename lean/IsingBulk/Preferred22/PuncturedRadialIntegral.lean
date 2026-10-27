import IsingBulk.Preferred22.PuncturedTransport
import IsingBulk.Preferred22.PuncturedCurrentGeometry
import IsingBulk.Preferred22.AngularRadialIntegral

/-! Exact radial differentiation of the actual smooth punctured right
integral. Periodic Stokes removes the full current; its genuine cutoff
flux is retained for the subsequent uniform limit. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Parameter holomorphy is used only for the actual density where its
cutoff can be nonzero. The cutoff itself is constant in the parameter. -/
theorem preferredPuncturedDensity_parameter_differentiable {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hreg : θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      (s,θ)∈preferredPhysicalRegularDomain τ B.p B.m) :
    DifferentiableAt ℂ (fun t => preferredPuncturedDensity d B τ R rcut j t θ) s := by
  by_cases hξ : preferredEqualityCutoff R θ=0
  · simp only [preferredPuncturedDensity,hξ,Complex.ofReal_zero,zero_mul]
    exact differentiableAt_const _
  · by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
    · have hd : 0<preferredAngularDiameter θ := by
        by_contra hn
        exact hξ (preferredEqualityCutoff_zero_germ R θ
          (le_antisymm (le_of_not_gt hn) Metric.diam_nonneg)).self_of_nhds
      exact ((preferredTransportedDensity_mixed_regularDomain hN τ preferredPopulationCutoff B.p B.m rcut
        preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 j (s,θ) (hreg hb hd)).2).const_mul _
    · have he : (fun t => preferredPuncturedDensity d B τ R rcut j t θ)=fun _ => 0 := by
        funext t
        simp only [preferredPuncturedDensity,
          preferredTransportedDensity_right_support d B τ rcut hcut j t θ hθ hb,mul_zero]
      rw [he]
      exact differentiableAt_const _

/-- The exact punctured recurrence also holds at the endpoint of the
one-sided interval; the physical upper particle plateau kills every term. -/
theorem preferred_punctured_transport_identity_Ioc {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (ε R : ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hreg : θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈preferredPhysicalRegularDomain τ B.p B.m) :
    deriv (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredPuncturedDensity d B τ R rcut (j+1) (IsingBulk.Branch.radialParameter d.alpha ε) θ+
      preferredAngularDivergence
        (preferredPuncturedCurrent d B τ R rcut j (IsingBulk.Branch.radialParameter d.alpha ε)) θ-
      preferredRightPunctureFlux d B τ rcut j ε R θ := by
  classical
  by_cases hi : ∀ i,θ i<Real.pi-B.delta
  · exact preferred_punctured_transport_identity hN d B rcut hcut j ε R θ
      (fun i => ⟨(hθ i).1,hi i⟩) hreg
  · obtain ⟨a,ha⟩ := not_forall.mp hi
    have he : θ a=Real.pi-B.delta := le_antisymm (hθ a).2 (le_of_not_gt ha)
    have hp : 1/2<B.p (θ a) := by
      rw [he,B.plateau _ ⟨by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos],le_rfl⟩]
      norm_num
    let s := IsingBulk.Branch.radialParameter d.alpha ε
    have hP (k : ℕ) (t : ℂ) :
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut k t θ=0 :=
      preferredTransportedDensity_zero_of_upper_particle d B τ rcut k t θ a hp
    have hpar : (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)=fun _ => 0 := by
      funext t
      simp only [preferredPuncturedDensity,hP j t,mul_zero]
    have hdiv (i : Fin N) : deriv (fun u : ℝ => preferredPuncturedCurrent d B τ R rcut j s
        (Function.update θ i u) i) (θ i)=0 := by
      have hg := preferredUpperParticle_zero_germ d B
        (fun z => preferredPuncturedCurrent d B τ R rcut j z.1 z.2 i)
        (fun t x k hk => preferredPuncturedCurrent_upper_zero d B τ R rcut j t x k hk i)
        s θ a hp
      have ht : Tendsto (fun u : ℝ => (s,Function.update θ i u)) (𝓝 (θ i)) (𝓝 (s,θ)) := by
        simpa only [Function.update_eq_self] using
          (show Continuous (fun u : ℝ => (s,Function.update θ i u)) by fun_prop).tendsto (θ i)
      simpa only [Function.comp_def,deriv_const] using (hg.comp_tendsto ht).deriv_eq
    rw [hpar,deriv_const]
    change 0=preferredPuncturedDensity d B τ R rcut (j+1) s θ+
      preferredAngularDivergence (preferredPuncturedCurrent d B τ R rcut j s) θ-
      preferredRightPunctureFlux d B τ rcut j ε R θ
    have hfl : preferredRightPunctureFlux d B τ rcut j ε R θ=0 := by
      unfold preferredRightPunctureFlux
      simp_rw [hP j (IsingBulk.Branch.radialParameter d.alpha ε)]
      simp
    simp only [preferredPuncturedDensity,hP (j+1) s,mul_zero,zero_add,
      preferredAngularDivergence,hfl,sub_zero]
    simp_rw [hdiv]
    simp

/-- The actual radial direction multiplies the complex physical derivative
by the fixed unit root, with no change in the angular cutoff. -/
theorem preferredPuncturedDensity_radial_hasDerivAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (ε R : ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hreg : θ∈preferredRightAngularBox d B.delta δB N → 0<preferredAngularDiameter θ →
      (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈preferredPhysicalRegularDomain τ B.p B.m) :
    HasDerivAt (fun t : ℝ => preferredPuncturedDensity d B τ R rcut j
        (IsingBulk.Branch.radialParameter d.alpha t) θ)
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*
        deriv (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)
          (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  have hd := (preferredPuncturedDensity_parameter_differentiable hN d B rcut hcut
    (IsingBulk.Branch.radialParameter d.alpha ε) R j θ hθ hreg).hasDerivAt
  have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (ε:ℂ) := by
    simpa using ((hasDerivAt_id (ε:ℂ)).const_add 1).mul_const ζ
  have hd' : HasDerivAt (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)
      (deriv (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t θ)
        (IsingBulk.Branch.radialParameter d.alpha ε)) ((1+(ε:ℂ))*ζ) := by
    simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hd
  convert! (hd'.comp (ε:ℂ) hp).comp_ofReal using 1 <;>
    simp only [Function.comp_def,IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ,mul_comm]

/-- The literal punctured right integral at a radial physical parameter. -/
def preferredPuncturedRightIntegral (n : ℕ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (R ε : ℝ) : ℂ :=
  ∫ θ in angularBox n,preferredPuncturedDensity d B τ R rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))

/-- The genuine physical equality-cutoff current, integrated on the full
original angular Haar box. -/
def preferredPunctureFluxIntegral (n : ℕ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (R ε : ℝ) : ℂ :=
  ∫ θ in angularBox n,preferredRightPunctureFlux d B τ rcut j ε R
    (preferredLiftedAngles B.delta (constrainedAngles θ))

/-- The ambient current divergence is continuous on the complete lifted
torus because it equals the intrinsic divergence of a genuine C∞ current. -/
theorem preferred_punctured_ambient_divergence_continuous {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (R : ℝ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (s,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m s x i)=0) :
    Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence
      (preferredPuncturedCurrent d B τ R rcut j s)
      (preferredLiftedAngles B.delta (constrainedAngles θ))) := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := preferredPuncturedCurrent d B τ R rcut j s
  have hzero : ∀ x a,1/2<B.p (x a) → ∀ i,F x i=0 :=
    fun x a ha i => preferredPuncturedCurrent_upper_zero d B τ R rcut j s x a ha i
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => preferredPuncturedCurrent_tangent d B rcut hcut s R j htan x hx
  have hχ : ContDiff ℝ ∞ (@constrainedAngles n) := by
    have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ)) =
        constrainedAngles := funext (constrainedAnglesCLM_apply n)
    rw [←he]
    exact (constrainedAnglesCLM n).contDiff
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAngles θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((preferredPuncturedDensity_and_current_lift_contDiffAt (by omega) d B rcut hcut
      s R j hreg (constrainedAngles θ)).2 i.castSucc).comp θ (contDiffAt_const.prodMk hχ.contDiffAt)
  have he : (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAngles θ)))=
      fun θ => ∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAngles x)) i.castSucc)
        θ (Pi.single i 1) := by
    funext θ
    symm
    apply preferred_lifted_intrinsic_divergence_point d B F hzero htan' θ
    intro i
    have hc := preferredPuncturedCurrent_contDiffAt (by omega) d B rcut hcut s R j hreg
      (preferredLiftedAngles B.delta (constrainedAngles θ))
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ)) i
    exact (hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence F
    (preferredLiftedAngles B.delta (constrainedAngles θ)))
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const

/-- Exact differentiated integral for every fixed positive puncture. The
complete periodic current cancels; the actual cutoff current is retained.
Source regularity and tangency here refer to their concrete previously
proved domains, not to an assumed transport-integral identity. -/
theorem preferred_punctured_right_integral_hasDerivAt {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (R : ℝ) (j : ℕ)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (preferredPuncturedRightIntegral n d B τ rcut j R)
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*
        (preferredPuncturedRightIntegral n d B τ rcut (j+1) R ε-
          preferredPunctureFluxIntegral n d B τ rcut j R ε)) ε := by
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let X := fun θ : Fin n → ℝ => preferredLiftedAngles B.delta (constrainedAngles θ)
  let F := fun z : ℝ × (Fin n → ℝ) =>
    preferredPuncturedDensity d B τ R rcut j (IsingBulk.Branch.radialParameter d.alpha z.1) (X z.2)
  let H := fun θ : Fin n → ℝ => fderiv ℝ F (ε,θ) (1,0)
  let C := fun θ : Fin n → ℝ => deriv (fun t : ℂ => preferredPuncturedDensity d B τ R rcut j t (X θ)) s
  let P := fun θ : Fin n → ℝ => preferredPuncturedDensity d B τ R rcut (j+1) s (X θ)
  let D := fun θ : Fin n → ℝ => preferredAngularDivergence (preferredPuncturedCurrent d B τ R rcut j s) (X θ)
  let E := fun θ : Fin n → ℝ => preferredRightPunctureFlux d B τ rcut j ε R (X θ)
  have hχ : ContDiff ℝ ∞ (@constrainedAngles n) := by
    have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ)) =
        constrainedAngles := funext (constrainedAnglesCLM_apply n)
    rw [←he]
    exact (constrainedAnglesCLM n).contDiff
  have hrad : ContDiff ℝ ∞ (IsingBulk.Branch.radialParameter d.alpha) := by
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
    exact (hc.comp (contDiff_const.add contDiff_id)).mul contDiff_const
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      (IsingBulk.Branch.radialParameter d.alpha z.1,constrainedAngles z.2)) :=
    (hrad.comp contDiff_fst).prodMk (hχ.comp contDiff_snd)
  have hF (t : ℝ) (ht : t∈Ioo 0 ε₀) (θ : Fin n → ℝ) : ContDiffAt ℝ ∞ F (t,θ) := by
    have hh := (preferredPuncturedDensity_and_current_lift_contDiffAt (by omega) d B rcut hcut
      (IsingBulk.Branch.radialParameter d.alpha t) R j (hreg t ht) (constrainedAngles θ)).1
    exact hh.comp (t,θ) hmap.contDiffAt
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hh := ((hF ε hε θ).fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply
      (contDiffAt_const (c := ((1:ℝ),(0:Fin n → ℝ))))
    exact hh.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hHC (θ : Fin n → ℝ) : H θ=ζ*C θ := by
    have hf : HasDerivAt (fun t : ℝ => F (t,θ)) (H θ) ε := by
      have hh := ((hF ε hε θ).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id' ε).prodMk (hasDerivAt_const ε θ))
      simpa only [Function.comp_def,H] using hh
    exact hf.unique (preferredPuncturedDensity_radial_hasDerivAt (by omega) d B rcut hcut
      j ε R (X θ) (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
      (hreg ε hε (X θ)))
  have hC : Continuous C := by
    have he : C=fun θ => ζ⁻¹*H θ := by
      funext θ
      rw [hHC]
      exact (inv_mul_cancel_left₀ (Complex.exp_ne_zero _) (C θ)).symm
    rw [he]
    exact continuous_const.mul hH
  have hP : Continuous P := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hh := (preferredPuncturedDensity_and_current_lift_contDiffAt (by omega) d B rcut hcut
      s R (j+1) (hreg ε hε) (constrainedAngles θ)).1
    exact (hh.comp θ (contDiffAt_const.prodMk hχ.contDiffAt)).continuousAt
  have hD : Continuous D := preferred_punctured_ambient_divergence_continuous d B rcut hcut
    s R j (hreg ε hε) (htan ε hε)
  have hrec (θ : Fin n → ℝ) : C θ=P θ+D θ-E θ :=
    preferred_punctured_transport_identity_Ioc (by omega) d B rcut hcut j ε R (X θ)
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ)) (hreg ε hε (X θ))
  have hE : Continuous E := by
    have he : E=fun θ => P θ+D θ-C θ := by
      funext θ
      linear_combination hrec θ
    rw [he]
    exact (hP.add hD).sub hC
  have hPi := continuous_integrableOn_angularBox hP
  have hDi := continuous_integrableOn_angularBox hD
  have hEi := continuous_integrableOn_angularBox hE
  have hzero : (∫ θ : Fin n → ℝ in angularBox n,D θ)=0 :=
    preferred_punctured_ambient_divergence_integral d B rcut hcut s R j (hreg ε hε) (htan ε hε)
  have hi : (∫ θ : Fin n → ℝ in angularBox n,H θ)=ζ*
      (preferredPuncturedRightIntegral n d B τ rcut (j+1) R ε-
        preferredPunctureFluxIntegral n d B τ rcut j R ε) := by
    simp_rw [hHC,hrec]
    rw [integral_const_mul]
    have hPD : IntegrableOn (fun θ => P θ+D θ) (angularBox n) := by
      convert! hPi.add hDi using 1
    have hsub : (∫ θ : Fin n → ℝ in angularBox n,P θ+D θ-E θ)=
        (∫ θ : Fin n → ℝ in angularBox n,P θ+D θ)-(∫ θ : Fin n → ℝ in angularBox n,E θ) := by
      convert! integral_sub hPD hEi using 1
    have hadd : (∫ θ : Fin n → ℝ in angularBox n,P θ+D θ)=
        (∫ θ : Fin n → ℝ in angularBox n,P θ)+(∫ θ : Fin n → ℝ in angularBox n,D θ) := by
      convert! integral_add hPi hDi using 1
    rw [hsub,hadd,hzero,add_zero]
    rfl
  have hd := preferred_angular_radial_integral_hasDerivAt F hε hF
  change HasDerivAt (preferredPuncturedRightIntegral n d B τ rcut j R)
    (∫ θ : Fin n → ℝ in angularBox n,H θ) ε at hd
  rw [hi] at hd
  exact hd

end
end IsingBulk.Preferred22
