import IsingBulk.Preferred22.AnchorGeometry
import IsingBulk.Preferred22.AngularRadialIntegral
import IsingBulk.Preferred22.DerivativePartition

/-! Exact global named-anchor transport. Every current is genuinely smooth
on the complete lifted torus, so ordinary periodic Stokes applies without
an equality puncture, for every particle number including two. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Complex parameter differentiation of the literal anchor density is
valid on the complete period; the upper population exclusion is exact. -/
theorem preferredAnchor_parameter_differentiable {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin N) (τ : ℝ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (s : ℂ) (j : ℕ)
    (hreg : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (s,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    DifferentiableAt ℂ (fun t => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j t θ) s := by
  classical
  by_cases hu : ∀ i,θ i≤B.delta
  · exact (preferredTransportedDensity_mixed_cellDomain (.anchor a) hN τ preferredPopulationCutoff B.p B.m rcut
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hr j (s,θ)
      (hreg θ (fun i => ⟨(hθ i).1.le,hu i⟩))).2
  · obtain ⟨i,hi⟩ := not_forall.mp hu
    have hp : 1/2<B.p (θ i) := by
      rw [B.plateau (θ i) ⟨(lt_of_not_ge hi).le,(hθ i).2⟩]
      norm_num
    have he : (fun t => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j t θ)=
        fun _ => 0 := funext (fun t =>
      preferredTransportedDensity_cell_zero_of_upper_particle (.anchor a) d B τ rcut j t θ i hp)
    rw [he]
    exact differentiableAt_const _

/-- The full ambient anchor-current divergence equals the intrinsic
periodic divergence and therefore is continuous and integrates to zero. -/
theorem preferred_anchor_ambient_divergence {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin (n+1)) (τ : ℝ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (s : ℂ) (j : ℕ)
    (hreg : ∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (s,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m)
    (htan : ∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (∑ i,preferredSourceAngularField (.anchor a) τ B.p B.m s x i)=0) :
    Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence (preferredAnchorCurrent a τ B.p B.m rcut j s)
      (preferredLiftedAngles B.delta (constrainedAngles θ))) ∧
    (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence (preferredAnchorCurrent a τ B.p B.m rcut j s)
      (preferredLiftedAngles B.delta (constrainedAngles θ)))=0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := preferredAnchorCurrent a τ B.p B.m rcut j s
  have hzero : ∀ x v,1/2<B.p (x v) → ∀ i,F x i=0 :=
    fun x v hv i => preferredAnchorCurrent_upper_zero d B a τ rcut j s x v hv i
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => preferredAnchorCurrent_tangent d B a τ rcut s j htan x hx
  have hχ : ContDiff ℝ ∞ (@constrainedAngles n) := by
    have he : (constrainedAnglesCLM n : (Fin n → ℝ) → (Fin (n+1) → ℝ))=constrainedAngles :=
      funext (constrainedAnglesCLM_apply n)
    rw [←he]
    exact (constrainedAnglesCLM n).contDiff
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAngles θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((preferredAnchor_density_current_lift_contDiffAt (by omega) d B a τ rcut hr s j hreg
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
    have hc := (preferredAnchor_density_current_contDiffAt (by omega) d B a τ rcut hr s j hreg
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

/-- The literal named-anchor integral on the outward physical ray. -/
def preferredAnchorRadialIntegral (n : ℕ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (a : Fin (n+1)) (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (ε : ℝ) : ℂ :=
  preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε)

/-- Exact radial transport of the complete named-anchor integral. Its
entire divergence vanishes by the preceding literal periodic Stokes proof. -/
theorem preferred_anchor_integral_radial_hasDerivAt {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin (n+1)) {τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (j : ℕ)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m)
    (htan : ∀ ε∈Ioo 0 ε₀,∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (∑ i,preferredSourceAngularField (.anchor a) τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (preferredAnchorRadialIntegral n d B a τ rcut j)
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*preferredAnchorRadialIntegral n d B a τ rcut (j+1) ε) ε := by
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let X := fun θ : Fin n → ℝ => preferredLiftedAngles B.delta (constrainedAngles θ)
  let F := fun z : ℝ × (Fin n → ℝ) => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff
    B.p B.m rcut j (IsingBulk.Branch.radialParameter d.alpha z.1) (X z.2)
  let H := fun θ : Fin n → ℝ => fderiv ℝ F (ε,θ) (1,0)
  let C := fun θ : Fin n → ℝ => deriv (fun t : ℂ =>
    preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j t (X θ)) s
  let P := fun θ : Fin n → ℝ => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut (j+1) s (X θ)
  let D := fun θ : Fin n → ℝ => preferredAngularDivergence (preferredAnchorCurrent a τ B.p B.m rcut j s) (X θ)
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
    exact (preferredAnchor_density_current_lift_contDiffAt (by omega) d B a τ rcut hr
      (IsingBulk.Branch.radialParameter d.alpha t) j (hreg t ht) (constrainedAngles θ)).1.comp (t,θ) hmap.contDiffAt
  have hHC (θ : Fin n → ℝ) : H θ=ζ*C θ := by
    have hf : HasDerivAt (fun t : ℝ => F (t,θ)) (H θ) ε := by
      have hh := ((hF ε hε θ).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id' ε).prodMk (hasDerivAt_const ε θ))
      simpa only [Function.comp_def,H] using hh
    have hd := (preferredAnchor_parameter_differentiable (by omega) d B a τ rcut hr s j
      (hreg ε hε) (X θ) (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))).hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (ε:ℂ) := by
      simpa using ((hasDerivAt_id (ε:ℂ)).const_add 1).mul_const ζ
    have hd' : HasDerivAt (fun t : ℂ => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff
        B.p B.m rcut j t (X θ)) (C θ) ((1+(ε:ℂ))*ζ) := by
      simpa only [s,C,IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hd
    have hh : HasDerivAt (fun t : ℝ => F (t,θ)) (ζ*C θ) ε := by
      convert! (hd'.comp (ε:ℂ) hp).comp_ofReal using 1 <;>
        simp only [Function.comp_def,F,IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ,mul_comm]
    exact hf.unique hh
  have hP : Continuous P := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact ((preferredAnchor_density_current_lift_contDiffAt (by omega) d B a τ rcut hr s (j+1)
      (hreg ε hε) (constrainedAngles θ)).1.comp θ (contDiffAt_const.prodMk hχ.contDiffAt)).continuousAt
  have hD := preferred_anchor_ambient_divergence d B a τ rcut hr s j (hreg ε hε) (htan ε hε)
  have hPi := continuous_integrableOn_angularBox hP
  have hDi := continuous_integrableOn_angularBox hD.1
  have hrec (θ : Fin n → ℝ) : C θ=P θ+D θ := by
    change C θ=P θ+preferredAngularDivergence
      (fun x i => preferredSourceAngularField (.anchor a) τ B.p B.m s x i *
        preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j s x) (X θ)
    dsimp only [C,P]
    rw [preferredTransportedDensity_succ]
    exact (sub_add_cancel _ _).symm
  have hi : (∫ θ : Fin n → ℝ in angularBox n,H θ)=
      ζ*preferredAnchorRadialIntegral n d B a τ rcut (j+1) ε := by
    simp_rw [hHC,hrec]
    rw [integral_const_mul]
    have hadd : (∫ θ : Fin n → ℝ in angularBox n,P θ+D θ)=
        (∫ θ : Fin n → ℝ in angularBox n,P θ)+(∫ θ : Fin n → ℝ in angularBox n,D θ) := by
      convert! integral_add hPi hDi using 1
    rw [hadd,hD.2,add_zero]
    rfl
  have hd := preferred_angular_radial_integral_hasDerivAt F hε hF
  change HasDerivAt (preferredAnchorRadialIntegral n d B a τ rcut j)
    (∫ θ : Fin n → ℝ in angularBox n,H θ) ε at hd
  rw [hi] at hd
  exact hd

/-- All named anchors have the original exact integrated transport
identity at every derivative order and every positive particle number.
The regime is fixed before N and j; N=2 is included without an exception. -/
theorem preferred_actual_anchor_integral_identity (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ τ₀ ε₀ : ℝ,0<τ₀ ∧ 0<ε₀ ∧ ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ n : ℕ,∀ a : Fin (n+1),∀ j : ℕ,∀ ε : ℝ,0<ε → ε<ε₀ →
      iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)=
      preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  obtain ⟨τ₀,ε₀,hτ₀,hε₀,hgeom⟩ := preferred_actual_anchor_geometry d B
  refine ⟨τ₀,ε₀,hτ₀,hε₀,?_⟩
  intro τ hτ hτr rcut hr hrper n a
  let I := preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut 0
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  have hreg : ∀ ε∈Ioo 0 ε₀,∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m :=
    fun ε hε x hx => (hgeom (n+1) (by omega) ε τ hε.1 hε.2 hτ hτr x hx a).1
  have htan : ∀ ε∈Ioo 0 ε₀,∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (∑ i,preferredSourceAngularField (.anchor a) τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0 :=
    fun ε hε x hx => (hgeom (n+1) (by omega) ε τ hε.1 hε.2 hτ hτr x hx a).2
  have hI (ε : ℝ) (hε : 0<ε) : AnalyticAt ℂ I (IsingBulk.Branch.radialParameter d.alpha ε) :=
    preferredTransportedIntegral_zero_analyticAt n d B (.anchor a) hτ preferredPopulationCutoff rcut
      preferredPopulationCutoff_smooth hr hrper (preferredRadialTrace_im_pos d hε)
  intro j
  induction j with
  | zero => intro ε _ _; rfl
  | succ j ih =>
    intro ε hε hεr
    have he : (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        =ᶠ[𝓝 ε] preferredAnchorRadialIntegral n d B a τ rcut j := by
      filter_upwards [isOpen_Ioo.mem_nhds (show ε∈Ioo 0 ε₀ from ⟨hε,hεr⟩)] with t ht
      exact ih t ht.1 ht.2
    have hf : HasDerivAt (fun t : ℝ => iteratedDeriv j I (IsingBulk.Branch.radialParameter d.alpha t))
        (ζ*iteratedDeriv (j+1) I (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
      have ha : AnalyticAt ℂ I ((1+(ε:ℂ))*ζ) := by
        simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ] using hI ε hε
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ]
        using preferred_radial_iterated_hasDerivAt ζ ε j ha
    have hg := preferred_anchor_integral_radial_hasDerivAt d B a rcut hr j hreg htan ⟨hε,hεr⟩
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((d.alpha:ℂ)*Complex.I))
    exact hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)

end
end IsingBulk.Preferred22
