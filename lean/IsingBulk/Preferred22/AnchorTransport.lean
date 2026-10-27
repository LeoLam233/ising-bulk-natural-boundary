import IsingBulk.Preferred22.AnchorFrameJets
import IsingBulk.Preferred22.CellRegularity
import IsingBulk.Preferred22.PhysicalTransportIteration

/-! Exact coordinate Piola transport with the full original resolvent kept
inside the scalar amplitude. This is the anchored transport mechanism;
no frozen-phase identity is imposed on an anchor field. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual divergence of a chosen source cell in its fixed-q frame. -/
def preferredCellRegularDivergence {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ a,preferredCoordinateFrame τ p m a
    (fun t x => preferredResidualField cell t (preferredSourceCoordinate τ p m t x) a) s θ

/-- The literal scalar generator after factoring only the coordinate
Jacobian; the original product resolvent remains in its scalar input. -/
def preferredCellRegularTransportStep {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (p m : ℝ → ℝ) (G : ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredParameterFrame τ p m G s θ+
    (∑ a,preferredResidualField cell s (preferredSourceCoordinate τ p m s θ) a*
      preferredCoordinateFrame τ p m a G s θ)+
    preferredCellRegularDivergence cell τ p m s θ*G s θ

def preferredCellRegularSeed {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight cell η p m r θ:ℂ)*
    preferredRegularAmplitude s (preferredSourceCoordinate τ p m s θ)

def preferredCellRegularScalar {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (η p m r : ℝ → ℝ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => preferredCellRegularSeed cell τ η p m r
  | j+1 => preferredCellRegularTransportStep cell τ p m (preferredCellRegularScalar cell τ η p m r j)

theorem preferredCellRegularTransportStep_eq {N : ℕ} (cell : PreferredTransportCell N) (τ : ℝ) (p m : ℝ → ℝ)
    (G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) :
    preferredCellRegularTransportStep cell τ p m G s θ =
      deriv (fun t => G t θ) s -
        (∑ i, preferredSourceAngularField cell τ p m s θ i *
          deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i)) +
      (∑ a, preferredCoordinateFrame τ p m a
        (fun t x => preferredResidualField cell t (preferredSourceCoordinate τ p m t x) a) s θ) * G s θ := by
  let M := preferredContourMatrix τ p m θ
  let u := fun a => preferredSourceUDot s (preferredSourceCoordinate τ p m s θ a)
  let v := fun a => preferredSourceUQ s (preferredSourceCoordinate τ p m s θ a)
  let B := preferredResidualField cell s (preferredSourceCoordinate τ p m s θ)
  let g := fun i => deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i)
  have hb : (∑ a, B a*(∑ i, M⁻¹ i a*v a*g i)) =
      ∑ i, (M⁻¹.mulVec (fun a => v a*B a)) i*g i := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold preferredCellRegularTransportStep preferredCellRegularDivergence
  congr 1
  change deriv (fun t => G t θ) s+(∑ i, (M⁻¹.mulVec u) i*g i)+
    (∑ a, B a*(∑ i, M⁻¹ i a*v a*g i)) =
      deriv (fun t => G t θ) s-(∑ i, -(M⁻¹.mulVec (fun a => u a+v a*B a)) i*g i)
  rw [hb]
  change deriv (fun t => G t θ) s+(∑ i, (M⁻¹.mulVec u) i*g i)+
    (∑ i, (M⁻¹.mulVec (fun a => v a*B a)) i*g i) =
      deriv (fun t => G t θ) s-(∑ i, -(M⁻¹.mulVec (u+(fun a => v a*B a))) i*g i)
  simp only [Matrix.mulVec_add,Pi.add_apply,neg_mul,Finset.sum_neg_distrib,sub_neg_eq_add,
    add_mul,Finset.sum_add_distrib]
  ring


theorem preferredRealSourceChart_cell_velocity {N : ℕ} (cell : PreferredTransportCell N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace (s+(t:ℂ))).re) (hSi : 0<(temperatureTrace (s+(t:ℂ))).im)
    (hSδ : (temperatureTrace (s+(t:ℂ))).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace (s+(t:ℂ))-Complex.cos (deformedAngles τ p m θ i)).im) :
    (preferredRealCoordinateJacobian (preferredRealSourceChart τ p m s) (t,θ))⁻¹.mulVec
      (preferredRealCoordinateSpeed (preferredRealSourceChart τ p m s) (t,θ)-
        preferredResidualField cell (s+(t:ℂ)) (preferredSourceCoordinate τ p m (s+(t:ℂ)) θ))=
      preferredSourceAngularField cell τ p m (s+(t:ℂ)) θ := by
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  rw [preferredRealSourceChart_jacobian τ p m hp hm s t θ hSi hW,
    preferredRealSourceChart_speed τ p m hp hm s t θ hSi hW,
    preferredSourceJacobian_inverse τ δ p m hp' hm' (s+(t:ℂ)) θ hδ hδπ hS hSδ hθ hW]
  have hspeed (i : Fin N) := (preferredSourceCoordinate_parameter_hasDerivAt τ δ p m (s+(t:ℂ)) θ i
    hδ hδπ hS hSi hSδ (hθ i) (hW i)).deriv
  have hv (i : Fin N) : preferredSourceUQ (s+(t:ℂ)) (preferredSourceCoordinate τ p m (s+(t:ℂ)) θ i)≠0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular (s+(t:ℂ)) (deformedAngles τ p m θ i) δ
      hδ hδπ hS hSδ (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  funext i
  simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,
    Matrix.mul_diagonal,Matrix.mulVec,dotProduct,Pi.sub_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hspeed]
  field_simp [hv j]
  ring


theorem preferred_source_cell_residual_trace {N : ℕ} (cell : PreferredTransportCell N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hS : 0<(temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hB : DifferentiableAt ℝ
      (fun x : Fin N → ℝ => preferredResidualField cell s (preferredSourceCoordinate τ p m s x)) θ) :
    Matrix.trace ((preferredSourceJacobian τ p m s θ)⁻¹*
      preferredRealResidualJacobian
        (fun x => preferredResidualField cell s (preferredSourceCoordinate τ p m s x)) θ)=
      preferredCellRegularDivergence cell τ p m s θ := by
  have hd (a i : Fin N) : preferredRealResidualJacobian
      (fun x => preferredResidualField cell s (preferredSourceCoordinate τ p m s x)) θ a i=
      deriv (fun u : ℝ => preferredResidualField cell s
        (preferredSourceCoordinate τ p m s (Function.update θ i u)) a) (θ i) := by
    have hh := (differentiableAt_pi.mp hB a).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      (hasDerivAt_update θ i (θ i)) (by simp only [Function.update_eq_self])
    exact hh.deriv.symm
  unfold preferredCellRegularDivergence
  simp_rw [preferredCoordinateFrame_eq_inverse_jacobian τ δ p m hp hm s θ _ _
    hδ hδπ hS hSδ hθ hW]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,hd]
  exact Finset.sum_comm


theorem preferredCoordinateJacobian_cell_piola {N : ℕ} (cell : PreferredTransportCell N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hreg : PreferredSourceRegime τ δ p m (s,θ))
    (hU : ∀ i,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (s,preferredSourceCoordinate τ p m s θ i))
    (hBa : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    deriv (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s-
      (∑ i, deriv (fun u : ℝ =>
        preferredSourceAngularField cell τ p m s (Function.update θ i u) i*
          preferredCoordinateJacobian τ p m s (Function.update θ i u)) (θ i))=
      preferredCoordinateJacobian τ p m s θ*preferredCellRegularDivergence cell τ p m s θ := by
  obtain ⟨hS,hSi,hSδ,hθo,hW⟩ := hreg
  have hθ (i : Fin N) : θ i∈Set.Icc (-Real.pi-δ) δ := ⟨(hθo i).1.le,(hθo i).2.le⟩
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  let F := preferredRealSourceChart (N := N) τ p m s
  let B := fun x : Fin N → ℝ => preferredResidualField cell s (preferredSourceCoordinate τ p m s x)
  have hF : ContDiffAt ℝ ∞ F (0,θ) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      preferredRealSourceChart_contDiffAt τ p m hp hm s 0 θ (by simpa using hSi) (by simpa using hW)
  have hχ := preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hSi hW
  have hBc : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredResidualField cell z.1 (preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => (z.1,preferredSourceCoordinate τ p m z.1 z.2))
      (g := fun z : ℂ × (Fin N → ℂ) => preferredResidualField cell z.1 z.2) (s,θ)
      (hBa.contDiffAt.restrict_scalars ℝ) (contDiffAt_fst.prodMk hχ)
  have hB : DifferentiableAt ℝ B θ :=
    (ContDiffAt.comp (f := fun x : Fin N → ℝ => (s,x))
      (g := fun z : ℂ × (Fin N → ℝ) => preferredResidualField cell z.1 (preferredSourceCoordinate τ p m z.1 z.2)) θ
      hBc (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hA : preferredRealCoordinateJacobian F (0,θ)=preferredSourceJacobian τ p m s θ := by
    simpa only [Complex.ofReal_zero,add_zero] using preferredRealSourceChart_jacobian τ p m hp hm s 0 θ (by simpa using hSi) (by simpa using hW)
  have hAn : (preferredRealCoordinateJacobian F (0,θ)).det≠0 := by
    rw [hA]
    exact preferredSourceJacobian_det_ne_zero τ δ p m hp' hm' s θ hδ hδπ hS hSδ hθ hW hM
  have hpiola := preferred_real_coordinate_piola F B 0 θ hF hB hAn
  have hregEv : ∀ᶠ z : ℝ × (Fin N → ℝ) in 𝓝 (0,θ),
      PreferredSourceRegime τ δ p m (s+(z.1:ℂ),z.2) := by
    have hg : Continuous (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2)) := by fun_prop
    have ht : Filter.Tendsto (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2))
        (𝓝 (0,θ)) (𝓝 (s,θ)) := by simpa only [Complex.ofReal_zero,add_zero] using hg.tendsto (0,θ)
    exact ht.eventually ((preferredSourceRegime_isOpen τ δ p m hp.continuous hm.continuous).mem_nhds
      ⟨hS,hSi,hSδ,hθo,hW⟩)
  have hdet : (fun z : ℝ × (Fin N → ℝ) => (preferredRealCoordinateJacobian F z).det)
      =ᶠ[𝓝 (0,θ)] (fun z => preferredCoordinateJacobian τ p m (s+(z.1:ℂ)) z.2) := by
    filter_upwards [hregEv] with z hz
    obtain ⟨hzS,hzSi,hzSδ,hzθ,hzW⟩ := hz
    rw [preferredRealSourceChart_jacobian τ p m hp hm s z.1 z.2 hzSi hzW]
    exact preferredSourceJacobian_det τ δ p m hp' hm' _ _ hδ hδπ hzS hzSδ
      (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW
  have hvel : (fun x : Fin N → ℝ =>
      (preferredRealCoordinateJacobian F (0,x))⁻¹.mulVec
        (preferredRealCoordinateSpeed F (0,x)-B x))
      =ᶠ[𝓝 θ] preferredSourceAngularField cell τ p m s := by
    have ht : Filter.Tendsto (fun x : Fin N → ℝ => ((0:ℝ),x)) (𝓝 θ) (𝓝 (0,θ)) :=
      (continuous_const.prodMk continuous_id).tendsto θ
    filter_upwards [ht.eventually hregEv] with x hx
    simp only [Complex.ofReal_zero,add_zero] at hx
    obtain ⟨hxS,hxSi,hxSδ,hxθ,hxW⟩ := hx
    simpa only [Complex.ofReal_zero,add_zero] using
      preferredRealSourceChart_cell_velocity cell τ δ p m hp hm s 0 x hδ hδπ
        (by simpa using hxS) (by simpa using hxSi) (by simpa using hxSδ)
        (fun i => ⟨(hxθ i).1.le,(hxθ i).2.le⟩) (by simpa using hxW)
  have hdetParam : (fun u : ℝ => (preferredRealCoordinateJacobian F (u,θ)).det)
      =ᶠ[𝓝 0] (fun u : ℝ => preferredCoordinateJacobian τ p m (s+(u:ℂ)) θ) :=
    hdet.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto 0)
  have hdetAngular : (fun x : Fin N → ℝ => (preferredRealCoordinateJacobian F (0,x)).det)
      =ᶠ[𝓝 θ] preferredCoordinateJacobian τ p m s := by
    have hh := hdet.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto θ)
    simpa only [Function.comp_def,id_eq,Complex.ofReal_zero,add_zero] using hh
  have hflux (i : Fin N) :
      deriv (fun u : ℝ => ((preferredRealCoordinateJacobian F (0,Function.update θ i u))⁻¹.mulVec
        (preferredRealCoordinateSpeed F (0,Function.update θ i u)-B (Function.update θ i u))) i*
          (preferredRealCoordinateJacobian F (0,Function.update θ i u)).det) (θ i)=
      deriv (fun u : ℝ => preferredSourceAngularField cell τ p m s (Function.update θ i u) i*
        preferredCoordinateJacobian τ p m s (Function.update θ i u)) (θ i) := by
    have ht : Filter.Tendsto (fun u : ℝ => Function.update θ i u) (𝓝 (θ i)) (𝓝 θ) := by
      have hh : Continuous (fun u : ℝ => Function.update θ i u) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hvel.comp_tendsto ht,hdetAngular.comp_tendsto ht] with u huV huJ
    dsimp only [Function.comp_def] at huV huJ
    rw [huV,huJ]
  have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  have hJ := preferredCoordinateJacobian_parameter_analyticAt τ p m s θ hSi hW hU hv
  have hJ0 : HasDerivAt (fun t : ℂ => preferredCoordinateJacobian τ p m t θ)
      (deriv (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s) (s+(0:ℂ)) := by
    simpa only [add_zero] using hJ.differentiableAt.hasDerivAt
  have hJreal : HasDerivAt (fun u : ℝ => preferredCoordinateJacobian τ p m (s+(u:ℂ)) θ)
      (deriv (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s) 0 := by
    convert! (hJ0.comp (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_add s)).comp_ofReal using 1
    simp only [mul_one]
  rw [hdetParam.deriv_eq,hJreal.deriv] at hpiola
  simp_rw [hflux] at hpiola
  rw [hA,preferredSourceJacobian_det τ δ p m hp' hm' s θ hδ hδπ hS hSδ hθ hW,
    preferred_source_cell_residual_trace cell τ δ p m hp' hm' s θ hδ hδπ hS hSδ hθ hW hB] at hpiola
  exact hpiola


/-- The physical source normalization factors only J and retains the full
unchanged normalized amplitude in the scalar seed, for every named cell. -/
theorem preferredPhysicalSeed_cell_factorized {N : ℕ} (cell : PreferredTransportCell N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hS : 0<(temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i,θ i∈Icc (-Real.pi-δ) δ)
    (hW : ∀ i,0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredPhysicalSeed cell τ η p m r s θ=
      preferredCoordinateJacobian τ p m s θ*preferredCellRegularSeed cell τ η p m r s θ := by
  rw [preferred_one_sided_seed_eq_regular cell τ δ η p m r s θ hδ hδπ hS hSδ hθ hW]
  unfold preferredCellRegularSeed
  ring

end
end IsingBulk.Preferred22
