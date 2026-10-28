import IsingBulk.HT22.Tail.SourceMixedCalculus
import IsingBulk.HT22.Transport.AngularField

/-! Exact unshifted-coordinate derivatives and angular frames. Parameter
jets are taken at fixed v, never silently at fixed moving q. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem inverseT_moving_adapter (t v : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v))
    (hb : DifferentiableAt ℂ preferredMovingBranch t) :
    inverseT t v=preferredSourceUDot t (v-preferredMovingBranch t)-
      inverseV t v*deriv preferredMovingBranch t := by
  let q := v-preferredMovingBranch t
  let F : ℂ × ℂ → ℂ := fun z => regularInverse z.1 z.2
  have he : (fun s => F (s,q+preferredMovingBranch s))=
      (fun s => preferredMovingInverse s q) := by
    funext s
    simp only [F,regularInverse_moving_adapter,add_sub_cancel_right]
  have hg := (hasDerivAt_id t).prodMk (hb.hasDerivAt.const_add q)
  have ht : (t,q+preferredMovingBranch t)=(t,v) := by dsimp [q]; simp
  have hd := hU.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq t hg ht.symm
  have hd' := hd.deriv
  change deriv (fun s => F (s,q+preferredMovingBranch s)) t = _ at hd'
  rw [he] at hd'
  have hv := inverseVJoint_eq t v hU
  have hu := inverseTJoint_eq t v hU
  have hsplit : (1,deriv preferredMovingBranch t)=
      ((1:ℂ),0)+(deriv preferredMovingBranch t) • ((0:ℂ),1) := by
    ext <;> simp
  rw [hsplit,map_add,map_smul] at hd'
  change preferredSourceUDot t q=inverseTJoint (t,v)+
    deriv preferredMovingBranch t*inverseVJoint (t,v) at hd'
  rw [hu,hv] at hd'
  dsimp only [q] at hd'
  linear_combination -hd'

theorem source_inverseV_ne_zero {N : ℕ} {τ δ : ℝ} {p m : ℝ → ℝ}
    {t : ℂ} {θ : Fin N → ℝ} (h : PreferredFramePoint τ δ p m t θ) (i : Fin N) :
    inverseV t (sourceCoordinate τ p m t θ i)≠0 := by
  rw [inverseV_moving_adapter,sourceCoordinate_moving_adapter]
  exact (preferred_global_one_sided_q_regular t (deformedAngles τ p m θ i) δ
    h.delta_pos h.delta_lt h.trace_re h.trace_cap
    (by simpa only [deformedAngles_re] using (h.angles i).1)
    (by simpa only [deformedAngles_re] using (h.angles i).2) (h.upper i)).2

theorem sourceCoordinate_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (t : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m t θ) (i j : Fin N) :
    HasDerivAt (fun x : ℝ => sourceCoordinate τ p m t (Function.update θ j x) i)
      ((inverseV t (sourceCoordinate τ p m t θ i))⁻¹*preferredContourMatrix τ p m θ i j)
      (θ j) := by
  have hh := (preferredSourceCoordinate_hasDerivAt τ δ p m hp hm t θ i j
    h.delta_pos h.delta_lt h.trace_re h.trace_cap (h.angles i) (h.upper i)).add_const
      (preferredMovingBranch t)
  rw [inverseV_moving_adapter,sourceCoordinate_moving_adapter]
  convert hh using 1
  funext x
  exact sub_eq_iff_eq_add.mp (sourceCoordinate_moving_adapter τ p m t (Function.update θ j x) i)

theorem sourceCoordinate_parameter_hasDerivAt {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m t θ) (i : Fin N) :
    HasDerivAt (fun s : ℂ => sourceCoordinate τ p m s θ i)
      (-inverseT t (sourceCoordinate τ p m t θ i)/
        inverseV t (sourceCoordinate τ p m t θ i)) t := by
  have hb := (preferredMovingBranch_analyticAt_upper t h.trace_im).differentiableAt
  have hh := (preferredSourceCoordinate_parameter_hasDerivAt τ δ p m t θ i
    h.delta_pos h.delta_lt h.trace_re h.trace_im h.trace_cap (h.angles i) (h.upper i)).add hb.hasDerivAt
  have hu := inverseT_moving_adapter t (sourceCoordinate τ p m t θ i)
    (framePoint_inverse_analytic h i) hb
  have hv := source_inverseV_ne_zero h i
  rw [sourceCoordinate_moving_adapter] at hu
  convert hh using 1
  · funext s
    exact sub_eq_iff_eq_add.mp (sourceCoordinate_moving_adapter τ p m s θ i)
  · rw [hu,←sourceCoordinate_moving_adapter τ p m t θ i,←inverseV_moving_adapter]
    field_simp
    ring

theorem coordinateFrame_eq_shared {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (a : Fin N) (F : ℂ → (Fin N → ℝ) → ℂ) :
    coordinateFrame τ p m a F=preferredCoordinateFrame τ p m a F := by
  funext t θ
  simp only [coordinateFrame,preferredCoordinateFrame,inverseV_moving_adapter,
    sourceCoordinate_moving_adapter]

theorem coordinateFrame_sourceCoordinate {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ) (a b : Fin N) :
    coordinateFrame τ p m a (fun t x => sourceCoordinate τ p m t x b) s θ=
      if b=a then 1 else 0 := by
  have hh := preferredCoordinateFrame_sourceCoordinate τ δ p m hp hm s θ a b
    h.delta_pos h.delta_lt h.trace_re h.trace_cap h.angles h.upper h.matrix
  unfold preferredCoordinateFrame at hh
  simp_rw [(preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ b _
    h.delta_pos h.delta_lt h.trace_re h.trace_cap (h.angles b) (h.upper b)).deriv] at hh
  unfold coordinateFrame
  simp_rw [(sourceCoordinate_hasDerivAt τ δ p m hp hm s θ h b _).deriv]
  simpa only [inverseV_moving_adapter,sourceCoordinate_moving_adapter] using hh

theorem parameterFrame_sourceCoordinate {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (h : PreferredFramePoint τ δ p m s θ) (b : Fin N) :
    parameterFrame τ p m (fun t x => sourceCoordinate τ p m t x b) s θ=0 := by
  unfold parameterFrame
  rw [(sourceCoordinate_parameter_hasDerivAt τ δ p m s θ h b).deriv]
  simp_rw [(sourceCoordinate_hasDerivAt τ δ p m hp hm s θ h b _).deriv]
  let M := preferredContourMatrix τ p m θ
  let u := fun a => inverseT s (sourceCoordinate τ p m s θ a)
  let v := inverseV s (sourceCoordinate τ p m s θ b)
  have he : (∑ i, (M⁻¹.mulVec u) i*(v⁻¹*M b i))=v⁻¹*u b := by
    calc
      _ = v⁻¹*(M.mulVec (M⁻¹.mulVec u)) b := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr h.matrix),Matrix.one_mulVec]
  change -u b/v+(∑ i, (M⁻¹.mulVec u) i*(v⁻¹*M b i))=0
  rw [he]
  ring

end
end IsingBulk.HT22.Tail
