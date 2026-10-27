import IsingBulk.Preferred22.RegularTransport
import IsingBulk.Preferred22.SourceMarkedTransport

/-! The actual source frames pull back the canonical complex parameter/q
directions. Angular differentiation remains real throughout the proof. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Primitive local physical geometry used by the exact frame formulas. -/
structure PreferredFramePoint {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : Prop where
  delta_pos : 0<δ
  delta_lt : δ<Real.pi/2
  trace_re : 0<(temperatureTrace s).re
  trace_im : 0<(temperatureTrace s).im
  trace_cap : (temperatureTrace s).re<2*Real.cos δ
  angles : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ
  upper : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im
  matrix : (preferredContourMatrix τ p m θ).det≠0

theorem preferredCoordinateFrame_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,preferredSourceCoordinate τ p m s θ)) (a : Fin N) :
    preferredCoordinateFrame τ p m a
      (fun t x => F (t,preferredSourceCoordinate τ p m t x)) s θ =
      fderiv ℂ F (s,preferredSourceCoordinate τ p m s θ) (0,Pi.single a 1) := by
  let q := preferredSourceCoordinate τ p m s θ
  let A : Fin N → (Fin N → ℂ) := fun i b =>
    deriv (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ i x) b) (θ i)
  let w : Fin N → ℂ := fun i => (preferredContourMatrix τ p m θ)⁻¹ i a * preferredSourceUQ s (q a)
  let T := fderiv ℂ F (s,q)
  have hχ (i : Fin N) : HasDerivAt
      (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ i x)) (A i) (θ i) := by
    apply hasDerivAt_pi.mpr
    intro b
    exact (preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ b i
      hpoint.delta_pos hpoint.delta_lt hpoint.trace_re hpoint.trace_cap
      (hpoint.angles b) (hpoint.upper b)).differentiableAt.hasDerivAt
  have hder (i : Fin N) :
      deriv (fun x : ℝ => F (s,preferredSourceCoordinate τ p m s (Function.update θ i x))) (θ i)=
        T (0,A i) := by
    have hh := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) s).prodMk (hχ i))
      (by simp only [Function.update_eq_self])
    exact hh.deriv
  have hvec : (∑ i, w i • ((0:ℂ),A i))=((0:ℂ),Pi.single a 1) := by
    ext b
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum,Prod.smul_snd,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      have hh := preferredCoordinateFrame_sourceCoordinate τ δ p m hp hm s θ a b
        hpoint.delta_pos hpoint.delta_lt hpoint.trace_re hpoint.trace_cap hpoint.angles hpoint.upper hpoint.matrix
      simpa only [preferredCoordinateFrame,w,A,q,Pi.single_apply,eq_comm] using hh
  unfold preferredCoordinateFrame
  simp_rw [hder]
  change (∑ i, w i*T (0,A i))=T (0,Pi.single a 1)
  calc
    _ = T (∑ i, w i • ((0:ℂ),A i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_smul,smul_eq_mul]
    _ = _ := by rw [hvec]

theorem preferredParameterFrame_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,preferredSourceCoordinate τ p m s θ)) :
    preferredParameterFrame τ p m
      (fun t x => F (t,preferredSourceCoordinate τ p m t x)) s θ =
      fderiv ℂ F (s,preferredSourceCoordinate τ p m s θ) (1,0) := by
  let q := preferredSourceCoordinate τ p m s θ
  let A : Fin N → (Fin N → ℂ) := fun i b =>
    deriv (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ i x) b) (θ i)
  let v : Fin N → ℂ := fun b => deriv (fun t : ℂ => preferredSourceCoordinate τ p m t θ b) s
  let w : Fin N → ℂ := (preferredContourMatrix τ p m θ)⁻¹.mulVec (fun b => preferredSourceUDot s (q b))
  let T := fderiv ℂ F (s,q)
  have hχs : HasDerivAt (fun t : ℂ => preferredSourceCoordinate τ p m t θ) v s := by
    apply hasDerivAt_pi.mpr
    intro b
    exact (preferredSourceCoordinate_parameter_hasDerivAt τ δ p m s θ b
      hpoint.delta_pos hpoint.delta_lt hpoint.trace_re hpoint.trace_im hpoint.trace_cap
      (hpoint.angles b) (hpoint.upper b)).differentiableAt.hasDerivAt
  have hχ (i : Fin N) : HasDerivAt
      (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ i x)) (A i) (θ i) := by
    apply hasDerivAt_pi.mpr
    intro b
    exact (preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ b i
      hpoint.delta_pos hpoint.delta_lt hpoint.trace_re hpoint.trace_cap
      (hpoint.angles b) (hpoint.upper b)).differentiableAt.hasDerivAt
  have hderS : deriv (fun t : ℂ => F (t,preferredSourceCoordinate τ p m t θ)) s=T (1,v) :=
    (hF.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hχs)).deriv
  have hder (i : Fin N) :
      deriv (fun x : ℝ => F (s,preferredSourceCoordinate τ p m s (Function.update θ i x))) (θ i)=
        T (0,A i) := by
    have hh := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) s).prodMk (hχ i))
      (by simp only [Function.update_eq_self])
    exact hh.deriv
  have hvec : ((1:ℂ),v)+(∑ i, w i • ((0:ℂ),A i))=((1:ℂ),0) := by
    ext b
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_add,Prod.snd_sum,Prod.smul_snd,Pi.add_apply,
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      exact preferredParameterFrame_sourceCoordinate τ δ p m hp hm s θ b
        hpoint.delta_pos hpoint.delta_lt hpoint.trace_re hpoint.trace_im hpoint.trace_cap
        hpoint.angles hpoint.upper hpoint.matrix
  unfold preferredParameterFrame
  rw [hderS]
  simp_rw [hder]
  change T (1,v)+(∑ i, w i*T (0,A i))=T (1,0)
  calc
    _ = T ((1,v)+(∑ i, w i • ((0:ℂ),A i))) := by
      rw [map_add,map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_smul,smul_eq_mul]
    _ = _ := by rw [hvec]

end
end IsingBulk.Preferred22
