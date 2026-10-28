import IsingBulk.HT22.Tail.CoordinateCalculus

/-! Exact fixed-v pullback for the real smooth angular frames. Adapted generic
linear differential chain rules; all parameter coordinate identities are new. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem coordinateFrame_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,sourceCoordinate τ p m s θ)) (a : Fin N) :
    coordinateFrame τ p m a
      (fun t x => F (t,sourceCoordinate τ p m t x)) s θ =
      fderiv ℂ F (s,sourceCoordinate τ p m s θ) (0,Pi.single a 1) := by
  let q := sourceCoordinate τ p m s θ
  let A : Fin N → (Fin N → ℂ) := fun i b =>
    deriv (fun x : ℝ => sourceCoordinate τ p m s (Function.update θ i x) b) (θ i)
  let w : Fin N → ℂ := fun i => (preferredContourMatrix τ p m θ)⁻¹ i a * inverseV s (q a)
  let T := fderiv ℂ F (s,q)
  have hχ (i : Fin N) : HasDerivAt
      (fun x : ℝ => sourceCoordinate τ p m s (Function.update θ i x)) (A i) (θ i) := by
    apply hasDerivAt_pi.mpr
    intro b
    exact (sourceCoordinate_hasDerivAt τ δ p m hp hm s θ hpoint b i).differentiableAt.hasDerivAt
  have hder (i : Fin N) :
      deriv (fun x : ℝ => F (s,sourceCoordinate τ p m s (Function.update θ i x))) (θ i)=
        T (0,A i) := by
    have hh := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) s).prodMk (hχ i))
      (by simp only [Function.update_eq_self])
    exact hh.deriv
  have hvec : (∑ i, w i • ((0:ℂ),A i))=((0:ℂ),Pi.single a 1) := by
    ext b
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum,Prod.smul_snd,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      have hh := coordinateFrame_sourceCoordinate τ δ p m hp hm s θ hpoint a b
      simpa only [coordinateFrame,w,A,q,Pi.single_apply,eq_comm] using hh
  unfold coordinateFrame
  simp_rw [hder]
  change (∑ i, w i*T (0,A i))=T (0,Pi.single a 1)
  calc
    _ = T (∑ i, w i • ((0:ℂ),A i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_smul,smul_eq_mul]
    _ = _ := by rw [hvec]

theorem parameterFrame_pullback {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,sourceCoordinate τ p m s θ)) :
    parameterFrame τ p m
      (fun t x => F (t,sourceCoordinate τ p m t x)) s θ =
      fderiv ℂ F (s,sourceCoordinate τ p m s θ) (1,0) := by
  let q := sourceCoordinate τ p m s θ
  let A : Fin N → (Fin N → ℂ) := fun i b =>
    deriv (fun x : ℝ => sourceCoordinate τ p m s (Function.update θ i x) b) (θ i)
  let v : Fin N → ℂ := fun b => deriv (fun t : ℂ => sourceCoordinate τ p m t θ b) s
  let w : Fin N → ℂ := (preferredContourMatrix τ p m θ)⁻¹.mulVec (fun b => inverseT s (q b))
  let T := fderiv ℂ F (s,q)
  have hχs : HasDerivAt (fun t : ℂ => sourceCoordinate τ p m t θ) v s := by
    apply hasDerivAt_pi.mpr
    intro b
    exact (sourceCoordinate_parameter_hasDerivAt τ δ p m s θ hpoint b).differentiableAt.hasDerivAt
  have hχ (i : Fin N) : HasDerivAt
      (fun x : ℝ => sourceCoordinate τ p m s (Function.update θ i x)) (A i) (θ i) := by
    apply hasDerivAt_pi.mpr
    intro b
    exact (sourceCoordinate_hasDerivAt τ δ p m hp hm s θ hpoint b i).differentiableAt.hasDerivAt
  have hderS : deriv (fun t : ℂ => F (t,sourceCoordinate τ p m t θ)) s=T (1,v) :=
    (hF.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hχs)).deriv
  have hder (i : Fin N) :
      deriv (fun x : ℝ => F (s,sourceCoordinate τ p m s (Function.update θ i x))) (θ i)=
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
      exact parameterFrame_sourceCoordinate τ δ p m hp hm s θ hpoint b
  unfold parameterFrame
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
end IsingBulk.HT22.Tail
