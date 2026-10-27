import IsingBulk.Preferred22.FrameWords
import IsingBulk.Preferred22.PhysicalTransport
import IsingBulk.Preferred22.AngularInverseJets

/-! Exact separated products for the genuine fixed-q source frames.
The analytic factor depends only on (s,q); the angular factor is genuinely
real smooth and includes the original cutoffs and inverse occupancy matrix. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def preferredSeparatedInverseFactor {N : ℕ} (a : Option (Fin N)) (b : Fin N)
    (z : ℂ × (Fin N → ℂ)) : ℂ :=
  match a with
  | none => preferredSourceUDot z.1 (z.2 b)
  | some k => if b=k then preferredSourceUQ z.1 (z.2 k) else 0

private theorem preferred_separated_sum_product {N : ℕ}
    (w f g : Fin N → ℂ) (A B : ℂ) :
    (∑ i, w i*(f i*B+A*g i))=(∑ i,w i*f i)*B+A*(∑ i,w i*g i) := by
  calc
    _ = ∑ i, ((w i*f i)*B+A*(w i*g i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]

/-- One literal frame maps a separated product to its exact finite sum of
separated products. In particular, every cutoff derivative remains real. -/
theorem preferredFrame_separated_step {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m) (s : ℂ) (θ : Fin N → ℝ)
    (hpoint : PreferredFramePoint τ δ p m s θ)
    (F : ℂ × (Fin N → ℂ) → ℂ) (G : (Fin N → ℝ) → ℂ)
    (hF : DifferentiableAt ℂ F (s,preferredSourceCoordinate τ p m s θ))
    (hG : DifferentiableAt ℝ G θ) (a : Option (Fin N)) :
    preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)*G x) [a] s θ=
      preferredComplexFrameJet F [a] (s,preferredSourceCoordinate τ p m s θ)*G θ+
      ∑ i, ∑ b, (F (s,preferredSourceCoordinate τ p m s θ)*
        preferredSeparatedInverseFactor a b (s,preferredSourceCoordinate τ p m s θ))*
        ((preferredContourMatrix τ p m θ)⁻¹ i b*deriv (fun u : ℝ => G (Function.update θ i u)) (θ i)) := by
  let q := preferredSourceCoordinate τ p m s θ
  let T := fun t x => F (t,preferredSourceCoordinate τ p m t x)
  let A := fun i b => deriv (fun x : ℝ => preferredSourceCoordinate τ p m s (Function.update θ i x) b) (θ i)
  let v := fun b => deriv (fun t : ℂ => preferredSourceCoordinate τ p m t θ b) s
  let f := fun i => deriv (fun x : ℝ => T s (Function.update θ i x)) (θ i)
  let g := fun i => deriv (fun x : ℝ => G (Function.update θ i x)) (θ i)
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
  have hTs : DifferentiableAt ℂ (fun t : ℂ => T t θ) s :=
    (hF.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hχs)).differentiableAt
  have hTi (i : Fin N) : DifferentiableAt ℝ (fun x : ℝ => T s (Function.update θ i x)) (θ i) :=
    ((hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) s).prodMk (hχ i)) (by simp only [Function.update_eq_self])).differentiableAt
  have hGi (i : Fin N) : DifferentiableAt ℝ (fun x : ℝ => G (Function.update θ i x)) (θ i) :=
    (hG.hasFDerivAt.comp_hasDerivAt_of_eq (θ i) (hasDerivAt_update θ i (θ i))
      (by simp only [Function.update_eq_self])).differentiableAt
  have hps : deriv (fun t : ℂ => T t θ*G θ) s=deriv (fun t : ℂ => T t θ) s*G θ :=
    (hTs.hasDerivAt.mul_const (G θ)).deriv
  have hpx (i : Fin N) : deriv (fun u : ℝ => T s (Function.update θ i u)*G (Function.update θ i u)) (θ i)=
      f i*G θ+T s θ*g i := by
    convert! ((hTi i).hasDerivAt.mul (hGi i).hasDerivAt).deriv using 1
    simp only [Function.update_eq_self,f,g]
  cases a with
  | none =>
    let w : Fin N → ℂ := (preferredContourMatrix τ p m θ)⁻¹.mulVec (fun b => preferredSourceUDot s (q b))
    have hsplit : preferredParameterFrame τ p m (fun t x => T t x*G x) s θ=
        preferredParameterFrame τ p m T s θ*G θ+T s θ*(∑ i,w i*g i) := by
      unfold preferredParameterFrame
      rw [hps]
      simp_rw [hpx]
      change deriv (fun t => T t θ) s*G θ+(∑ i,w i*(f i*G θ+T s θ*g i))=_
      rw [preferred_separated_sum_product]
      ring
    change preferredParameterFrame τ p m (fun t x => T t x*G x) s θ=_
    rw [hsplit,preferredParameterFrame_pullback τ δ p m hp hm s θ hpoint F hF]
    congr 1
    change F (s,q)*(∑ i,w i*g i)=_
    simp only [preferredSeparatedInverseFactor,w,Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    ring
  | some a =>
    let w : Fin N → ℂ := fun i => (preferredContourMatrix τ p m θ)⁻¹ i a*preferredSourceUQ s (q a)
    have hsplit : preferredCoordinateFrame τ p m a (fun t x => T t x*G x) s θ=
        preferredCoordinateFrame τ p m a T s θ*G θ+T s θ*(∑ i,w i*g i) := by
      unfold preferredCoordinateFrame
      simp_rw [hpx]
      exact preferred_separated_sum_product w f g (T s θ) (G θ)
    change preferredCoordinateFrame τ p m a (fun t x => T t x*G x) s θ=_
    rw [hsplit,preferredCoordinateFrame_pullback τ δ p m hp hm s θ hpoint F hF a]
    congr 1
    simp only [preferredSeparatedInverseFactor,mul_ite,ite_mul,mul_zero,zero_mul,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w,T,q,g]
    ring

end
end IsingBulk.Preferred22
