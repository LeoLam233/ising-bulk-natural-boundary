import IsingBulk.HT22.Tail.SignedRadialIntegral

/-! Pointwise radial chain rule and the genuine continuity of the parameter
integrand obtained from joint smoothness, before invoking periodic Stokes. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem radial_point_hasDerivAt (α ε : ℝ) (H : ℂ → ℂ)
    (hH : DifferentiableAt ℂ H (IsingBulk.Branch.radialParameter α ε)) :
    HasDerivAt (fun u : ℝ => H (IsingBulk.Branch.radialParameter α u))
      (Complex.exp ((α:ℂ)*Complex.I)*deriv H (IsingBulk.Branch.radialParameter α ε)) ε := by
  let ζ := Complex.exp ((α:ℂ)*Complex.I)
  have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (ε:ℂ) := by
    simpa using ((hasDerivAt_id (ε:ℂ)).const_add 1).mul_const ζ
  have hh := (hH.hasDerivAt.comp_of_eq (ε:ℂ) hp
    (by simp only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ])).comp_ofReal
  convert hh using 1 <;>
    simp only [Function.comp_def,IsingBulk.Branch.radialParameter,
      Complex.ofReal_add,Complex.ofReal_one,ζ,mul_comm]

theorem signed_parameter_integrand_continuous {n : ℕ} (c δ α ε : ℝ)
    (H : ℂ → (Fin (n+1) → ℝ) → ℂ)
    (hF : ∀ q : Fin n → ℝ,ContDiffAt ℝ ∞
      (fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter α z.1)
        (preferredLiftedAngles δ (constrainedAtTotal c z.2))) (ε,q))
    (hH : ∀ q : Fin n → ℝ,DifferentiableAt ℂ
      (fun s => H s (preferredLiftedAngles δ (constrainedAtTotal c q)))
      (IsingBulk.Branch.radialParameter α ε)) :
    Continuous (fun q : Fin n → ℝ =>
      deriv (fun s => H s (preferredLiftedAngles δ (constrainedAtTotal c q)))
        (IsingBulk.Branch.radialParameter α ε)) := by
  let ζ := Complex.exp ((α:ℂ)*Complex.I)
  let F := fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter α z.1)
    (preferredLiftedAngles δ (constrainedAtTotal c z.2))
  let C := fun q : Fin n → ℝ => deriv (fun s => H s (preferredLiftedAngles δ (constrainedAtTotal c q)))
    (IsingBulk.Branch.radialParameter α ε)
  let D := fun q : Fin n → ℝ => fderiv ℝ F (ε,q) (1,0)
  have hD : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hh := ((hF q).fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply
      (contDiffAt_const (c := ((1:ℝ),(0:Fin n → ℝ))))
    exact hh.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hDC (q : Fin n → ℝ) : D q=ζ*C q := by
    have hf : HasDerivAt (fun u : ℝ => F (u,q)) (D q) ε := by
      have hFc : ContDiffAt ℝ ∞ F (ε,q) := hF q
      exact hFc.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id' ε).prodMk (hasDerivAt_const ε q))
    exact hf.unique (radial_point_hasDerivAt α ε _ (hH q))
  have he : C=fun q => ζ⁻¹*D q := by
    funext q
    rw [hDC]
    exact (inv_mul_cancel_left₀ (Complex.exp_ne_zero _) (C q)).symm
  change Continuous C
  rw [he]
  exact continuous_const.mul hD

end
end IsingBulk.HT22.Tail
