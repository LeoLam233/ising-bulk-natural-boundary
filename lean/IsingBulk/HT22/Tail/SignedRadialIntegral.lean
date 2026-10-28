import IsingBulk.HT22.Tail.SignedStokes
import IsingBulk.Preferred22.AngularRadialIntegral

/-! Differentiation on the genuine signed lifted angular torus. Compact
joint smoothness proves domination; no integral derivative or transported
endpoint is assumed. The affine total angle is never replaced by zero. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def signedLiftedIntegral {n : ℕ} (c δ : ℝ)
    (H : ℂ → (Fin (n+1) → ℝ) → ℂ) (s : ℂ) : ℂ :=
  ∫ q in angularBox n,H s (preferredLiftedAngles δ (constrainedAtTotal c q))

def signedLiftedRadialIntegral {n : ℕ} (c δ α : ℝ)
    (H : ℂ → (Fin (n+1) → ℝ) → ℂ) (ε : ℝ) : ℂ :=
  signedLiftedIntegral c δ H (IsingBulk.Branch.radialParameter α ε)

/-- Scalar differentiation under the unchanged Haar box; the factor exp(iα)
is exactly the derivative of the original radial parameter. -/
theorem signed_radial_integral_hasDerivAt {n : ℕ} (c δ α : ℝ)
    (H : ℂ → (Fin (n+1) → ℝ) → ℂ) {a b ε : ℝ} (hε : ε∈Ioo a b)
    (hF : ∀ u∈Ioo a b,∀ q : Fin n → ℝ,ContDiffAt ℝ ∞
      (fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter α z.1)
        (preferredLiftedAngles δ (constrainedAtTotal c z.2))) (u,q))
    (hH : ∀ q : Fin n → ℝ,DifferentiableAt ℂ
      (fun s => H s (preferredLiftedAngles δ (constrainedAtTotal c q)))
      (IsingBulk.Branch.radialParameter α ε)) :
    HasDerivAt (signedLiftedRadialIntegral c δ α H)
      (Complex.exp ((α:ℂ)*Complex.I)*signedLiftedIntegral c δ
        (fun s x => deriv (fun t => H t x) s) (IsingBulk.Branch.radialParameter α ε)) ε := by
  let ζ := Complex.exp ((α:ℂ)*Complex.I)
  let X := fun q : Fin n → ℝ => preferredLiftedAngles δ (constrainedAtTotal c q)
  let F := fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter α z.1) (X z.2)
  have hd := preferred_angular_radial_integral_hasDerivAt F hε hF
  have hder (q : Fin n → ℝ) : fderiv ℝ F (ε,q) (1,0)=
      ζ*deriv (fun s => H s (X q)) (IsingBulk.Branch.radialParameter α ε) := by
    have hf : HasDerivAt (fun u : ℝ => F (u,q)) (fderiv ℝ F (ε,q) (1,0)) ε := by
      have hFc : ContDiffAt ℝ ∞ F (ε,q) := hF ε hε q
      exact hFc.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id' ε).prodMk (hasDerivAt_const ε q))
    have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (ε:ℂ) := by
      simpa using ((hasDerivAt_id (ε:ℂ)).const_add 1).mul_const ζ
    have hh := ((hH q).hasDerivAt.comp_of_eq (ε:ℂ) hp
      (by simp only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,ζ])).comp_ofReal
    have hh' : HasDerivAt (fun u : ℝ => F (u,q))
        (ζ*deriv (fun s => H s (X q)) (IsingBulk.Branch.radialParameter α ε)) ε := by
      convert hh using 1 <;>
        simp only [F,X,Function.comp_def,IsingBulk.Branch.radialParameter,
          Complex.ofReal_add,Complex.ofReal_one,ζ,mul_comm]
    exact hf.unique hh'
  simp_rw [hder] at hd
  rw [integral_const_mul] at hd
  exact hd

/-- Exact flux-retaining radial recurrence. For an outside puncture cutoff,
J is the cutoff-gradient current; it cannot be silently discarded. -/
theorem signed_radial_integral_recurrence {n : ℕ} (c δ α : ℝ)
    (H G D J : ℂ → (Fin (n+1) → ℝ) → ℂ) {a b ε : ℝ} (hε : ε∈Ioo a b)
    (hF : ∀ u∈Ioo a b,∀ q : Fin n → ℝ,ContDiffAt ℝ ∞
      (fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter α z.1)
        (preferredLiftedAngles δ (constrainedAtTotal c z.2))) (u,q))
    (hH : ∀ q : Fin n → ℝ,DifferentiableAt ℂ
      (fun s => H s (preferredLiftedAngles δ (constrainedAtTotal c q)))
      (IsingBulk.Branch.radialParameter α ε))
    (hrec : ∀ q : Fin n → ℝ,
      let s := IsingBulk.Branch.radialParameter α ε
      let x := preferredLiftedAngles δ (constrainedAtTotal c q)
      deriv (fun t => H t x) s=G s x+D s x-J s x)
    (hG : IntegrableOn (fun q : Fin n → ℝ => G (IsingBulk.Branch.radialParameter α ε)
      (preferredLiftedAngles δ (constrainedAtTotal c q))) (angularBox n))
    (hD : IntegrableOn (fun q : Fin n → ℝ => D (IsingBulk.Branch.radialParameter α ε)
      (preferredLiftedAngles δ (constrainedAtTotal c q))) (angularBox n))
    (hJ : IntegrableOn (fun q : Fin n → ℝ => J (IsingBulk.Branch.radialParameter α ε)
      (preferredLiftedAngles δ (constrainedAtTotal c q))) (angularBox n))
    (hzero : signedLiftedIntegral c δ D (IsingBulk.Branch.radialParameter α ε)=0) :
    HasDerivAt (signedLiftedRadialIntegral c δ α H)
      (Complex.exp ((α:ℂ)*Complex.I)*
        (signedLiftedIntegral c δ G (IsingBulk.Branch.radialParameter α ε)-
          signedLiftedIntegral c δ J (IsingBulk.Branch.radialParameter α ε))) ε := by
  have hd := signed_radial_integral_hasDerivAt c δ α H hε hF hH
  have hi : signedLiftedIntegral c δ (fun s x => deriv (fun t => H t x) s)
      (IsingBulk.Branch.radialParameter α ε)=
      signedLiftedIntegral c δ G (IsingBulk.Branch.radialParameter α ε)-
        signedLiftedIntegral c δ J (IsingBulk.Branch.radialParameter α ε) := by
    unfold signedLiftedIntegral
    simp_rw [hrec]
    have hs := integral_sub (hG.add hD) hJ
    have ha := integral_add hG hD
    simp only [Pi.add_apply] at hs
    rw [hs,ha]
    change signedLiftedIntegral c δ G _+signedLiftedIntegral c δ D _-signedLiftedIntegral c δ J _=_
    rw [hzero,add_zero]
    rfl
  rw [hi] at hd
  exact hd

end
end IsingBulk.HT22.Tail
