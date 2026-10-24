import IsingBulk.Anisotropic.RegularEdges.TransferRoot
import IsingBulk.First.ResidueBounds
import IsingBulk.HT.Contour.PhysicalAngular

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour
open scoped BigOperators

/-- Rational complex pair weight, with no square roots of anisotropy. -/
def angularRootPair (a b q t : ℂ) : ℂ :=
  4*a*b*(Complex.sin ((q-t)/2))^2/(1-a*b)^2

def complexAngularWeight {N : ℕ} (lam : ℝ) (z : ℂ) (q : Fin N → ℂ) : ℂ :=
  (spectralT lam z/spectralS z)^(N.choose 2)*(spectralS z)⁻¹^N *
    (∏ i, 2*transferRoot lam z (q i)/(1-transferRoot lam z (q i)^2)) *
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),
      angularRootPair (transferRoot lam z (q i)) (transferRoot lam z (q j)) (q i) (q j))

def complexAngularDensity {N : ℕ} (lam : ℝ) (z : ℂ) (q : Fin N → ℂ) : ℂ :=
  complexAngularWeight lam z q *
    ((1+∏ i,transferRoot lam z (q i))/(1-∏ i,transferRoot lam z (q i)))

def unscaledAngularCoefficient (n : ℕ) (lam : ℝ) (z : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun q => complexAngularDensity lam z
      (fun i => (physicalDependentAngles n q i:ℂ)))

theorem complexAngularDensity_joint_analyticAt {N : ℕ} (hN : 0<N)
    {lam : ℝ} {z : ℂ} (hz : z∉spectralSet lam) (hS : spectralS z≠0) (q : Fin N → ℝ) :
    AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => complexAngularDensity lam p.1 p.2)
      (z,fun i => (q i:ℂ)) := by
  let p := (z,fun i => (q i:ℂ))
  have dz : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => t.1) p := analyticAt_fst
  have dq (i : Fin N) : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => t.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dr (i : Fin N) : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => transferRoot lam t.1 (t.2 i)) p := by
    exact AnalyticAt.fun_comp_of_eq
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i))
      (g := fun v : ℂ × ℂ => transferRoot lam v.1 v.2)
      (transferRoot_joint_analyticAt hz hS (q i)) (dz.prod (dq i)) rfl
  have hn (i : Fin N) := (transferRoot_bounds hz hS (q i)).2
  have hpair (i j : Fin N) : 1-transferRoot lam z (q i:ℂ)*transferRoot lam z (q j:ℂ)≠0 :=
    one_sub_mul_ne_zero_of_norm_lt_one (hn i) (hn j)
  have hZ : 1-∏ i, transferRoot lam z (q i:ℂ)≠0 :=
    one_sub_coordinateProduct_ne_zero hN hn
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dr i)
  have dS : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => spectralS t.1) p := Complex.analyticAt_sinh.comp dz
  have dT : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => spectralT lam t.1) p :=
    Complex.analyticAt_sinh.comp (analyticAt_const.mul dz)
  unfold complexAngularDensity complexAngularWeight
  refine (((((dT.div dS hS).pow _).mul ((dS.inv hS).pow _)).mul ?_).mul ?_).mul
    ((analyticAt_const.add dZ).div (analyticAt_const.sub dZ) hZ)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod
    intro j _
    exact ((((analyticAt_const.mul (dr i)).mul (dr j)).mul
      ((Complex.analyticAt_sin.comp (((dq i).sub (dq j)).div_const)).pow 2))).div
        ((analyticAt_const.sub ((dr i).mul (dr j))).pow 2) (pow_ne_zero _ (hpair i j))

end
end IsingBulk.Anisotropic.RegularEdges
