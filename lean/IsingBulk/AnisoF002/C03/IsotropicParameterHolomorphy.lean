import IsingBulk.AnisoF002.C03.IsotropicInteriorMultiplier
import IsingBulk.AnisoF002.C03.IsotropicActualWordGerms

/-!
# Parameter holomorphy of the full physical transported density

Real angular cutoffs remain real. For fixed actual real angles, their
separated-word factors are constant in the complex parameter, while the
whole analytic word and the true coordinate determinant are holomorphic.
This identifies the real radial derivative with the exact scalar current.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

variable {N : ℕ}

theorem actualPhysicalPhase_parameter_analyticAt (η τ ξ : ℝ) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im) (i : Fin N) :
    AnalyticAt ℂ (fun u => actualPhysicalPhase η τ ξ (u, θ) i) s := by
  have hd : AnalyticAt ℂ
      (fun u : ℂ => isotropicDispersion (u, actualHomotopyAngle η τ ξ θ i)) s := by
    change AnalyticAt ℂ (fun u : ℂ => u - Complex.cos (actualHomotopyAngle η τ ξ θ i)) s
    exact analyticAt_id.sub analyticAt_const
  exact (upperPhysicalPhase_analyticAt _
    (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i)).comp
      (f := fun u : ℂ => isotropicDispersion (u, actualHomotopyAngle η τ ξ θ i))
      hd

theorem actual_regular_map_parameter_analyticAt (η τ ξ : ℝ) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im) :
    AnalyticAt ℂ (fun u => regularJointMap (actualPhysicalCoordinate η τ ξ) (u, θ)) s := by
  apply analyticAt_id.prod
  apply AnalyticAt.pi
  intro i
  change AnalyticAt ℂ (fun u : ℂ => actualHomotopyAngle η τ ξ θ i +
    actualPhysicalPhase η τ ξ (u, θ) i) s
  exact analyticAt_const.add (actualPhysicalPhase_parameter_analyticAt η τ ξ θ s hη hτ hξ hs i)

theorem actualCoordinateDeterminant_parameter_analyticAt (η τ ξ : ℝ) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im) :
    AnalyticAt ℂ (fun u => actualCoordinateDeterminant η τ ξ (u, θ)) s := by
  have hm (i : Fin N) : AnalyticAt ℂ (fun u => actualCoordinateMultiplier η τ ξ (u, θ) i) s := by
    change AnalyticAt ℂ (fun u : ℂ => 1 - Complex.sin (actualHomotopyAngle η τ ξ θ i) /
      Complex.sin (actualPhysicalPhase η τ ξ (u, θ) i)) s
    exact analyticAt_const.sub (analyticAt_const.div
      (Complex.analyticAt_sin.comp (actualPhysicalPhase_parameter_analyticAt η τ ξ θ s hη hτ hξ hs i))
      (upperPhysicalPhase_sin_ne_zero _
        (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i)))
  have ha : AnalyticAt ℂ (fun u => (actualBalancedJacobian η τ ξ θ).det *
      ∏ i, actualCoordinateMultiplier η τ ξ (u, θ) i) s :=
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => hm i))
  apply ha.congr
  filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hs)] with u hu
  exact (actualCoordinateDeterminant_factorization η τ ξ (u, θ)
    (fun i => actual_balanced_homotopy_sheet u hu η τ ξ hη hτ hξ θ i)).symm

theorem actualSignedProductKernel_parameter_analyticAt (hN : 0 < N) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im) :
    AnalyticAt ℂ (fun u => actualSignedProductKernel σ η τ ξ (u, θ)) s := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hp : AnalyticAt ℂ (fun u => actualTotalPhase η τ ξ (u, θ)) s :=
    Finset.analyticAt_fun_sum _ (fun i _ => actualPhysicalPhase_parameter_analyticAt η τ ξ θ s hη hτ hξ hs i)
  change AnalyticAt ℂ (fun u : ℂ => physicalPhaseKernel σ (actualTotalPhase η τ ξ (u, θ))) s
  exact (physicalPhaseKernel_analyticAt σ (actualTotalPhase η τ ξ (s, θ))
    (actualSignedProductKernel_denominator σ hσ η τ ξ hη hτ hξ (s, θ) hs)).comp
      (f := fun u : ℂ => actualTotalPhase η τ ξ (u, θ)) hp

theorem actualTransportDensityMultiplier_parameter_analyticAt (hN : 0 < N) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (η τ ξ : ℝ) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im) :
    AnalyticAt ℂ (fun u => actualTransportDensityMultiplier σ η τ ξ (u, θ)) s :=
  (actualCoordinateDeterminant_parameter_analyticAt η τ ξ θ s hη hτ hξ hs).mul
    (actualSignedProductKernel_parameter_analyticAt hN σ hσ η τ ξ θ s hη hτ hξ hs)

theorem actualSeparatedWordSum_parameter_analyticAt (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ) (n : ℕ)
    (θ : Fin N → ℝ) (s : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im)
    (hB : AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ))) :
    AnalyticAt ℂ (fun u => actualSeparatedWordSum η τ ξ F g n (u, θ)) s := by
  apply Finset.analyticAt_fun_sum
  intro w _
  change AnalyticAt ℂ (fun u : ℂ =>
    transportAnalyticWord (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      rightCutoffTransportCoefficient F n w
        (regularJointMap (actualPhysicalCoordinate η τ ξ) (u, θ)) *
      transportAngularWord (actualBalancedInverseEntry η τ ξ) g n w θ) s
  exact ((transportAnalyticWord_analyticAt _ _ _ _ hB hK hF n w).comp
    (f := fun u : ℂ => regularJointMap (actualPhysicalCoordinate η τ ξ) (u, θ))
    (actual_regular_map_parameter_analyticAt η τ ξ θ s hη hτ hξ hs)).mul analyticAt_const

theorem actualTransportDescendant_parameter_analyticAt (η τ ξ : ℝ)
    (F : RegularJointSpace N → ℂ) (g : (Fin N → ℝ) → ℂ)
    (hA : ∀ i j : Fin N, ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i j))
    (hg : ContDiff ℝ ∞ g) (θ : Fin N → ℝ) (s : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hs : 0 < s.im)
    (hχ : ∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ))
    (hB : AnalyticAt ℂ (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hK : ∀ j, AnalyticAt ℂ (fun p : RegularJointSpace N => rightCutoffTransportCoefficient p j)
      (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hF : AnalyticAt ℂ F (regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)))
    (hdet : actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0)
    (hV : ∀ᶠ y in 𝓝 (s, θ), ∀ i, actualCovarianceAngularVelocity η τ ξ i y =
      -∑ j, actualBalancedInverseEntry η τ ξ i j y.2 *
        rightCutoffTransportCoefficient (regularJointMap (actualPhysicalCoordinate η τ ξ) y) j)
    (n : ℕ) :
    AnalyticAt ℂ (fun u => actualTransportDescendant η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n (u, θ)) s := by
  have he := actualTransportDescendant_germ_eq_separated_words η τ ξ F g hA hg (s, θ)
    hχ hB hK hF hdet hV n
  have hm : ContinuousAt (fun u : ℂ => (u, θ)) s := continuousAt_id.prodMk continuousAt_const
  have he' : (fun u => actualTransportDescendant η τ ξ
      (fun y => F (regularJointMap (actualPhysicalCoordinate η τ ξ) y) * g y.2) n (u, θ))
      =ᶠ[𝓝 s] (fun u => actualSeparatedWordSum η τ ξ F g n (u, θ)) := hm.eventually he
  exact (actualSeparatedWordSum_parameter_analyticAt η τ ξ F g n θ s hη hτ hξ hs hB hK hF).congr
    he'.symm

theorem scalarPartial_parameter_eq_complex_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ × E → ℂ) (s : ℂ) (θ : E)
    (hf : DifferentiableAt ℝ f (s, θ))
    (hs : DifferentiableAt ℂ (fun u => f (u, θ)) s) :
    scalarPartial f (1, 0) (s, θ) = deriv (fun u => f (u, θ)) s := by
  have hm : HasFDerivAt (fun u : ℂ => (u, θ)) (ContinuousLinearMap.inl ℝ ℂ E) s := by
    exact (hasFDerivAt_id (𝕜 := ℝ) s).prodMk (hasFDerivAt_const _ _)
  have hh := hf.hasFDerivAt.comp s hm
  simp only [Function.comp_def] at hh
  have he := hh.unique (hs.hasFDerivAt.restrictScalars ℝ)
  have hv := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) he
  change fderiv ℝ f (s, θ) (1, 0) = fderiv ℂ (fun u => f (u, θ)) s 1 at hv
  simpa only [scalarPartial, fderiv_apply_one_eq_deriv] using hv

end
end IsingBulk.AnisoF002.Isotropic
