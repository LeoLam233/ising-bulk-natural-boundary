import IsingBulk.Joint.Negative.FamilyAllParticleCauchy
import IsingBulk.Joint.Negative.CanonicalJets
import IsingBulk.Anisotropic.NegativeDominance.ParticleWeightScaling
import IsingBulk.Joint.Negative.UpperDensity

/-! # Literal boundary-jet attachment for arbitrary complex families -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
  IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Joint.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- The actual upper unscaled coordinate and physical particle scale. -/
def physicalNegativeParameter (b : ℝ) (K : Coupling) (amp : ℂ) : NumeratorParameter :=
  (transferC K+transferB K-b,(-T K/S K,S K/amp))

theorem physicalNegativeParameter_analyticAt {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {curve : E→Coupling} {amp : E→ℂ} {x : E} {b : ℝ}
    (hc : AnalyticAt ℂ curve x) (ha : AnalyticAt ℂ amp x)
    (hS : S (curve x)≠0) (hamp : amp x≠0) :
    AnalyticAt ℂ (fun x => physicalNegativeParameter b (curve x) (amp x)) x := by
  have hs : AnalyticAt ℂ (fun x => S (curve x)) x :=
    Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)
  have ht : AnalyticAt ℂ (fun x => T (curve x)) x :=
    Complex.analyticAt_sinh.comp (analyticAt_snd.comp hc)
  have hA : AnalyticAt ℂ (fun x => A (curve x)) x :=
    (Complex.analyticAt_cosh.comp (analyticAt_fst.comp hc)).mul
      (Complex.analyticAt_cosh.comp (analyticAt_snd.comp hc))
  exact (((hA.div hs hS).add (ht.div hs hS)).sub analyticAt_const).prod
    ((ht.neg.div hs hS).prod (hs.div ha hamp))

theorem physicalNegativeParameter_zero {b : ℝ} {K : Coupling} {amp : ℂ}
    (hS : S K≠0) (he : A K+T K=(b:ℂ)*S K) :
    (physicalNegativeParameter b K amp).1=0 := by
  change A K/S K+T K/S K-(b:ℂ)=0
  rw [←add_div,he,mul_div_cancel_right₀ _ hS,sub_self]

/-- The complete shifted density, including its sign and normalization,
coincides as an actual analytic germ with the independent full integrand. -/
theorem paperShiftedDensity_independent_germ (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ}
    (hc : AnalyticAt ℂ curve 0) (hS : S (curve 0)≠0)
    (he : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) (v : Fin n→ℝ) :
    (fun t => paperShiftedDensity n curve amp t v) =ᶠ[𝓝 (0:ℂ)]
      (fun t => (((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n)*
        (-1:ℂ)^((n+1).choose 2)*
        independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
          (negativeShiftedAngles n v)) := by
  let q := physicalDependentAngles n (fun k => v k+Real.pi)
  have hq : ∑i,q i=0 := physicalDependentAngles_sum_zero n _
  have hr (i : Fin (n+1)) : AnalyticAt ℂ
      (fun t => continuedTransferRoot (curve t) (q i:ℂ)) 0 :=
    (continuedTransferRoot_negative_joint_analyticAt hS he hb hB (q i)).comp
      (f := fun t => (curve t,(q i:ℂ))) (hc.prod analyticAt_const)
  have hp := Finset.univ.analyticAt_fun_prod (fun i _ => hr i)
  have hZ0 : 1-∏i,continuedTransferRoot (curve 0) (q i:ℂ)≠0 :=
    by
      intro hz
      have hlt := continuedTransferRoot_odd_negative_product_lt_one hn hS he hb hB q hq
      rw [←sub_eq_zero.mp hz,norm_one] at hlt
      exact lt_irrefl _ hlt
  have hZ := (analyticAt_const.sub hp).continuousAt.eventually_ne hZ0
  filter_upwards [hZ] with t ht
  have he' : transferC (curve t)+transferB (curve t)=
      (b:ℂ)+(physicalNegativeParameter b (curve t) (amp t)).1 := by
    dsimp [physicalNegativeParameter]; ring
  have hd := continuedAngularDensity_eq_negative_edgeFullIntegrand
    (B := fun _ => -T (curve t)/S (curve t)) (S := fun _ => S (curve t))
    rfl rfl he' q ht
  have hw : edgeFullIntegrand b (fun _ => -T (curve t)/S (curve t))
      (fun _ => S (curve t)) (physicalNegativeParameter b (curve t) (amp t)).1
      (fun i => q i-Real.pi)=
      negativeShiftedFullIntegrand b (fun _ => -T (curve t)/S (curve t))
        (fun _ => S (curve t)) n (physicalNegativeParameter b (curve t) (amp t)).1 v := by
    unfold negativeShiftedFullIntegrand negativeShiftedAngles
    exact (edgeFullIntegrand_wrapAngle _ _ _ _ _).symm
  rw [hw] at hd
  change _ = _ at hd
  unfold paperShiftedDensity
  rw [hd]
  have hs := negativeShiftedFullIntegrand_div_scale b
    (fun _ => -T (curve t)/S (curve t)) (fun _ => S (curve t)) (fun _ => amp t)
    n (physicalNegativeParameter b (curve t) (amp t)).1 v
  have hi : independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
      (negativeShiftedAngles n v)=
      negativeShiftedFullIntegrand b (fun _ => -T (curve t)/S (curve t))
        (fun _ => S (curve t)/amp t) n (physicalNegativeParameter b (curve t) (amp t)).1 v := rfl
  rw [hi,hs]
  ring

/-- Exact full coefficient boundary jets as probability angular integrals of the
independent complete integrand. The derivative exchange is proved from the
actual negative-edge density, rather than assumed. -/
theorem physical_negative_boundary_jet_integral (n j : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ}
    (hc : AnalyticAt ℂ curve 0) (ha : AnalyticAt ℂ amp 0) (hS : S (curve 0)≠0)
    (he : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) :
    iteratedDeriv j (fun t => amp t^(n+1)*continuedAngularCoefficient n (curve t)) 0=
      ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
        ∫v : Fin n→ℝ, iteratedDeriv j
          (fun t => independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
            (negativeShiftedAngles n v)) 0 ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  have hj := (paper_weighted_boundary_taylor_integral n hn hc ha hS he hb hB j).2
  have hd (v : Fin n→ℝ) :
      iteratedDeriv j (fun t => paperShiftedDensity n curve amp t v) 0=
        (((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n)*(-1:ℂ)^((n+1).choose 2)*
          iteratedDeriv j
          (fun t => independentFullIntegrand b (physicalNegativeParameter b (curve t) (amp t))
            (negativeShiftedAngles n v)) 0 := by
    rw [(paperShiftedDensity_independent_germ n hn hc hS he hb hB v).iteratedDeriv_eq j,
      iteratedDeriv_const_mul_field]
  simp_rw [hd] at hj
  rw [integral_div,integral_const_mul] at hj
  have hfac : (j.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hj' := (div_left_inj' hfac).mp hj
  rw [hj',edgeAngleMeasure_integral_eq]
  ring

end
end IsingBulk.Joint.Negative
