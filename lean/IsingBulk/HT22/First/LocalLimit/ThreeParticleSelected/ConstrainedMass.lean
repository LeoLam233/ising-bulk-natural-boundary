import IsingBulk.HT22.First.LocalLimit.ThreeParticleSelected.Young
import IsingBulk.HT22.First.LocalLimit.ThreeParticleSelected.ProfileMass
import IsingBulk.HT22.Physical.Angular

namespace IsingBulk.HT22.LocalLimit.ThreeParticleSelected
noncomputable section
open Set MeasureTheory Filter IsingBulk.Preferred22
open scoped BigOperators Topology ENNReal

theorem affine_periodic_three_halves_bound {T : ℝ} [Fact (0<T)] {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f T) (hf0 : ∀ x,0≤f x)
    (a q : ℝ) :
    (∫ θ in Set.pi Set.univ (fun _ : Fin 2 => Ioc a (a+T)),
      (∏ i,f (θ i))*f (q-∑ i,θ i))≤
      (∫ y in Ioc a (a+T),(f y)^(3/2:ℝ))^2 := by
  have hfc : Continuous hp.lift := hf.quotient_liftOn' _
  have hfl (x : AddCircle T) : 0≤hp.lift x := by
    refine Quotient.inductionOn' x ?_
    exact hf0
  have hc := triple_convolution_bound hfc hfl (q:AddCircle T)
  change preferredCircleConvolutionPower hp.lift 2 (q:AddCircle T)≤_ at hc
  rw [preferredCircleConvolutionPower_eq_constrained hfc] at hc
  have he :
      (∫ θ in Set.pi Set.univ (fun _ : Fin 2 => Ioc a (a+T)),
        (∏ i,f (θ i))*f (q-∑ i,θ i))=
      ∫ θ : Fin 2 → AddCircle T,(∏ i,hp.lift (θ i))*hp.lift ((q:AddCircle T)-∑ i,θ i) := by
    rw [←preferredCircle_box_integral a _ (by fun_prop)]
    apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
    intro θ _
    simp only [Function.Periodic.lift_coe]
    rw [←preferredCircle_coe_sum,←AddCircle.coe_sub,Function.Periodic.lift_coe]
  rw [he]
  convert hc using 1
  rw [←AddCircle.integral_preimage T a (fun y => (hp.lift y)^(3/2:ℝ))]
  rfl

theorem signed_three_profile_constrained_mass (d : PreferredBranchData) :
    ∃ C : ℝ, 0<C ∧ ∀ negative : Bool, ∀ ε : ℝ, 0<ε →
      (∫ θ in angularBox 2, ∏ i : Fin 3,
        preferredSelectedOneBodyProfile d ε (Physical.constrainedAngles negative 2 θ i))≤C := by
  obtain ⟨A,hA,hbound⟩ := selected_profile_three_halves_uniform_mass d
  refine ⟨A^2,sq_pos_of_pos hA,?_⟩
  intro negative ε hε
  let : Fact (0<2*Real.pi) := ⟨by positivity⟩
  have hf := preferred_selected_oneBody_profile_continuous d hε
  have hnonneg (θ : ℝ) : 0≤preferredSelectedOneBodyProfile d ε θ :=
    (preferred_selected_oneBody_profile_pos d hε θ).le
  have h := affine_periodic_three_halves_bound hf
    (preferred_selected_oneBody_profile_periodic d ε) hnonneg (-Real.pi)
    (Physical.constraintAngle negative)
  have hmass : 0≤∫ θ in Ioc (-Real.pi) Real.pi,
      (preferredSelectedOneBodyProfile d ε θ)^(3/2:ℝ) :=
    integral_nonneg (fun θ => Real.rpow_nonneg (hnonneg θ) _)
  have hpow := pow_le_pow_left₀ hmass (hbound ε hε).1 2
  rw [show -Real.pi+2*Real.pi=Real.pi by ring] at h
  have hfinal := h.trans hpow
  simpa only [angularBox,Physical.constrainedAngles,Fin.prod_univ_castSucc,Fin.snoc_castSucc,
    Fin.snoc_last] using hfinal

end
end IsingBulk.HT22.LocalLimit.ThreeParticleSelected
