import IsingBulk.Preferred22.SelectedProfileConvolution
import IsingBulk.HT22.Physical.Angular

/-! The fourfold-convolution majorant at the actual signed affine constraint.
The evaluation point is zero or pi, not silently reset to zero. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open Set MeasureTheory Filter IsingBulk.Preferred22
open scoped BigOperators Topology ENNReal

 theorem affine_periodic_four_thirds_bound {T : ℝ} [Fact (0<T)] {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f T) (hf0 : ∀ x,0≤f x)
    (a q : ℝ) (n : ℕ) :
    (∫ θ in Set.pi Set.univ (fun _ : Fin (n+3) => Ioc a (a+T)),
      (∏ i,f (θ i))*f (q-∑ i,θ i))≤
      (∫ y in Ioc a (a+T),(f y)^(4/3:ℝ))^3*
        (∫ y in Ioc a (a+T),f y)^n := by
  have hfc : Continuous hp.lift := hf.quotient_liftOn' _
  have hfl (x : AddCircle T) : 0≤hp.lift x := by
    refine Quotient.inductionOn' x ?_
    exact hf0
  have hc := preferredCircle_constrained_four_thirds_bound hfc hfl n (q:AddCircle T)
  have he :
      (∫ θ in Set.pi Set.univ (fun _ : Fin (n+3) => Ioc a (a+T)),
        (∏ i,f (θ i))*f (q-∑ i,θ i))=
      ∫ θ : Fin (n+3) → AddCircle T,(∏ i,hp.lift (θ i))*hp.lift ((q:AddCircle T)-∑ i,θ i) := by
    rw [←preferredCircle_box_integral a _ (by fun_prop)]
    apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
    intro θ _
    simp only [Function.Periodic.lift_coe]
    rw [←preferredCircle_coe_sum,←AddCircle.coe_sub,Function.Periodic.lift_coe]
  rw [he]
  convert hc using 1
  rw [←AddCircle.integral_preimage T a (fun y => (hp.lift y)^(4/3:ℝ)),
    ←AddCircle.integral_preimage T a hp.lift]
  rfl

 theorem signed_profile_constrained_mass (d : PreferredBranchData) :
    ∃ C : ℝ, 0<C ∧ ∀ negative : Bool, ∀ n : ℕ, 4≤n+1 → ∀ ε : ℝ, 0<ε →
      (∫ θ in angularBox n, ∏ i : Fin (n+1),
        preferredSelectedOneBodyProfile d ε (Physical.constrainedAngles negative n θ i))≤C^(n+1) := by
  obtain ⟨A,hA,hbound⟩ := preferred_selected_profile_uniform_mass d
  let C := max 1 A
  have hC1 : 1≤C := le_max_left _ _
  have hC : 0<C := lt_of_lt_of_le zero_lt_one hC1
  have hAC : A≤C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro negative n hn ε hε
  obtain ⟨m,rfl⟩ : ∃m : ℕ,n=m+3 := ⟨n-3,by omega⟩
  let : Fact (0<2*Real.pi) := ⟨by positivity⟩
  have hf := preferred_selected_oneBody_profile_continuous d hε
  have hnonneg (θ : ℝ) : 0≤preferredSelectedOneBodyProfile d ε θ :=
    (preferred_selected_oneBody_profile_pos d hε θ).le
  have h := affine_periodic_four_thirds_bound hf
    (preferred_selected_oneBody_profile_periodic d ε) hnonneg (-Real.pi)
    (Physical.constraintAngle negative) m
  have hfour : 0≤∫ θ in Ioc (-Real.pi) Real.pi,
      (preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ) :=
    integral_nonneg (fun θ => Real.rpow_nonneg (hnonneg θ) _)
  have hone : 0≤∫ θ in Ioc (-Real.pi) Real.pi,preferredSelectedOneBodyProfile d ε θ :=
    integral_nonneg hnonneg
  have hpow := mul_le_mul
    (pow_le_pow_left₀ hfour ((hbound ε hε).1.trans hAC) 3)
    (pow_le_pow_left₀ hone ((hbound ε hε).2.trans hAC) m)
    (pow_nonneg hone m) (pow_nonneg hC.le 3)
  have he : C^3*C^m=C^(m+3) := by rw [pow_add]; ring
  have hfinal := h.trans (by
    convert hpow.trans (he.le.trans (pow_le_pow_right₀ hC1 (show m+3≤m+3+1 by omega))) using 1;
      rw [show -Real.pi+2*Real.pi=Real.pi by ring])
  simpa only [angularBox,Physical.constrainedAngles,Fin.prod_univ_castSucc,Fin.snoc_castSucc,
    Fin.snoc_last,show -Real.pi+2*Real.pi=Real.pi by ring] using hfinal

end
end IsingBulk.HT22.Selected
