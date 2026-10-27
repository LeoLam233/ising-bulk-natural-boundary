import IsingBulk.Preferred22.CircleConstrained
import IsingBulk.Preferred22.Physical

/-! The exact real constrained angular-box form of the source convolution bound. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

variable {T : ℝ} [Fact (0<T)]

/-- The complete product quotient map preserves the actual interval-box measure. -/
theorem preferredCircle_box_integral {n : ℕ} (a : ℝ)
    (F : (Fin n → AddCircle T) → ℝ) (hF : Continuous F) :
    (∫ θ in Set.pi Set.univ (fun _ : Fin n => Ioc a (a+T)),
      F (fun i => (θ i : AddCircle T)))=∫ θ,F θ := by
  have hm := measurePreserving_pi
    (fun _ : Fin n => volume.restrict (Ioc a (a+T)))
    (fun _ : Fin n => (volume : Measure (AddCircle T)))
    (fun _ => AddCircle.measurePreserving_mk T a)
  rw [volume_pi,Measure.restrict_pi_pi,volume_pi,←hm.map_eq]
  exact (integral_map_of_stronglyMeasurable hm.measurable hF.stronglyMeasurable).symm

omit [Fact (0<T)] in
theorem preferredCircle_coe_sum {n : ℕ} (θ : Fin n → ℝ) :
    ((∑ i,θ i : ℝ) : AddCircle T)=∑ i,(θ i : AddCircle T) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples T)) θ Finset.univ

/-- The actual unnormalized real-box constrained convolution estimate.
The normalization (2π)^(N-1) remains explicit in the physical coefficient. -/
theorem preferred_periodic_constrained_four_thirds_bound {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f T) (hf0 : ∀ x,0≤f x)
    (a : ℝ) (n : ℕ) :
    (∫ θ in Set.pi Set.univ (fun _ : Fin (n+3) => Ioc a (a+T)),
      (∏ i,f (θ i))*f (-∑ i,θ i))≤
      (∫ y in Ioc a (a+T),(f y)^(4/3:ℝ))^3*
        (∫ y in Ioc a (a+T),f y)^n := by
  have hfc : Continuous hp.lift := hf.quotient_liftOn' _
  have hfl (x : AddCircle T) : 0≤hp.lift x := by
    refine Quotient.inductionOn' x ?_
    exact hf0
  have hc := preferredCircle_constrained_four_thirds_bound hfc hfl n 0
  have he :
      (∫ θ in Set.pi Set.univ (fun _ : Fin (n+3) => Ioc a (a+T)),
        (∏ i,f (θ i))*f (-∑ i,θ i))=
      ∫ θ : Fin (n+3) → AddCircle T,(∏ i,hp.lift (θ i))*hp.lift (0-∑ i,θ i) := by
    rw [←preferredCircle_box_integral a _ (by fun_prop)]
    apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
    intro θ _
    simp only [Function.Periodic.lift_coe,zero_sub]
    rw [←preferredCircle_coe_sum,←AddCircle.coe_neg,Function.Periodic.lift_coe]
  rw [he]
  convert hc using 1
  rw [←AddCircle.integral_preimage T a (fun y => (hp.lift y)^(4/3:ℝ)),
    ←AddCircle.integral_preimage T a hp.lift]
  rfl

/-- Manuscript Lemma 5.2 on the literal complete constrained angle vector. -/
theorem preferred_angularBox_four_thirds_bound {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f (2*Real.pi)) (hf0 : ∀ x,0≤f x)
    (n : ℕ) :
    (∫ θ in angularBox (n+3),∏ i : Fin (n+4),f (constrainedAngles θ i))≤
      (∫ y in Ioc (-Real.pi) Real.pi,(f y)^(4/3:ℝ))^3*
        (∫ y in Ioc (-Real.pi) Real.pi,f y)^n := by
  let : Fact (0<2*Real.pi) := ⟨by positivity⟩
  have h := preferred_periodic_constrained_four_thirds_bound hf hp hf0 (-Real.pi) n
  have hend : -Real.pi+2*Real.pi=Real.pi := by ring
  simpa only [angularBox,constrainedAngles,Fin.prod_univ_castSucc,Fin.snoc_castSucc,
    Fin.snoc_last,hend] using h

end
end IsingBulk.Preferred22
