import IsingBulk.Preferred22.PhysicalSymmetries
import IsingBulk.Preferred22.AngularAnalytic
import IsingBulk.First.PeriodicBoxIntegral

/-! Evenness of the literal constrained coefficients. The proof translates
the entire fundamental box and checks its dependent final angle exactly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators

theorem angleRoot_periodic : Function.Periodic angleRoot (2*Real.pi) := by
  intro θ
  rw [show θ+2*Real.pi = (θ+Real.pi)+Real.pi by ring]
  rw [angleRoot_add_pi,angleRoot_add_pi,neg_neg]

theorem cos_eq_of_angleRoot_eq {u v : ℝ} (h : angleRoot u=angleRoot v) :
    Real.cos u=Real.cos v := by
  have ht := angleRoot_trace u
  rw [h,angleRoot_trace] at ht
  exact_mod_cast (show (Real.cos u:ℂ)=(Real.cos v:ℂ) by linear_combination (-1/2:ℂ)*ht)

theorem fullAngularDensity_congr_angles {N : ℕ} (s : ℂ) (θ φ : Fin N → ℝ)
    (h : ∀ i, angleRoot (θ i)=angleRoot (φ i)) :
    fullAngularDensity s θ=fullAngularDensity s φ := by
  have hy : (fun i => angleRoot (θ i))=(fun i => angleRoot (φ i)) := funext h
  have hz : angularRoots s θ=angularRoots s φ := by
    funext i
    simp only [angularRoots,angularW,cos_eq_of_angleRoot_eq (h i)]
  simp only [fullAngularDensity,hy,hz]

theorem constrainedDensity_periodic {n : ℕ} (s : ℂ) :
    IsingBulk.First.CoordinatePeriodic n (fun θ => fullAngularDensity s (constrainedAngles θ)) := by
  intro θ i
  apply fullAngularDensity_congr_angles
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [constrainedAngles,Fin.snoc_last]
    have hsum : (∑ j, Function.update θ i (θ i+2*Real.pi) j)=∑ j,θ j+2*Real.pi := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) θ]
      ring
    rw [hsum,neg_add]
    exact angleRoot_periodic.sub_eq _
  · simp only [constrainedAngles,Fin.snoc_castSucc]
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self]
      exact angleRoot_periodic _
    · rw [Function.update_of_ne hji]

theorem fullAngularDensity_continuous {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 1 < ‖s‖) : Continuous (@fullAngularDensity N s) := by
  have hc : Continuous (fun θ : Fin N → ℝ =>
      complexAngularDensity (s,fun i => (θ i:ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (complexAngularDensity_analyticAt hN hs θ).continuousAt.comp
      (f := fun u : Fin N → ℝ => (s,fun i => (u i:ℂ)))
      (continuous_const.prodMk (continuous_pi fun i =>
        Complex.continuous_ofReal.comp (continuous_apply i))).continuousAt
  simpa only [complexAngularDensity_real] using hc

theorem angularBox_integral_eq_shifted_box (n : ℕ) (f : (Fin n → ℝ) → ℂ) :
    (∫ x in angularBox n,f x)=
      ∫ x in IsingBulk.First.angleBox n,f (fun i => x i-Real.pi) := by
  let c : Fin n → ℝ := fun _ => Real.pi
  let B : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Icc (-Real.pi) Real.pi)
  have hB : angularBox n =ᵐ[volume] B := Measure.pi_Ioc_ae_eq_pi_Icc
  have hpre : (fun x : Fin n → ℝ => x+c) ⁻¹' IsingBulk.First.angleBox n=B := by
    ext x
    simp only [mem_preimage,IsingBulk.First.angleBox,mem_Icc,Pi.le_def,Pi.add_apply,c,
      B,mem_pi,mem_univ,forall_true_left]
    constructor
    · rintro ⟨h1,h2⟩ i
      exact ⟨by linarith [h1 i],by linarith [h2 i]⟩
    · intro h
      exact ⟨fun i => by linarith [(h i).1],fun i => by linarith [(h i).2]⟩
  have hh := (measurePreserving_add_right (volume : Measure (Fin n → ℝ)) c).setIntegral_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding
    (fun x : Fin n → ℝ => f (fun i => x i-Real.pi)) (IsingBulk.First.angleBox n)
  rw [hpre] at hh
  rw [setIntegral_congr_set hB]
  simpa only [Pi.add_apply,c,add_sub_cancel_right] using hh

/-- Translation invariance of the exact constrained angular fundamental box. -/
theorem angularBox_integral_shift {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hc : Continuous f) (hf : IsingBulk.First.CoordinatePeriodic n f) (c : Fin n → ℝ) :
    (∫ x in angularBox n,f (fun i => x i+c i))=∫ x in angularBox n,f x := by
  rw [angularBox_integral_eq_shifted_box,angularBox_integral_eq_shifted_box]
  let g : (Fin n → ℝ) → ℂ := fun x => f (fun i => x i-Real.pi)
  have hg : Continuous g := hc.comp (continuous_pi (fun i => (continuous_apply i).sub continuous_const))
  have hp : IsingBulk.First.CoordinatePeriodic n g := by
    intro x i
    have he : (fun j => Function.update x i (x i+2*Real.pi) j-Real.pi)=
        Function.update (fun j => x j-Real.pi) i ((x i-Real.pi)+2*Real.pi) := by
      funext j
      by_cases hji : j=i
      · subst j
        simp only [Function.update_self]
        ring
      · simp [Function.update_of_ne hji]
    dsimp only [g]
    rw [he]
    exact hf _ _
  have hh := IsingBulk.First.angleBox_integral_shift n g hg hp c
  convert hh using 1
  congr 1
  funext x
  congr 1
  funext i
  ring

theorem constrainedAngles_add_pi_roots {n : ℕ} (he : Even (n+1)) (θ : Fin n → ℝ) :
    ∀ j, angleRoot (constrainedAngles (fun i => θ i+Real.pi) j)=
      -angleRoot (constrainedAngles θ j) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · obtain ⟨m,hm⟩ := he
    simp only [constrainedAngles,Fin.snoc_last,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hmR : (n:ℝ)+1=2*m := by exact_mod_cast (show n+1=2*m by omega)
    rw [show -(∑ i,θ i+(n:ℝ)*Real.pi)=
      (-∑ i,θ i)+Real.pi-(m:ℝ)*(2*Real.pi) by linear_combination -Real.pi*hmR]
    rw [angleRoot_periodic.sub_nat_mul_eq,angleRoot_add_pi]
  · simp only [constrainedAngles,Fin.snoc_castSucc,angleRoot_add_pi]

theorem fullAngularDensity_neg_of_angles {N : ℕ} (he : Even N) {s : ℂ}
    (hs : 1 < ‖s‖) (θ φ : Fin N → ℝ)
    (hy : ∀ i, angleRoot (φ i) = -angleRoot (θ i)) :
    fullAngularDensity (-s) φ=fullAngularDensity s θ := by
  have hw (i : Fin N) : angularW (-s) (φ i) = -angularW s (θ i) := by
    have ht := angleRoot_trace (φ i)
    rw [hy i,inv_neg,← neg_add,angleRoot_trace] at ht
    have hc : (Real.cos (φ i):ℂ)=-(Real.cos (θ i):ℂ) := by linear_combination (-1/2:ℂ)*ht
    simp only [angularW,temperatureTrace,inv_neg,hc]
    ring
  have hz : angularRoots (-s) φ=fun i => -angularRoots s θ i := by
    funext i
    simp only [angularRoots,hw,physicalRoot_neg (angularW_off_segment hs (θ i))]
  have hk (y z : Fin N → ℂ) : gaugeKernel (fun i => -y i) (fun i => -z i)=-gaugeKernel y z := by
    ext i j
    simp only [gaugeKernel,neg_div_neg_eq,neg_mul_neg,Matrix.neg_apply]
    ring
  have hb (z : ℂ) : oneBody (-z)=-oneBody z := by simp [oneBody]; ring
  simp only [fullAngularDensity,hz,show (fun i => angleRoot (φ i))=(fun i => -angleRoot (θ i)) from funext hy,hk]
  simp only [Matrix.det_neg,Fintype.card_fin,hb,Finset.prod_neg,
    Finset.card_univ,he.neg_one_pow,one_mul]

theorem coefficient_even {N : ℕ} (he : Even N) {s : ℂ} (hs : 1 < ‖s‖) :
    coefficient N (-s)=coefficient N s := by
  cases N with
  | zero => rfl
  | succ n =>
    simp only [coefficient]
    congr 1
    have hsn : 1 < ‖-s‖ := by simpa using hs
    have hc : Continuous (fun θ : Fin n → ℝ => fullAngularDensity (-s) (constrainedAngles θ)) :=
      (fullAngularDensity_continuous (by omega) hsn).comp (by
        apply continuous_pi
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [constrainedAngles,Fin.snoc_last]
          fun_prop
        · simp only [constrainedAngles,Fin.snoc_castSucc]
          fun_prop)
    rw [← angularBox_integral_shift _ hc (constrainedDensity_periodic (-s)) (fun _ => Real.pi)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => fullAngularDensity_neg_of_angles he hs _ _
      (constrainedAngles_add_pi_roots he θ)

theorem evenSeries_even {s : ℂ} (hs : 1 < ‖s‖) : evenSeries (-s)=evenSeries s := by
  unfold evenSeries
  apply tsum_congr
  intro n
  exact coefficient_even (even_two_mul _) hs

end
end IsingBulk.Preferred22
