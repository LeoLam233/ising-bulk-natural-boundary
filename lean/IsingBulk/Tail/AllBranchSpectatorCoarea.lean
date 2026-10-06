import IsingBulk.Tail.CompactPairCoarea

namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
 theorem injective_coordinate_weighted_coarea_on {N : ℕ} {S R : Set (Fin N → ℝ)}
    (hS : MeasurableSet S) (f : (Fin N → ℝ) → (Fin N → ℝ))
    (f' : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
    (hf' : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x) (hf : InjOn f S)
    (himage : f '' S ⊆ R) (a k : (Fin N → ℝ) → ℝ)
    (ha : ContinuousOn a S) (hk : ContinuousOn k R) (hk0 : ∀ x, 0≤k x)
    (hki : IntegrableOn k R) {C : ℝ} (hC : 0≤C)
    (ha0 : ∀ x ∈ S, 0≤a x) (hratio : ∀ x ∈ S, a x≤C*|(f' x).det|) :
    IntegrableOn (fun x => a x*k (f x)) S ∧
      (∫ x in S, a x*k (f x))≤C*(∫ y in R, k y) := by
  let : (volume : Measure (Fin N → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]
    infer_instance
  have hkimage : IntegrableOn k (f '' S) := hki.mono_set himage
  have hdet := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (Fin N → ℝ)) hS hf' hf k).mp hkimage
  have hdom : IntegrableOn (fun x => C*(|(f' x).det| *k (f x))) S := by
    simpa only [smul_eq_mul,IntegrableOn] using hdet.const_mul C
  have hfc : ContinuousOn f S := fun x hx => (hf' x hx).continuousWithinAt
  have hw : ContinuousOn (fun x => a x*k (f x)) S := ha.mul (hk.comp hfc (fun x hx => himage ⟨x,hx,rfl⟩))
  have hpoint : ∀ x ∈ S, ‖a x*k (f x)‖≤C*(|(f' x).det| *k (f x)) := by
    intro x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ha0 x hx) (hk0 _))]
    have hh := mul_le_mul_of_nonneg_right (hratio x hx) (hk0 (f x))
    simpa only [mul_assoc] using hh
  have hi : IntegrableOn (fun x => a x*k (f x)) S :=
    hdom.mono' (hw.aestronglyMeasurable hS) ((ae_restrict_iff' hS).mpr (Eventually.of_forall hpoint))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in S, C*(|(f' x).det| *k (f x)) :=
      setIntegral_mono_on hi hdom hS (fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hpoint x hx))
    _ = C*(∫ x in S, |(f' x).det| *k (f x)) := integral_const_mul _ _
    _ = C*(∫ y in f '' S, k y) := by
      rw [integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (Fin N → ℝ)) hS hf' hf k]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hki (Eventually.of_forall hk0) (Eventually.of_forall himage)) hC


def weightedPhaseSpectatorKernel {N : ℕ} (p q : Fin N) (a b : ℝ) (L : ℝ → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∏ i, if i=p then (phaseDenominator (Real.exp (-a)) (x i))⁻¹
    else if i=q then (phaseDenominator (Real.exp (-b)) (x i))⁻¹ else L (x i)

theorem weightedPhaseSpectatorKernel_nonneg {N : ℕ} (p q : Fin N) (a b : ℝ) (L : ℝ → ℝ)
    (hL : ∀ t, 0 ≤ L t) (x : Fin N → ℝ) : 0 ≤ weightedPhaseSpectatorKernel p q a b L x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact hL _

theorem weightedPhaseSpectatorKernel_continuousOn {N : ℕ} (p q : Fin N) {a b R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (L : ℝ → ℝ) (hL : ContinuousOn L (Icc (-R) R)) :
    ContinuousOn (weightedPhaseSpectatorKernel p q a b L) (phaseSpectatorBox p q R) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hip : i=p
  · simp only [hip,ite_true]
    exact ((simple_kernel_continuous ha).comp (continuous_apply p)).continuousOn
  · by_cases hiq : i=q
    · subst i
      simp only [hip,ite_false,ite_true]
      exact ((simple_kernel_continuous hb).comp (show Continuous (fun x : Fin N → ℝ => x q) from continuous_apply q)).continuousOn
    · simp only [hip,hiq,ite_false]
      apply hL.comp (continuous_apply i).continuousOn
      intro x hx
      exact ⟨by simpa [phaseSpectatorBox,hip,hiq] using hx.1 i,
        by simpa [phaseSpectatorBox,hip,hiq] using hx.2 i⟩

theorem weighted_phase_spectator_kernel_integral {N : ℕ} {i j : Fin N} (hij : i≠j)
    (L : ℝ → ℝ) (C : ℝ) ( _hC : 0 ≤ C) (hL0 : ∀ t, 0 ≤ L t)
    {R a b : ℝ} ( _hR : 0≤R) (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1)
    (hLc : ContinuousOn L (Icc (-R) R)) (hLint : (∫ t in Icc (-R) R, L t) ≤ C) :
    IntegrableOn (weightedPhaseSpectatorKernel i j a b L) (phaseSpectatorBox i j R) ∧
      (∫ x in phaseSpectatorBox i j R, weightedPhaseSpectatorKernel i j a b L x)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2) := by
  have hcont := weightedPhaseSpectatorKernel_continuousOn i j ha hb L hLc
  refine ⟨hcont.integrableOn_compact isCompact_Icc,?_⟩
  let h : Fin N → ℝ := fun l => if l=i ∨ l=j then (N:ℝ)*Real.pi else R
  let w : Fin N → ℝ → ℝ := fun l t => if l=i then (phaseDenominator (Real.exp (-a)) t)⁻¹
    else if l=j then (phaseDenominator (Real.exp (-b)) t)⁻¹ else L t
  have hw (x : Fin N → ℝ) : weightedPhaseSpectatorKernel i j a b L x=∏ l, w l (x l) := rfl
  have hmeasure : volume.restrict (phaseSpectatorBox i j R)=
      Measure.pi (fun l => volume.restrict (Icc (-h l) (h l))) := by
    rw [phaseSpectatorBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  simp_rw [hw]
  rw [hmeasure,integral_fintype_prod_eq_prod]
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  let B := (N:ℝ)*simpleKernelConstant*(1+|Real.log b|)
  have hNpi : 0≤(N:ℝ)*Real.pi := by positivity
  have haI : (∫ t in Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi), (phaseDenominator (Real.exp (-a)) t)⁻¹)≤A := by
    have he := simple_kernel_interval_integral ha ha1 N
      (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith)
      (show (N:ℝ)*Real.pi≤-(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith),← integral_Icc_eq_integral_Ioc] at he
    exact he
  have hbI : (∫ t in Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi), (phaseDenominator (Real.exp (-b)) t)⁻¹)≤B := by
    have he := simple_kernel_interval_integral hb hb1 N
      (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith)
      (show (N:ℝ)*Real.pi≤-(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith),← integral_Icc_eq_integral_Ioc] at he
    exact he
  calc
    _ ≤ ∏ l : Fin N, if l=i then A else if l=j then B else C := by
      apply Finset.prod_le_prod₀
      · intro l _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact hL0 _
      · intro l _
        by_cases hli : l=i
        · subst l; simpa [w,h,neg_mul] using haI
        · by_cases hlj : l=j
          · subst l; simpa [w,h,Ne.symm hij,neg_mul] using hbI
          · simp only [w,h,hli,hlj,ite_false,or_self]
            exact hLint
    _ = _ := prod_two_distinguished hij A B C

theorem weightedPhaseSpectatorKernel_factorization {N : ℕ} (p q : Fin N) (hpq : p ≠ q)
    (a b : ℝ) (L : ℝ → ℝ) (x : Fin N → ℝ) :
    weightedPhaseSpectatorKernel p q a b L x=coordinatePhaseKernel p q a b x*
      ∏ i ∈ (Finset.univ.erase p).erase q, L (x i) := by
  let w : Fin N → ℝ := fun i => if i=p then (phaseDenominator (Real.exp (-a)) (x i))⁻¹
    else if i=q then (phaseDenominator (Real.exp (-b)) (x i))⁻¹ else L (x i)
  have hq : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hpq.symm,Finset.mem_univ q⟩
  change (∏ i, w i)=_
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ p),
    ← Finset.mul_prod_erase (Finset.univ.erase p) w hq]
  have he : ∏ i ∈ (Finset.univ.erase p).erase q, w i=∏ i ∈ (Finset.univ.erase p).erase q, L (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiq := (Finset.mem_erase.mp hi).1
    have hip := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [w,hip,hiq]
  rw [he]
  simp [w,coordinatePhaseKernel,hpq.symm,mul_assoc]

end
end IsingBulk.Tail
