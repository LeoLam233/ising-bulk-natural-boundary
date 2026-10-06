import IsingBulk.Tail.CoareaRectangleKernel
import IsingBulk.Tail.CompactActualPairJacobian
import Mathlib.MeasureTheory.Integral.Pi

/-! Full-dimensional injective coarea for two actual phase rows and fixed
spectators. Spectator volume is charged explicitly. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
 theorem injective_coordinate_weighted_coarea_le {N : ℕ} {S R : Set (Fin N → ℝ)}
    (hS : MeasurableSet S) (f : (Fin N → ℝ) → (Fin N → ℝ))
    (f' : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
    (hf' : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x) (hf : InjOn f S)
    (himage : f '' S ⊆ R) (a k : (Fin N → ℝ) → ℝ)
    (ha : ContinuousOn a S) (hk : Continuous k) (hk0 : ∀ x, 0≤k x)
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
  have hw : ContinuousOn (fun x => a x*k (f x)) S := ha.mul (hk.comp_continuousOn hfc)
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


theorem prod_two_distinguished {N : ℕ} {i j : Fin N} (hij : i≠j) (A B C : ℝ) :
    (∏ l : Fin N, if l=i then A else if l=j then B else C)=A*B*C^(N-2) := by
  classical
  let w : Fin N → ℝ := fun l => if l=i then A else if l=j then B else C
  have hji : j∈Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij,Finset.mem_univ j⟩
  have he : ∏ l∈(Finset.univ.erase i).erase j, w l=C^((Finset.univ.erase i).erase j).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro l hl
    have hl' := Finset.mem_erase.mp hl
    have hl'' := Finset.mem_erase.mp hl'.2
    simp [w,hl'.1,hl''.1]
  change (∏ l, w l)=_
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) w hji,he]
  simp [w,Ne.symm hij,Finset.card_erase_of_mem hji,mul_assoc,show N-1-1=N-2 by omega]

def phaseSpectatorBox {N : ℕ} (i j : Fin N) (R : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun l => -(if l=i ∨ l=j then (N:ℝ)*Real.pi else R))
    (fun l => if l=i ∨ l=j then (N:ℝ)*Real.pi else R)

def coordinatePhaseKernel {N : ℕ} (i j : Fin N) (a b : ℝ) (x : Fin N → ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-a)) (x i))⁻¹*(phaseDenominator (Real.exp (-b)) (x j))⁻¹

theorem coordinatePhaseKernel_nonneg {N : ℕ} (i j : Fin N) (a b : ℝ) (x : Fin N → ℝ) :
    0≤coordinatePhaseKernel i j a b x := by unfold coordinatePhaseKernel phaseDenominator; positivity

theorem coordinatePhaseKernel_continuous {N : ℕ} (i j : Fin N) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) : Continuous (coordinatePhaseKernel i j a b) :=
  ((simple_kernel_continuous ha).comp (continuous_apply i)).mul
    ((simple_kernel_continuous hb).comp (continuous_apply j))

theorem phase_spectator_kernel_integral {N : ℕ} {i j : Fin N} (hij : i≠j)
    {R a b : ℝ} (hR : 0≤R) (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1) :
    IntegrableOn (coordinatePhaseKernel i j a b) (phaseSpectatorBox i j R) ∧
      (∫ x in phaseSpectatorBox i j R, coordinatePhaseKernel i j a b x)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*(2*R)^(N-2) := by
  have hcont := coordinatePhaseKernel_continuous i j ha hb
  refine ⟨hcont.continuousOn.integrableOn_compact isCompact_Icc,?_⟩
  let h : Fin N → ℝ := fun l => if l=i ∨ l=j then (N:ℝ)*Real.pi else R
  let w : Fin N → ℝ → ℝ := fun l t => if l=i then (phaseDenominator (Real.exp (-a)) t)⁻¹
    else if l=j then (phaseDenominator (Real.exp (-b)) t)⁻¹ else 1
  have hw (x : Fin N → ℝ) : coordinatePhaseKernel i j a b x=∏ l, w l (x l) := by
    have he := prod_two_distinguished hij
      ((phaseDenominator (Real.exp (-a)) (x i))⁻¹)
      ((phaseDenominator (Real.exp (-b)) (x j))⁻¹) 1
    simp only [one_pow,mul_one] at he
    unfold coordinatePhaseKernel
    rw [← he]
    apply Finset.prod_congr rfl
    intro l _
    by_cases hli : l=i
    · subst l; simp [w]
    · by_cases hlj : l=j
      · subst l; simp [w,Ne.symm hij]
      · simp [w,hli,hlj]
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
    _ ≤ ∏ l : Fin N, if l=i then A else if l=j then B else 2*R := by
      apply Finset.prod_le_prod₀
      · intro l _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | norm_num
      · intro l _
        by_cases hli : l=i
        · subst l; simpa [w,h,neg_mul] using haI
        · by_cases hlj : l=j
          · subst l; simpa [w,h,Ne.symm hij,neg_mul] using hbI
          · simp only [w,h,hli,hlj,ite_false,or_self]
            rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -R≤R)]
            simp
            linarith
    _ = _ := prod_two_distinguished hij A B (2*R)

end
end IsingBulk.Tail
