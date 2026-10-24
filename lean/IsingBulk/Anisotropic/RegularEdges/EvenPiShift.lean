import IsingBulk.Anisotropic.RegularEdges.LeadingCoefficient
import IsingBulk.Anisotropic.NegativeDominance.NegativeNumeratorBridge

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory
open scoped BigOperators

theorem edgeAngularDensity_wrapAngle {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (u : ℂ) (q : Fin N→ℝ) :
    edgeAngularDensity b B S u (fun i => wrapAngle (q i))=edgeAngularDensity b B S u q := by
  simp only [edgeAngularDensity,edgeAngularWeight,edgeRootProduct,edgeParamRoot_wrapAngle,angularRootPair_wrapAngle]

theorem complexAngularWeight_eq_negative_edgeAngularWeight {N : ℕ}
    {lam b : ℝ} {B S : ℂ→ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : Fin N→ℝ) :
    complexAngularWeight lam z (fun i => (q i:ℂ))=
      (-1:ℂ)^(N.choose 2)*edgeAngularWeight b B S u (fun i => q i-Real.pi) := by
  rw [edgeAngularWeight_eq_edgeNumerator,edgeNumerator_eq_indexed]
  unfold complexAngularWeight
  simp_rw [transferRoot_eq_negative_edgeParamRoot hB he hu hBi,angularRootPair_shift_pi]
  rw [hS]
  have hcoef : (spectralT lam z/spectralS z)^(N.choose 2)=(-1:ℂ)^(N.choose 2)*(B u)^(N.choose 2) := by
    rw [←mul_pow,hB]
    congr 1
    ring
  rw [hcoef]
  ring

theorem complexAngularDensity_eq_negative_edgeAngularDensity {N : ℕ}
    {lam b : ℝ} {B S : ℂ→ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : Fin N→ℝ) :
    complexAngularDensity lam z (fun i => (q i:ℂ))=
      (-1:ℂ)^(N.choose 2)*edgeAngularDensity b B S u (fun i => q i-Real.pi) := by
  unfold complexAngularDensity edgeAngularDensity edgeRootProduct
  rw [complexAngularWeight_eq_negative_edgeAngularWeight hB hS he hu hBi]
  simp_rw [transferRoot_eq_negative_edgeParamRoot hB he hu hBi]
  ring

theorem even_dependent_pi_shift_wrap {n : ℕ} (hn : Even (n+1)) (q : Fin n→ℝ) (i : Fin (n+1)) :
    wrapAngle (physicalDependentAngles n (fun j => q j+Real.pi) i-Real.pi)=
      wrapAngle (physicalDependentAngles n q i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [physicalDependentAngles,Fin.snoc_last,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    obtain ⟨m,hm⟩ := hn
    have hm' : (n:ℝ)+1=(m:ℝ)+(m:ℝ) := by exact_mod_cast hm
    rw [show -((∑j,q j)+(n:ℝ)*Real.pi)-Real.pi= -(∑j,q j)-(m:ℝ)*(2*Real.pi) by linear_combination -Real.pi*hm']
    exact (show Function.Periodic wrapAngle (2*Real.pi) from wrapAngle_add_period).sub_nat_mul_eq m
  · simp only [physicalDependentAngles,Fin.snoc_castSucc,add_sub_cancel_right]

theorem complexAngularDensity_negative_even_shift {n : ℕ} (hn : Even (n+1))
    {lam b : ℝ} {B S : ℂ→ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) (q : Fin n→ℝ) :
    complexAngularDensity lam z (fun i => (physicalDependentAngles n (fun j => q j+Real.pi) i:ℂ))=
      (-1:ℂ)^((n+1).choose 2)*edgeAngularDensity b B S u (physicalDependentAngles n q) := by
  rw [complexAngularDensity_eq_negative_edgeAngularDensity hB hS he hu hBi]
  congr 1
  rw [←edgeAngularDensity_wrapAngle b B S u (fun i => physicalDependentAngles n (fun j => q j+Real.pi) i-Real.pi),
    ←edgeAngularDensity_wrapAngle b B S u (physicalDependentAngles n q)]
  congr 1
  funext i
  exact even_dependent_pi_shift_wrap hn q i

/-- The genuine π translation of the full free-angle cube, with no branch or parity assumption. -/
theorem angleBox_integral_eq_centered_pi_shift (n : ℕ) (f : (Fin n→ℝ)→ℂ) :
    (∫q in angleBox n,f q)=∫q in Icc (fun _ => -Real.pi) (fun _ => Real.pi),f (fun i => q i+Real.pi) := by
  let K : Set (Fin n→ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  let c : Fin n→ℝ := fun _ => Real.pi
  have hm (q : Fin n→ℝ) : q+c∈angleBox n ↔ q∈K := by
    constructor <;> intro h <;> constructor <;> intro i
    · have hh := h.1 i
      change 0≤q i+Real.pi at hh
      change -Real.pi≤q i
      linarith
    · have hh := h.2 i
      change q i+Real.pi≤2*Real.pi at hh
      change q i≤Real.pi
      linarith
    · have hh := h.1 i
      change -Real.pi≤q i at hh
      change 0≤q i+Real.pi
      linarith
    · have hh := h.2 i
      change q i≤Real.pi at hh
      change q i+Real.pi≤2*Real.pi
      linarith
  have he : (fun q => (angleBox n).indicator f (q+c))=K.indicator (fun q => f (q+c)) := by
    funext q
    by_cases hq : q∈K
    · simp only [indicator_of_mem hq,indicator_of_mem ((hm q).mpr hq)]
    · simp only [indicator_of_notMem hq,indicator_of_notMem (not_congr (hm q) |>.mpr hq)]
  have ht := integral_add_right_eq_self (μ := volume) ((angleBox n).indicator f) c
  rw [he,integral_indicator (show MeasurableSet K from measurableSet_Icc),
    integral_indicator (show MeasurableSet (angleBox n) from measurableSet_Icc)] at ht
  exact ht.symm

theorem unscaledAngularCoefficient_negative_even_eq {n : ℕ} (hn : Even (n+1))
    {lam b : ℝ} {B S : ℂ→ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (hz : z∉spectralSet lam) (hs : spectralS z≠0) :
    unscaledAngularCoefficient n lam z=(-1:ℂ)^((n+1).choose 2)*edgeCoefficientNormalization n*
      ∫q in Icc (fun _ => -Real.pi) (fun _ => Real.pi),
        edgeAngularDensity b B S u (physicalDependentAngles n q) := by
  unfold unscaledAngularCoefficient
  rw [multiAngleIntegral_eq_box n _ (complexAngularDensity_dependent_continuous n hz hs),
    angleBox_integral_eq_centered_pi_shift]
  simp_rw [complexAngularDensity_negative_even_shift hn hB hS he hu hBi]
  rw [integral_const_mul]
  dsimp [edgeCoefficientNormalization]
  ring

end
end IsingBulk.Anisotropic.RegularEdges
