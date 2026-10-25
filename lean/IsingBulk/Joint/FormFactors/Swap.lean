import IsingBulk.Joint.FormFactors.RadiusIndependence
import IsingBulk.Joint.FormFactors.ContourContinuity
import IsingBulk.Joint.FormFactors.Normalized
import IsingBulk.Joint.Geometry.SpectralComplement
import IsingBulk.Joint.Geometry.Swap

/-! Exact exchange of the independent lattice axes for the literal double
contours and complete normalized sums, without any physical-input premise. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

@[simp] theorem p_swap (K : Coupling) : p K.swap=p K := by simp [p,S,T,mul_comm]

@[simp] theorem dispersion_swap (K : Coupling) (x y : ℂ) :
    dispersion K.swap x y = dispersion K y x := by
  unfold dispersion
  have hA : A K.swap=A K := by simp [A,mul_comm]
  rw [hA]
  exact Anisotropic.FormFactors.dispersion_axis_exchange (T K) (S K) (A K) x y

theorem contourAnnulus_swap {K : Coupling} {r : ℝ} (hr : ContourAnnulus K r) :
    ContourAnnulus K.swap r := by
  refine ⟨hr.1,hr.2.1,?_⟩
  intro x y hx hx1 hy hy1
  rw [dispersion_swap]
  exact hr.2.2 y x hy hy1 hx hx1

theorem fullDensity_swap {N : ℕ} (K : Coupling) (x y : Fin N → ℂ) :
    fullDensity K.swap x y = fullDensity K y x := by
  unfold fullDensity commonDensity
  simp_rw [dispersion_swap]
  simp only [mul_comm,mul_left_comm,mul_assoc]

theorem unscaledFullCoefficientAtRadius_swap (N : ℕ) (hN : 0<N)
    {r : ℝ} {K : Coupling} (hr : ContourAnnulus K r) :
    unscaledFullCoefficientAtRadius N r K.swap=unscaledFullCoefficientAtRadius N r K := by
  rw [unscaledFullCoefficientAtRadius_eq_box N hN (contourAnnulus_swap hr),
    unscaledFullCoefficientAtRadius_eq_box N hN hr]
  congr 1
  have he (q : (Fin N → ℝ) × (Fin N → ℝ)) :
      doubleAngularDensityOf r (fullDensity K.swap) q=
        doubleAngularDensityOf r (fullDensity K) q.swap := by
    unfold doubleAngularDensityOf
    rw [fullDensity_swap]
    dsimp only [Prod.swap]
    ring
  simp_rw [he]
  exact setIntegral_prod_swap (angleBox N) (angleBox N) (doubleAngularDensityOf r (fullDensity K))

theorem swap_mem_spectralSet_iff (K : Coupling) : K.swap∈spectralSet ↔ K∈spectralSet := by
  suffices hh : ∀ K : Coupling, K.swap∈spectralSet → K∈spectralSet from
    ⟨hh K,fun h => by simpa only [Prod.swap_swap] using hh K.swap h⟩
  intro K h
  obtain ⟨a,ha,b,hb,he⟩ := h
  refine ⟨b,hb,a,ha,?_⟩
  simpa only [A,S,T,Prod.fst_swap,Prod.snd_swap,mul_comm,add_comm] using he

theorem unscaledFullCoefficient_swap (N : ℕ) (hN : 0<N) {K : Coupling}
    (hK : K∉spectralSet) : unscaledFullCoefficient N K.swap=unscaledFullCoefficient N K := by
  have hr := contourRadius_valid hK
  have hKs : K.swap∉spectralSet := mt (swap_mem_spectralSet_iff K).mp hK
  rw [unscaledFullCoefficient_eq_fixed_radius N hN hKs (contourAnnulus_swap hr)]
  exact unscaledFullCoefficientAtRadius_swap N hN hr

@[simp] theorem highPrefactor_swap (K : Coupling) : highPrefactor K.swap=highPrefactor K := by
  simp only [highPrefactor,p_swap]
@[simp] theorem lowPrefactor_swap (K : Coupling) : lowPrefactor K.swap=lowPrefactor K := by
  simp only [lowPrefactor,p_swap]

theorem highNormalizedBulk_swap {K : Coupling} (hK : K∈highDomain) :
    highNormalizedBulk K.swap=highNormalizedBulk K := by
  unfold highNormalizedBulk
  rw [highPrefactor_swap,p_swap]
  congr 1
  apply tsum_congr
  intro n
  rw [unscaledFullCoefficient_swap _ (by omega) (highDomain_subset_spectralComplement hK)]

theorem lowNormalizedBulk_swap {K : Coupling} (hK : K∈lowDomain) :
    lowNormalizedBulk K.swap=lowNormalizedBulk K := by
  unfold lowNormalizedBulk
  rw [lowPrefactor_swap,p_swap]
  congr 1
  apply tsum_congr
  intro n
  rw [unscaledFullCoefficient_swap _ (by omega) (lowDomain_subset_spectralComplement hK)]

end
end IsingBulk.Joint.FormFactors
