import IsingBulk.Joint.Negative.AngularDensity
import IsingBulk.Joint.Negative.CurveCoordinates
import IsingBulk.Anisotropic.NegativeCycles.DensityPhaseBridge
import IsingBulk.Anisotropic.NegativeCycles.LocalPhysicalDensity

/-! Exact independent-coupling angular density to hyperbolic pole-density
bridge. The full factorial, angular measure, anisotropy power and kernel are
preserved for every odd particle number. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators

/-- Literal continued angular weight, with every scalar and factorial retained. -/
theorem scaled_continuedAngularWeight_eq_formFactorNumerator (m : ℕ)
    (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ)
    (v : Config (2*m+1)) {K : Coupling} {a : ℂ}
    (hB : B t=T K/S K) (hAR : a/S K=rootB t)
    (hR : (rootB t)^2=B t)
    (hroot : ∀i, continuedTransferRoot K ((Real.pi:ℂ)+d+v i)=
      Complex.exp (-negativePhase B phi hphi t (d+v i))) :
    a^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
      continuedAngularWeight K (fun i => (Real.pi:ℂ)+d+v i)=
        formFactorNumerator B rootB phi hphi d t v := by
  unfold continuedAngularWeight
  simp_rw [hroot,rootOneBody_exp_neg,angularRootPair_exp_neg]
  have hp : (∏i,∏j∈Finset.univ.filter (fun j => i<j),
      (Complex.sin ((((Real.pi:ℂ)+d+v i)-((Real.pi:ℂ)+d+v j))/2)/
       Complex.sinh ((negativePhase B phi hphi t (d+v i)+negativePhase B phi hphi t (d+v j))/2))^2)=
      ∏p∈firstStrictPairs (2*m+1),
        (Complex.sin ((v p.1-v p.2)/2)/pairDenominator B phi hphi d t (v p.1) (v p.2))^2 := by
    rw [firstStrictPairs_prod_indexed (2*m+1) (fun i j =>
      (Complex.sin ((v i-v j)/2)/pairDenominator B phi hphi d t (v i) (v j))^2)]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    unfold pairDenominator
    congr 3
    ring
  rw [hp,←hB]
  unfold formFactorNumerator densityPrefactor
  have hs := odd_density_scalar m a (S K) (B t) (rootB t) hAR hR
  have hn : 2*m+1-1=2*m := by omega
  rw [hn]
  calc
    _ = (a^(2*m+1)*(B t)^((2*m+1).choose 2)*(S K)⁻¹^(2*m+1))/
        (((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
        (∏i,(Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹)*
        (∏p∈firstStrictPairs (2*m+1),
          (Complex.sin ((v p.1-v p.2)/2)/pairDenominator B phi hphi d t (v p.1) (v p.2))^2) := by ring
    _ = _ := by rw [hs]

/-- At resonance the exact physical density has the proved coth kernel. -/
theorem scaled_continuedAngularDensity_eq_phase (m : ℕ)
    (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ)
    (v : Config (2*m+1)) {K : Coupling} {a : ℂ}
    (hB : B t=T K/S K) (hAR : a/S K=rootB t)
    (hR : (rootB t)^2=B t)
    (hroot : ∀i, continuedTransferRoot K ((Real.pi:ℂ)+d+v i)=
      Complex.exp (-negativePhase B phi hphi t (d+v i)))
    (hres : Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1) :
    a^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
      continuedAngularDensity K (fun i => (Real.pi:ℂ)+d+v i)=
        formFactorNumerator B rootB phi hphi d t v *
          cothHalf (fun u => poleEquation B phi hphi d u v) t := by
  unfold continuedAngularDensity
  rw [←mul_assoc,scaled_continuedAngularWeight_eq_formFactorNumerator m B rootB phi hphi d t v hB hAR hR hroot]
  simp_rw [hroot]
  rw [rootKernel_exp_neg]
  exact congrArg (fun w => formFactorNumerator B rootB phi hphi d t v*w)
    (resonant_kernel_eq B phi hphi d t v hres)

/-- Exact shifted root identity for independent couplings. -/
theorem continuedTransferRoot_eq_negativeDispersion (B : ℂ → ℂ) {phi : ℝ}
    {K : Coupling} {t : ℂ} (hB : B t = transferB K)
    (he : transferC K + transferB K = (Real.cos phi : ℂ) + B t * t) (delta : ℂ) :
    continuedTransferRoot K ((Real.pi : ℂ) + delta) =
      continuedRoot (negativeDispersion B (Real.cos phi) t delta) := by
  unfold continuedTransferRoot
  congr 1
  rw [transferW_eq, Complex.cos_add, Complex.cos_pi, Complex.sin_pi]
  unfold negativeDispersion
  rw [hB] at *
  linear_combination he

/-- The actual root/pole-density bridge, on one local disk chosen before m. -/
theorem local_scaled_physical_density (B : ℂ → ℂ) {phi : ℝ}
    (hp : 0 < phi) (hpi : phi < Real.pi) (hphi : Real.sin phi ≠ 0)
    (hBa : AnalyticAt ℂ B 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ m : ℕ, ∀ d t : ℂ, ∀ v : Config (2*m+1),
      ∀ K : Coupling, ∀ a : ℂ, ∀ rootB : ℂ → ℂ,
      ‖t‖ < r → (∀ i, ‖d+v i‖ < r) → S K ≠ 0 →
      B t = transferB K →
      transferC K + transferB K = (Real.cos phi : ℂ) + B t*t →
      a^2 = p K → a / S K = rootB t →
      Complex.exp (((2*m+1 : ℕ) : ℂ) * ((phi : ℂ) * Complex.I)) = 1 →
      a^(2*m+1) / (((2*m+1).factorial : ℂ) * (2*(Real.pi : ℂ))^(2*m)) *
        continuedAngularDensity K (fun i => (Real.pi : ℂ)+d+v i) =
          formFactorNumerator B rootB phi hphi d t v *
            cothHalf (fun u => poleEquation B phi hphi d u v) t := by
  obtain ⟨r, hr, hroot⟩ := negativePhase_root_uniform B hp hpi hphi hBa
  refine ⟨r, hr, ?_⟩
  intro m d t v K a rootB ht hv hS hB he ha har hres
  have hR : rootB t ^ 2 = B t := by
    rw [← har, div_pow, ha, hB]
    unfold p transferB
    field_simp [hS]
  apply scaled_continuedAngularDensity_eq_phase m B rootB phi hphi d t v hB har hR _ hres
  intro i
  rw [show (Real.pi : ℂ)+d+v i = (Real.pi : ℂ)+(d+v i) by ring,
    continuedTransferRoot_eq_negativeDispersion B hB he]
  exact hroot t (d+v i) ht (hv i)

end
end IsingBulk.Joint.Negative
