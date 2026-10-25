import IsingBulk.Anisotropic.NegativeCycles.WindingTranslation
import IsingBulk.Joint.Negative.LocalDensity

noncomputable section
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory
open scoped BigOperators

@[simp] theorem continuedTransferRoot_wrapAngle (K : Coupling) (q : ℝ) :
    continuedTransferRoot K (wrapAngle q:ℂ)=continuedTransferRoot K (q:ℂ) := by
  simp only [continuedTransferRoot,transferW,←Complex.ofReal_cos,cos_wrapAngle]

theorem continuedAngularDensity_wrapAngle {N : ℕ} (K : Coupling) (q : Fin N→ℝ) :
    continuedAngularDensity K (fun i => (wrapAngle (q i):ℂ))=
      continuedAngularDensity K (fun i => (q i:ℂ)) := by
  simp only [continuedAngularDensity,continuedAngularWeight,continuedTransferRoot_wrapAngle,angularRootPair_wrapAngle]

theorem continuedAngularDensity_winding (n : ℕ) (K : Coupling) (d : ℝ) (k : ℤ)
    (hk : (n+1:ℕ)*(Real.pi+d)=(k:ℝ)*(2*Real.pi)) (v : Fin n→ℝ) :
    continuedAngularDensity K (fun i => (physicalDependentAngles n (fun j => v j+Real.pi+d) i:ℂ))=
      continuedAngularDensity K (fun i => ((Real.pi+d+shapeExtend v i:ℝ):ℂ)) := by
  rw [←continuedAngularDensity_wrapAngle K,
    ←continuedAngularDensity_wrapAngle K (fun i => Real.pi+d+shapeExtend v i)]
  congr 1
  funext i
  rw [physicalDependentAngles_winding n d k hk]

/-- True physical inner winding sectors are transformed to the actual arcosh density,
with the precise winding mean, all normalization constants, and no cycle-equality premise. -/
theorem actual_inner_winding_density_integral (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0) (hBa : AnalyticAt ℂ B 0) :
    ∃r : ℝ,0<r ∧ ∀m : ℕ, ∀k : Fin (2*m+2), ∀d σ : ℝ,
      (2*m+1:ℕ)*d=(2*(k.val:ℝ)-(2*m+1:ℕ))*Real.pi → σ≤Real.pi^2 → σ≤r^2 →
      ∀t : ℂ, ∀K : Coupling, ∀a : ℂ, ∀rootB : ℂ→ℂ,
      ‖t‖<r → S K≠0 → B t=T K/S K →
      transferC K+transferB K=(Real.cos phi:ℂ)+B t*t → a^2=p K →
      a/S K=rootB t → Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      (∫v in {v : Fin (2*m)→ℝ | v∈Icc (fun _ => -Real.pi) (fun _ => Real.pi) ∧
        v∈windingSector (2*m) k ∧ (∑i,(negativeShiftedAngles (2*m) v i)^2)<σ},
        a^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
          continuedAngularDensity K (fun i => (physicalDependentAngles (2*m) (fun j => v j+Real.pi) i:ℂ)))=
      ∫w in {w : Fin (2*m)→ℝ | constrainedSquaredRadius w<σ-(2*m+1:ℕ)*d^2},
        formFactorNumerator B rootB phi hphi (d:ℂ) t (fun i => ((shapeExtend w i:ℝ):ℂ))*
          cothHalf (fun u => poleEquation B phi hphi (d:ℂ) u (fun i => ((shapeExtend w i:ℝ):ℂ))) t := by
  obtain ⟨r,hr,hden⟩ := local_scaled_physical_density B hp hpi hphi hBa
  refine ⟨r,hr,?_⟩
  intro m k d σ hd hσpi hσr t K a rootB ht hS hB he hA hAR hres
  rw [actual_inner_winding_eq_ellipsoid (2*m) k σ hσpi,
    integral_winding_mean_translation (2*m) k d σ hd]
  apply setIntegral_congr_fun (measurableSet_lt
    (constrainedSquaredRadius_contDiff (n := 2*m) 0).continuous.measurable measurable_const)
  intro w hw
  dsimp only
  have hk : (2*m+1:ℕ)*(Real.pi+d)=(k.val:ℝ)*(2*Real.pi) := by nlinarith [hd]
  have hangle : (fun j => d+w j+Real.pi)=(fun j => w j+Real.pi+d) := by funext j; ring
  rw [hangle,continuedAngularDensity_winding (2*m) K d (k.val:ℤ) (by exact_mod_cast hk)]
  have henergy : (∑i,(d+shapeExtend w i)^2)<r^2 := by
    have hshift := windingAffine_energy_shift (2*m) k d hd w
    rw [windingAffine_mean_shift (2*m) k d hd] at hshift
    change constrainedSquaredRadius w<σ-(2*m+1:ℕ)*d^2 at hw
    linarith
  have hsmall (i : Fin (2*m+1)) : ‖(d:ℂ)+(shapeExtend w i:ℝ)‖<r := by
    have hi := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (2*m+1)))) => sq_nonneg (d+shapeExtend w j)) (Finset.mem_univ i)
    rw [←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> nlinarith
  simpa only [Complex.ofReal_add] using
    hden m (d:ℂ) t (fun i => ((shapeExtend w i:ℝ):ℂ)) K a rootB ht hsmall hS hB he hA hAR hres

end IsingBulk.Joint.Negative
