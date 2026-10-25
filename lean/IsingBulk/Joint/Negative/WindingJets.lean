import IsingBulk.Joint.Negative.WindingIntegral

noncomputable section
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.HT.Contour IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory Filter Metric
open scoped BigOperators Topology

/-- Literal physically weighted, normalized shifted angular density. -/
def weightedShiftedPhysicalDensity (n : ℕ) (curve : ℂ→Coupling) (a : ℂ→ℂ)
    (v : Fin n→ℝ) (t : ℂ) : ℂ :=
  a t^(n+1)/(((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)*
    continuedAngularDensity (curve t)
      (fun i => (physicalDependentAngles n (fun j => v j+Real.pi) i:ℂ))

/-- The actual winding change of variables applies to every normalized Taylor jet.
Only exact local physical chart identities are inputs, not contour estimates. -/
theorem actual_inner_winding_jet_integral (B : ℂ→ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0) (hBa : AnalyticAt ℂ B 0) :
    ∃r : ℝ,0<r ∧ ∀m j : ℕ, ∀k : Fin (2*m+2), ∀d σ : ℝ,
      (2*m+1:ℕ)*d=(2*(k.val:ℝ)-(2*m+1:ℕ))*Real.pi → σ≤Real.pi^2 → σ≤r^2 →
      ∀curve : ℂ→Coupling, ∀a rootB : ℂ→ℂ,
      (∀ᶠt in 𝓝 (0:ℂ), S (curve t)≠0 ∧
        B t=T (curve t)/S (curve t) ∧
        transferC (curve t)+transferB (curve t)=(Real.cos phi:ℂ)+B t*t ∧
        a t^2=p (curve t) ∧ a t/S (curve t)=rootB t) →
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      (∫v in {v : Fin (2*m)→ℝ | v∈Icc (fun _ => -Real.pi) (fun _ => Real.pi) ∧
        v∈windingSector (2*m) k ∧ (∑i,(negativeShiftedAngles (2*m) v i)^2)<σ},
        iteratedDeriv j (weightedShiftedPhysicalDensity (2*m) curve a v) 0/(j.factorial:ℂ))=
      ∫w in {w : Fin (2*m)→ℝ | constrainedSquaredRadius w<σ-(2*m+1:ℕ)*d^2},
        iteratedDeriv j (fun t => formFactorNumerator B rootB phi hphi (d:ℂ) t
          (fun i => ((shapeExtend w i:ℝ):ℂ))*
          cothHalf (fun u => poleEquation B phi hphi (d:ℂ) u
            (fun i => ((shapeExtend w i:ℝ):ℂ))) t) 0/(j.factorial:ℂ) := by
  obtain ⟨r,hr,hden⟩ := local_scaled_physical_density B hp hpi hphi hBa
  refine ⟨r,hr,?_⟩
  intro m j k d σ hd hσpi hσr curve a rootB hchart hres
  rw [actual_inner_winding_eq_ellipsoid (2*m) k σ hσpi,
    integral_winding_mean_translation (2*m) k d σ hd]
  apply setIntegral_congr_fun (measurableSet_lt
    (constrainedSquaredRadius_contDiff (n := 2*m) 0).continuous.measurable measurable_const)
  intro w hw
  have hk : (2*m+1:ℕ)*(Real.pi+d)=(k.val:ℝ)*(2*Real.pi) := by nlinarith [hd]
  have hangle : (fun j => d+w j+Real.pi)=(fun j => w j+Real.pi+d) := by funext j; ring
  have henergy : (∑i,(d+shapeExtend w i)^2)<r^2 := by
    have hshift := windingAffine_energy_shift (2*m) k d hd w
    rw [windingAffine_mean_shift (2*m) k d hd] at hshift
    change constrainedSquaredRadius w<σ-(2*m+1:ℕ)*d^2 at hw
    linarith
  have hsmall (i : Fin (2*m+1)) : ‖(d:ℂ)+(shapeExtend w i:ℝ)‖<r := by
    have hi := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (2*m+1)))) => sq_nonneg (d+shapeExtend w j)) (Finset.mem_univ i)
    rw [←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> nlinarith
  have hevent : weightedShiftedPhysicalDensity (2*m) curve a (fun i => d+w i) =ᶠ[𝓝 (0:ℂ)]
      (fun t => formFactorNumerator B rootB phi hphi (d:ℂ) t (fun i => ((shapeExtend w i:ℝ):ℂ))*
        cothHalf (fun u => poleEquation B phi hphi (d:ℂ) u (fun i => ((shapeExtend w i:ℝ):ℂ))) t) := by
    filter_upwards [hchart,ball_mem_nhds (0:ℂ) hr] with t ht htr
    rw [weightedShiftedPhysicalDensity,hangle,
      continuedAngularDensity_winding (2*m) (curve t) d (k.val:ℤ) (by exact_mod_cast hk)]
    simpa only [Complex.ofReal_add] using hden m (d:ℂ) t
      (fun i => ((shapeExtend w i:ℝ):ℂ)) (curve t) (a t) rootB
      (by simpa using htr) hsmall ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 hres
  dsimp only
  rw [hevent.iteratedDeriv_eq j]

end IsingBulk.Joint.Negative
