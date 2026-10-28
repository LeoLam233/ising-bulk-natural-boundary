import IsingBulk.HT22.Physical.FiniteAssembly.Derivatives
import IsingBulk.HT22.Physical.LiftIdentity
import IsingBulk.HT22.Geometry.SignedCriticalLocalization
namespace IsingBulk.HT22.Physical.FiniteAssembly
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def localizedRightIntegral (negative : Bool) (n : ℕ) (τ : ℝ) (p m r : ℝ → ℝ)
    (χ : (Fin n → ℝ) → ℝ) (t : ℂ) : ℂ :=
  ∫ θ in angularBox n,(χ θ:ℂ)*(preferredCellWeight .right preferredPopulationCutoff p m r
    (constrainedAngles negative n θ):ℂ)*bareContourDensity negative τ p m t (constrainedAngles negative n θ)

abbrev rightContourWeight (n : ℕ) (τ : ℝ) (p m r : ℝ → ℝ) : (Fin (n+1) → ℝ) → ℂ :=
  Geometry.rightContourWeight τ preferredPopulationCutoff p m r

theorem rightContourWeight_continuous (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    Continuous (rightContourWeight n τ B.p B.m r) := by
  have hmat : Continuous (fun w : Fin (n+1) → ℝ => (preferredContourMatrix τ B.p B.m w).det) := by
    simp_rw [preferredContourMatrix_eq_full]
    exact (fullAngularJacobian_det_contDiff 1 τ B.p B.m B.smooth B.m_smooth).continuous
  exact ((Complex.continuous_ofReal.comp (preferredCellWeight_contDiff .right preferredPopulationCutoff B.p B.m r
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hr).continuous).mul hmat).div_const _

theorem localizedRightIntegral_analyticAt (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (χ : (Fin n → ℝ) → ℝ) (hχ : Continuous χ)
    {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (localizedRightIntegral negative n τ B.p B.m r χ) s := by
  let w : (Fin (n+1) → ℝ) → ℂ := fun θ => (χ (fun i => θ i.castSucc):ℂ)*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m r θ:ℂ)
  have hw : Continuous w := (Complex.continuous_ofReal.comp (hχ.comp (by fun_prop))).mul
    (Complex.continuous_ofReal.comp (preferredCellWeight_contDiff .right preferredPopulationCutoff B.p B.m r
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hr).continuous)
  have hh := signed_weighted_contour_integral_analyticAt negative n d B hτ w hw hS
  convert hh using 1
  funext t
  apply integral_congr_ae
  exact Eventually.of_forall (fun θ => by
    simp only [w,constrainedAngles,Fin.snoc_castSucc])

theorem localizedRightIntegral_one (negative : Bool) (n : ℕ) (τ : ℝ) (p m r : ℝ → ℝ) :
    localizedRightIntegral negative n τ p m r (fun _ => 1)=
      rightPopulationIntegral negative n τ preferredPopulationCutoff p m r := by
  funext t
  simp only [localizedRightIntegral,rightPopulationIntegral,weightedContourIntegral,Complex.ofReal_one,one_mul]

theorem localizedRightIntegral_eq_lifted (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ)
    (r : ℝ → ℝ) (hr : Function.Periodic r (2*Real.pi)) (χ : (Fin n → ℝ) → ℝ) (t : ℂ) :
    localizedRightIntegral negative n τ B.p B.m r χ t=
      Geometry.localizedSignedLiftedIntegral n negative d B τ (fun θ => (χ θ:ℂ))
        (rightContourWeight n τ B.p B.m r) t := by
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  unfold localizedRightIntegral Geometry.localizedSignedLiftedIntegral
  apply integral_congr_ae
  refine Eventually.of_forall (fun θ => ?_)
  change (χ θ:ℂ)*_*bareContourDensity negative τ B.p B.m t (constrainedAngles negative n θ)=_
  rw [←bareContourDensity_lift negative τ B.delta B.p B.m B.periodic hmp]
  rw [←preferredCellWeight_lift .right B.delta preferredPopulationCutoff B.p B.m r B.periodic hmp hr]
  simp only [rightContourWeight,Geometry.rightContourWeight,bareContourDensity,Nat.add_sub_cancel,constrainedAngles,constrainedAtTotal]
  ring
end
end IsingBulk.HT22.Physical.FiniteAssembly
