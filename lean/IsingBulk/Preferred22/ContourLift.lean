import IsingBulk.Preferred22.ContourPartition
import IsingBulk.Preferred22.EvenSymmetry
import IsingBulk.Preferred22.ContourBumpJets

/-! Exact periodic one-sided lift and the integrated fixed-anchor telescope.
All equalities retain the original physical density and normalization. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem preferred_periodic_lift {E : Type*} (f : ℝ → E)
    (hf : Function.Periodic f (2*Real.pi)) (δ θ : ℝ) :
    f (toIocMod (by positivity : 0<2*Real.pi) (-Real.pi-δ) θ)=f θ := by
  unfold toIocMod
  exact hf.sub_zsmul_eq _

theorem preferred_occupancy_lift {N : ℕ} (p : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (δ : ℝ) (θ : Fin N → ℝ) :
    occupancy p (preferredLiftedAngles δ θ)=occupancy p θ := by
  simp only [occupancy,preferredLiftedAngles,preferred_periodic_lift p hp]

theorem preferred_shift_lift {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin N → ℝ) (i : Fin N) :
    balancedShift τ p m (preferredLiftedAngles δ θ) i=balancedShift τ p m θ i := by
  simp only [balancedShift,preferred_occupancy_lift p hp,preferred_occupancy_lift m hm,
    preferredLiftedAngles,preferred_periodic_lift p hp,preferred_periodic_lift m hm]

theorem preferred_contourMatrix_lift {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin N → ℝ) :
    preferredContourMatrix τ p m (preferredLiftedAngles δ θ)=preferredContourMatrix τ p m θ := by
  ext i j
  simp only [preferredContourMatrix,shiftJacobian,preferredLiftedAngles,
    preferred_periodic_lift p hp,preferred_periodic_lift m hm,
    preferred_periodic_lift (deriv p) (bump_derivative_periodic hp),
    preferred_periodic_lift (deriv m) (bump_derivative_periodic hm)]

theorem preferred_homotopyRoot_lift {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin N → ℝ) :
    homotopyRoot τ 1 p m (preferredLiftedAngles δ θ)=homotopyRoot τ 1 p m θ := by
  ext i
  simp only [homotopyRoot,Complex.ofReal_one,one_mul,Complex.exp_add,
    preferred_shift_lift τ δ p m hp hm]
  have he (x : ℝ) : Complex.exp (Complex.I*(x:ℂ))=angleRoot x := by
    unfold angleRoot
    rfl
  simp only [he,preferredLiftedAngles,preferred_periodic_lift angleRoot angleRoot_periodic]

theorem preferred_deformedDensity_eq_rootFree {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredDeformedPhysicalDensity τ p m s θ = rootFreeDensity s (homotopyRoot τ 1 p m θ) := by
  have hy : homotopyRoot τ 1 p m θ = fun i => Complex.exp (Complex.I*deformedAngles τ p m θ i) :=
    funext (homotopyRoot_eq_exp_deformedAngles τ p m θ)
  rw [hy,rootFreeDensity_eq_complexAngularDensity]
  simp only [preferredDeformedPhysicalDensity,gaugeKernel_det_normalization]
  rfl

theorem preferred_deformedDensity_lift {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredDeformedPhysicalDensity τ p m s (preferredLiftedAngles δ θ)=
      preferredDeformedPhysicalDensity τ p m s θ := by
  simp only [preferred_deformedDensity_eq_rootFree,
    preferred_homotopyRoot_lift τ δ p m hp hm]

theorem preferredCellWeight_lift {N : ℕ} (cell : PreferredTransportCell N)
    (δ : ℝ) (η p m r : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (hr : Function.Periodic r (2*Real.pi)) (θ : Fin N → ℝ) :
    preferredCellWeight cell η p m r (preferredLiftedAngles δ θ)=preferredCellWeight cell η p m r θ := by
  cases cell <;>
    simp only [preferredCellWeight,preferredLowerWeight,preferred_occupancy_lift p hp,
      preferred_occupancy_lift m hm,preferredRightWeight,preferredAnchorWeight,
      preferredLiftedAngles,preferred_periodic_lift r hr]

theorem preferredPhysicalSeed_lift {N : ℕ} (cell : PreferredTransportCell N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (hr : Function.Periodic r (2*Real.pi)) (s : ℂ) (θ : Fin N → ℝ) :
    preferredPhysicalSeed cell τ η p m r s (preferredLiftedAngles δ θ)=
      preferredPhysicalSeed cell τ η p m r s θ := by
  simp only [preferredPhysicalSeed,preferredCellWeight_lift cell δ η p m r hp hm hr,
    preferred_contourMatrix_lift τ δ p m hp hm,preferred_deformedDensity_lift τ δ p m hp hm]

/-- The modular seam creates no correction in the literal zeroth density. -/
theorem preferredTransportedIntegral_zero_eq_unlifted (n : ℕ)
    (cell : PreferredTransportCell (n+1)) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (hr : Function.Periodic r (2*Real.pi)) (s : ℂ) :
    preferredTransportedIntegral cell δ τ η p m r 0 s =
      ∫ θ in angularBox n, preferredPhysicalSeed cell τ η p m r s (constrainedAngles θ) := by
  simp only [preferredTransportedIntegral,preferredTransportedDensity_zero,
    preferredPhysicalSeed_lift cell τ δ η p m r hp hm hr]

/-- The complete lower-population integral is the actual lifted right term
plus every fixed named anchor, with no omitted domain or seam term. -/
theorem preferred_lower_integral_telescope (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (η r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hr : ContDiff ℝ ∞ r)
    (hrp : Function.Periodic r (2*Real.pi)) :
    preferredLowerPopulationIntegral n τ η B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) =
      preferredTransportedIntegral (n := n) .right B.delta τ η B.p B.m r 0
        (IsingBulk.Branch.radialParameter d.alpha ε) +
      ∑ a : Fin (n+1), preferredTransportedIntegral (.anchor a) B.delta τ η B.p B.m r 0
        (IsingBulk.Branch.radialParameter d.alpha ε) := by
  simp only [preferredTransportedIntegral_zero_eq_unlifted n _ τ B.delta η B.p B.m r
    B.periodic B.m_periodic hrp]
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let R := fun θ : Fin n → ℝ => preferredPhysicalSeed .right τ η B.p B.m r s (constrainedAngles θ)
  let A := fun a : Fin (n+1) => fun θ : Fin n → ℝ =>
    preferredPhysicalSeed (.anchor a) τ η B.p B.m r s (constrainedAngles θ)
  have hiR : IntegrableOn R (angularBox n) :=
    preferredPhysicalSeed_integrableOn_angularBox n d B .right hε hτ η r hη hr
  have hiA (a : Fin (n+1)) : IntegrableOn (A a) (angularBox n) :=
    preferredPhysicalSeed_integrableOn_angularBox n d B (.anchor a) hε hτ η r hη hr
  have hpoint (θ : Fin n → ℝ) : R θ+∑ a,A a θ =
      (preferredLowerWeight η B.p B.m (constrainedAngles θ):ℂ)*
        preferredBareContourDensity τ B.p B.m s (constrainedAngles θ) := by
    dsimp only [R,A]
    rw [preferredPhysicalSeed_sum]
    unfold preferredBareContourDensity
    ring
  unfold preferredLowerPopulationIntegral
  change (∫ θ in angularBox n,(preferredLowerWeight η B.p B.m (constrainedAngles θ):ℂ)*
      preferredBareContourDensity τ B.p B.m s (constrainedAngles θ)) =
    (∫ θ in angularBox n,R θ)+∑ a,∫ θ in angularBox n,A a θ
  calc
    _ = ∫ θ in angularBox n,R θ+∑ a,A a θ :=
      integral_congr_ae (Filter.Eventually.of_forall fun θ => (hpoint θ).symm)
    _ = (∫ θ in angularBox n,R θ)+∫ θ in angularBox n,∑ a,A a θ :=
      integral_add hiR (integrable_finsetSum _ (fun a _ => hiA a))
    _ = _ := congrArg (fun z => (∫ θ in angularBox n,R θ)+z)
      (integral_finsetSum _ (fun a _ => hiA a))

end
end IsingBulk.Preferred22
