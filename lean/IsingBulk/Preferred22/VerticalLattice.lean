import IsingBulk.Preferred22.EvenSymmetry
import IsingBulk.Preferred22.KernelBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The full two-sided vertical lattice sum on the actual constrained torus.
The summation includes displacement zero and is justified absolutely before
interchanging it with the integral. Horizontal Fourier inversion and the
joint particle/site estimate are separate obligations. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
open scoped BigOperators

def regularAngularDensity {N : ℕ} (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)).det *
    ∏ i,oneBody (angularRoots s θ i)

def constrainedVerticalCoefficient (n : ℕ) (b : ℤ) (s : ℂ) : ℂ :=
  (((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹ *
    ∫ θ in angularBox n, regularAngularDensity s (constrainedAngles θ) *
      (∏ i,angularRoots s (constrainedAngles θ) i)^b.natAbs

theorem twoSided_geometric_norm_summable {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun b : ℤ => q^b.natAbs) := by
  have hs := summable_geometric_of_lt_one hq hq1
  apply Summable.of_nat_of_neg
  · simpa using hs
  · simpa using hs

theorem twoSided_geometric_sum {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' b : ℤ,z^b.natAbs)=(1+z)/(1-z) := by
  have hs := summable_geometric_of_norm_lt_one hz
  have hp : Summable (fun m : ℕ => z^((m:ℤ).natAbs)) := by simpa using hs
  have hm : Summable (fun m : ℕ => z^((-(m:ℤ)).natAbs)) := by simpa using hs
  have he : (∑' b : ℤ,z^b.natAbs)=(∑' m : ℕ,z^m)+(∑' m : ℕ,z^m)-1 := by
    simpa using Summable.tsum_of_nat_of_neg (f := fun b : ℤ => z^b.natAbs) hp hm
  rw [he,tsum_geometric_of_norm_lt_one hz]
  have hden : 1-z ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h,norm_one] at hz
    exact lt_irrefl _ hz
  field_simp
  ring

theorem constrainedAngles_continuous (n : ℕ) : Continuous (@constrainedAngles n) := by
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [constrainedAngles,Fin.snoc_last]
    fun_prop
  · simp only [constrainedAngles,Fin.snoc_castSucc]
    fun_prop

theorem angularRoot_continuous {s : ℂ} (hs : 1 < ‖s‖) :
    Continuous (fun θ : ℝ => physicalRoot (angularW s θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact (physicalRoot_analyticAt (angularW_off_segment hs θ)).continuousAt.comp
    (continuous_const.sub (Complex.continuous_ofReal.comp Real.continuous_cos)).continuousAt

theorem regularAngularDensity_continuous {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 1 < ‖s‖) : Continuous (@regularAngularDensity N s) := by
  let Z : (Fin N → ℝ) → ℂ := fun θ => ∏ i,angularRoots s θ i
  have hZ : Continuous Z := continuous_finsetProd _ (fun i _ =>
    (angularRoot_continuous hs).comp (continuous_apply i))
  have hZi (θ : Fin N → ℝ) : ‖Z θ‖ < 1 := by
    exact angular_product_norm_lt_one hN hs θ
  have hplus (θ : Fin N → ℝ) : 1+Z θ ≠ 0 := by
    intro h
    have he : Z θ = -1 := by linear_combination h
    have hh := hZi θ
    rw [he,norm_neg,norm_one] at hh
    exact lt_irrefl _ hh
  have hminus (θ : Fin N → ℝ) : 1-Z θ ≠ 0 :=
    angular_product_denominator_ne_zero hN hs θ
  have hc : Continuous (fun θ => fullAngularDensity s θ * ((1-Z θ)/(1+Z θ))) :=
    (fullAngularDensity_continuous hN hs).mul
      ((continuous_const.sub hZ).div (continuous_const.add hZ) hplus)
  convert hc using 1
  funext θ
  have hp : 1+(∏ i,angularRoots s θ i) ≠ 0 := hplus θ
  have hm : 1-(∏ i,angularRoots s θ i) ≠ 0 := hminus θ
  unfold regularAngularDensity fullAngularDensity
  dsimp only [Z]
  field_simp [hp,hm]

theorem continuous_integrableOn_angularBox {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) : IntegrableOn f (angularBox n) := by
  have hh : IntegrableOn f (Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi)) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  apply hh.mono_set
  intro θ hθ
  have ht : ∀ i, -Real.pi < θ i ∧ θ i ≤ Real.pi := by simpa [angularBox] using hθ
  exact ⟨fun i => (ht i).1.le,fun i => (ht i).2⟩

/-- The actual full vertical displacement sum equals the exact Preferred
constrained coefficient, with its factorial and N-1 angular normalization. -/
theorem constrainedVerticalCoefficient_summable_eq_coefficient (n : ℕ)
    {s : ℂ} (hs : 1 < ‖s‖) :
    Summable (fun b : ℤ => ‖constrainedVerticalCoefficient n b s‖) ∧
      (∑' b : ℤ,constrainedVerticalCoefficient n b s)=coefficient (n+1) s := by
  let K : ℂ := (((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹
  let A : (Fin n → ℝ) → ℂ := fun θ => regularAngularDensity s (constrainedAngles θ)
  let Z : (Fin n → ℝ) → ℂ := fun θ => ∏ i,angularRoots s (constrainedAngles θ) i
  let F : ℤ → (Fin n → ℝ) → ℂ := fun b θ => A θ*(Z θ)^b.natAbs
  obtain ⟨q,hq,hq1,hbound⟩ := compact_physical_root_bound (isCompact_singleton (x := s))
    (by intro t ht; simpa only [mem_singleton_iff.mp ht] using hs)
  have hZbound (θ : Fin n → ℝ) : ‖Z θ‖ ≤ q :=
    product_norm_le_q (N := n+1) (Nat.succ_pos n) hq.le hq1 _ (fun i => hbound s rfl _)
  have hA : Continuous A := (regularAngularDensity_continuous (N := n+1) (Nat.succ_pos n) hs).comp
    (constrainedAngles_continuous n)
  have hZ : Continuous Z := by
    apply continuous_finsetProd
    intro i _
    exact (angularRoot_continuous hs).comp
      ((continuous_apply i : Continuous (fun x : Fin (n+1) → ℝ => x i)).comp
        (constrainedAngles_continuous n))
  have hAi := continuous_integrableOn_angularBox hA
  have hFi (b : ℤ) : IntegrableOn (F b) (angularBox n) :=
    continuous_integrableOn_angularBox (hA.mul (hZ.pow _))
  have hnorm (b : ℤ) : (∫ θ in angularBox n,‖F b θ‖) ≤
      (∫ θ in angularBox n,‖A θ‖)*q^b.natAbs := by
    rw [← integral_mul_const]
    apply integral_mono (hFi b).norm (hAi.norm.mul_const _)
    intro θ
    simp only [F,norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hZbound θ) _) (norm_nonneg _)
  have hsI : Summable (fun b : ℤ => ∫ θ in angularBox n,‖F b θ‖) :=
    ((twoSided_geometric_norm_summable hq.le hq1).mul_left
      (∫ θ in angularBox n,‖A θ‖)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hnorm
  have hsNorm : Summable (fun b : ℤ => ‖∫ θ in angularBox n,F b θ‖) :=
    hsI.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  constructor
  · simpa only [constrainedVerticalCoefficient,norm_mul] using hsNorm.mul_left ‖K‖
  · change (∑' b : ℤ,K*(∫ θ in angularBox n,F b θ))=_
    rw [tsum_mul_left,integral_tsum_of_summable_integral_norm hFi hsI]
    change K*(∫ θ in angularBox n,∑' b : ℤ,F b θ)=
      K*(∫ θ in angularBox n,fullAngularDensity s (constrainedAngles θ))
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ => by
      simp only [F,tsum_mul_left,twoSided_geometric_sum ((hZbound θ).trans_lt hq1)]
      simp only [A,Z,regularAngularDensity,fullAngularDensity]
      ring)

end
end IsingBulk.Preferred22
