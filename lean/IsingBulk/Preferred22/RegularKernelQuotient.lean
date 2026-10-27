import IsingBulk.Preferred22.RegularFrameJets
import IsingBulk.Preferred22.JointDividedDifference
import IsingBulk.Preferred22.VandermondeTransport
import IsingBulk.Preferred22.Pfaffian
import IsingBulk.Preferred22.ComplexKernelBridge

/-! The actual regular-kernel divided difference and full determinant
Vandermonde factor. The quotient extends analytically through every pair
collision on the proved common regular domain. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric Filter Complex
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def preferredKernelQuotient (s q r : ℂ) : ℂ :=
  dslope (fun x => preferredKernelExtension s x r) r q

theorem preferredKernelExtension_factor (s q r : ℂ) :
    preferredKernelExtension s q r=(q-r)*preferredKernelQuotient s q r := by
  simpa only [smul_eq_mul,preferredKernelExtension_diagonal,sub_zero,preferredKernelQuotient] using
    (sub_smul_dslope (fun x => preferredKernelExtension s x r) r q).symm

theorem preferredKernelQuotient_analyticAt (s q r : ℂ)
    (hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) (s,q,r))
    (hr : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelExtension z.1 z.2.1 z.2.2) (s,r,r)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelQuotient z.1 z.2.1 z.2.2) (s,q,r) := by
  let F : (ℂ × ℂ) × ℂ → ℂ := fun z => preferredKernelExtension z.1.1 z.2 z.1.2
  have hπ (x : (ℂ × ℂ) × ℂ) :
      AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2,z.1.2)) x :=
    (analyticAt_fst.comp analyticAt_fst).prod
      (analyticAt_snd.prod (analyticAt_snd.comp analyticAt_fst))
  have hFq : AnalyticAt ℂ F ((s,r),q) := hq.fun_comp_of_eq
    (f := fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2,z.1.2)) (hπ _) rfl
  have hFr : AnalyticAt ℂ F ((s,r),r) := hr.fun_comp_of_eq
    (f := fun z : (ℂ × ℂ) × ℂ => (z.1.1,z.2,z.1.2)) (hπ _) rfl
  have hh := analyticAt_moving_dslope (T := fun z : ℂ × ℂ => z.2) hFq hFr analyticAt_snd
  have hκ : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => ((z.1,z.2.2),z.2.1)) (s,q,r) :=
    (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)).prod
      (analyticAt_fst.comp analyticAt_snd)
  exact hh.fun_comp_of_eq (f := fun z : ℂ × ℂ × ℂ => ((z.1,z.2.2),z.2.1)) hκ rfl

theorem preferred_regular_pair_factor (c : ℝ) (s q r : ℂ)
    (h : PreferredRightRegularPoint c s q r)
    (hφq : (preferredRegularPhase s q).im<0) (hφr : (preferredRegularPhase s r).im<0) :
    preferredRegularPair s q r=(q-r)*preferredKernelQuotient s q r := by
  exact (preferred_regular_pair_germ c s q r h hφq hφr).eq_of_nhds.trans
    (preferredKernelExtension_factor s q r)

/-- Every fixed joint quotient jet is bounded on the same actual compact
domain, with the domain and parameter radius chosen before the order. -/
theorem preferred_kernel_quotient_domain_all_jets (d : PreferredBranchData) (ρ c : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
      ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D → r∈D →
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ × ℂ => preferredKernelQuotient z.1 z.2.1 z.2.2) (s,q,r)‖≤C := by
  let K := closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ (D ×ˢ D)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (hD.prod hD)
  have ha : AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => preferredKernelQuotient z.1 z.2.1 z.2.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖<ρ := by
      have hh : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
        simpa only [mem_closedBall,dist_eq_norm] using hz.1
      linarith
    have hqr := hgood z.1 z.2.1 z.2.2 hs hz.2.1 hz.2.2
    have hrr := hgood z.1 z.2.2 z.2.2 hs hz.2.2 hz.2.2
    apply preferredKernelQuotient_analyticAt
    · exact preferredKernelExtension_analyticAt _ _ _ hqr.2.1 hqr.2.2.1 hqr.1 hqr.2.2.2.2.2.2.2.2.2
    · exact preferredKernelExtension_analyticAt _ _ _ hrr.2.1 hrr.2.2.1 hrr.1 hrr.2.2.2.2.2.2.2.2.2
  intro j
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (fun z hz =>
    ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  refine ⟨max C 0+1,by positivity,?_⟩
  intro s q r hs hq hr
  exact (hC (s,q,r) ⟨by simpa only [mem_closedBall,dist_eq_norm] using hs,hq,hr⟩).trans
    (by have := le_max_left C 0; linarith)

theorem exp_mul_I_dispersion (v : ℂ) :
    exp (I*v)+(exp (I*v))⁻¹=2*cos v := by
  rw [←exp_neg,Complex.two_cos]
  congr 1 <;> congr 1 <;> ring

/-- The actual half-angle determinant has the full squared pair product
for every even size and every partial coincidence. -/
theorem halfAngleKernel_determinant_product (n : ℕ) (S : ℂ)
    (w φ : Fin (2*n) → ℂ) (hcurve : ∀ i, cos (w i)+cos (φ i)=S)
    (hroot : ∀ i, ‖exp (-I*φ i)‖<1) :
    (halfAngleKernel w φ).det=
      ∏ i, ∏ j∈Finset.Ioi i, (halfAngleKernel w φ i j)^2 := by
  let y : Fin (2*n) → ℂ := fun i => exp (I*w i)
  let z : Fin (2*n) → ℂ := fun i => exp (-I*φ i)
  let r := canonicalPhaseGauge w φ
  have hm : dispersionMatrix y z r=halfAngleKernel w φ := by
    ext i j
    simpa only [dispersionMatrix,scaledPair,dispersionB,y,z,r,mul_div_assoc] using
      canonicalPhaseGauge_halfAngle w φ i j
  rw [←hm]
  apply dispersion_determinant_product n S y z r
  · exact fun _ => exp_ne_zero _
  · exact fun _ => exp_ne_zero _
  · intro i
    have hy := exp_mul_I_dispersion (w i)
    have hz := exp_mul_I_dispersion (-(φ i))
    simp only [mul_neg,cos_neg] at hz
    dsimp only [y,z]
    simp only [neg_mul]
    linear_combination hy+hz+2*hcurve i
  · intro i j _ he
    have hn : ‖z i*z j‖<1 := by
      rw [norm_mul]
      calc
        _ ≤ ‖z i‖*1 := mul_le_mul_of_nonneg_left (hroot j).le (norm_nonneg _)
        _ < 1 := by simpa only [mul_one] using hroot i
    have hh : z i*z j=1 := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hn
    exact (lt_irrefl _ hn)
  · exact canonicalPhaseGauge_sq w φ

def preferredVandermondeKernelAmplitude {N : ℕ} (s : ℂ) (q : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j∈Finset.Ioi i, (preferredKernelQuotient s (q i) (q j))^2

theorem preferredRegularKernel_vandermonde (n : ℕ) (c : ℝ) (s : ℂ)
    (q : Fin (2*n) → ℂ)
    (hgood : ∀ i j, PreferredRightRegularPoint c s (q i) (q j))
    (hroot : ∀ i, ‖exp (-I*preferredRegularPhase s (q i))‖<1)
    (hφ : ∀ i, (preferredRegularPhase s (q i)).im<0) :
    (preferredRegularKernel s q).det=
      preferredSquaredVandermonde q*preferredVandermondeKernelAmplitude s q := by
  have hcurve (i : Fin (2*n)) :
      cos (preferredMovingInverse s (q i))+cos (preferredRegularPhase s (q i))=temperatureTrace s :=
    preferredRegular_dispersion s (q i) (hgood i i).2.2.2.2.2.1
  have hh := halfAngleKernel_determinant_product n (temperatureTrace s)
    (fun i => preferredMovingInverse s (q i)) (fun i => preferredRegularPhase s (q i)) hcurve hroot
  change (preferredRegularKernel s q).det=
    ∏ i, ∏ j∈Finset.Ioi i, (preferredRegularKernel s q i j)^2 at hh
  rw [hh]
  have hp (i j : Fin (2*n)) : preferredRegularKernel s q i j=
      (q i-q j)*preferredKernelQuotient s (q i) (q j) :=
    preferred_regular_pair_factor c s (q i) (q j) (hgood i j) (hφ i) (hφ j)
  simp_rw [hp,mul_pow]
  simp only [Finset.prod_mul_distrib,preferredSquaredVandermonde,preferredVandermondeKernelAmplitude]

end
end IsingBulk.Preferred22
