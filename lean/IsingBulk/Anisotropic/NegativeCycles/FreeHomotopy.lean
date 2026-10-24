import IsingBulk.Anisotropic.NegativeCycles.ActualHomotopyPole
import IsingBulk.Anisotropic.NegativeCycles.ConstrainedAnnularTransport
import IsingBulk.Anisotropic.NegativeNormalForm.ConstrainedJacobian

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set
open scoped BigOperators

@[simp] theorem freeChartCLM_eq_shapeExtend (n : ℕ) (q : Config n) :
    freeChartCLM n q=shapeExtend q := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def complexify (n : ℕ) : (Fin n→ℝ)→L[ℝ] Config n :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem complexify_apply (n : ℕ) (q : Fin n→ℝ) (i : Fin n) : complexify n q i=(q i:ℂ) := rfl

theorem shapeExtend_complexify (n : ℕ) (q : Fin n→ℝ) :
    shapeExtend (complexify n q)=(fun i => ((shapeExtend q i : ℝ):ℂ)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

theorem norm_shapeExtend_complexify_le {n : ℕ} (q : Fin n→ℝ) {r : ℝ}
    (hr : 0≤r) (hq : constrainedSquaredRadius q≤r^2) : ‖shapeExtend (complexify n q)‖≤r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  have hi := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin (n+1)))) => sq_nonneg (shapeExtend q j)) (Finset.mem_univ i)
  change (shapeExtend q i)^2≤constrainedSquaredRadius q at hi
  rw [shapeExtend_complexify]
  simp only [Complex.norm_real,Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> nlinarith

def freeStraightHomotopy {n : ℕ} (Psi : Config n→Config n) (x : ParameterSpace n) : Config n :=
  let q := complexify n (fun i => x i.succ)
  q+(x 0:ℂ) • (Psi q-q)

theorem freeStraightHomotopy_contDiffAt {n : ℕ} (Psi : Config n→Config n)
    (x : ParameterSpace n) (hPsi : AnalyticAt ℂ Psi (complexify n (fun i => x i.succ))) :
    ContDiffAt ℝ 2 (freeStraightHomotopy Psi) x := by
  have hq : ContDiff ℝ 2 (fun y : ParameterSpace n => complexify n (fun i => y i.succ)) :=
    (complexify n).contDiff.comp (by fun_prop)
  have ht : ContDiff ℝ 2 (fun y : ParameterSpace n => (y 0:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop)
  exact hq.contDiffAt.add (ht.contDiffAt.smul
    (((hPsi.contDiffAt : ContDiffAt ℂ 2 Psi _).restrict_scalars ℝ).comp x hq.contDiffAt |>.sub hq.contDiffAt))

/-- The free-coordinate chain is the restriction of the genuine zero-mean chain. -/
theorem freeStraightHomotopy_constrained {n : ℕ} (Phi : Config (n+1)→Config (n+1))
    (x : ParameterSpace n) (hm : ZeroMean (Phi (shapeExtend (complexify n (fun i => x i.succ))))) :
    shapeExtend (freeStraightHomotopy (constrainedMap Phi) x)=
      shapeExtend (complexify n (fun i => x i.succ))+
        (x 0:ℂ) • (Phi (shapeExtend (complexify n (fun i => x i.succ)))-
          shapeExtend (complexify n (fun i => x i.succ))) := by
  let y := shapeExtend (complexify n (fun i => x i.succ))
  have hmy : ZeroMean y := sum_shapeExtend _
  have hz : ZeroMean (y+(x 0:ℂ) • (Phi y-y)) := by
    simp only [ZeroMean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    rw [hmy,hm]
    ring
  rw [←shapeExtend_restrict (y+(x 0:ℂ) • (Phi y-y)) hz]
  congr 1
  funext i
  simp [freeStraightHomotopy,constrainedMap,y]

theorem correctedHomotopy_zeroMean {n : ℕ} {B : ℂ→ℂ} {phi : ℝ} {hphi : Real.sin phi≠0}
    {d : ℂ} {r C R : ℝ} (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (hRr : R≤r/2)
    (s : ℝ) (y : Config n) (hy : ‖y‖≤R/2) (hm : ZeroMean y) :
    ZeroMean (P.V (J.W y)) ∧ ZeroMean (correctedHomotopy P J s y) := by
  have hw := J.w_inverse y hy
  have hwm := hw.2.2.2 hm
  have hvm := (P.v_inverse (J.W y) (hw.1.trans hRr)).2.2.2 hwm
  refine ⟨hvm.1,?_⟩
  simp only [correctedHomotopy,ZeroMean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Pi.sub_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [hm,hvm.1]
  ring

theorem correctedHomotopy_norm_le {n : ℕ} {B : ℂ→ℂ} {phi : ℝ} {hphi : Real.sin phi≠0}
    {d : ℂ} {r C R : ℝ} (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2)
    (s : ℝ) (hs : s∈Icc (-1/2:ℝ) (3/2)) (y : Config n) (hy : ‖y‖≤R/2) :
    ‖correctedHomotopy P J s y‖≤2*‖y‖ := by
  have hsup := ((J.corrected_bounds B phi hphi d r C R P hr hR hRr).2 y hy).2
  have hsn : ‖(s:ℂ)‖≤3/2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hs.1,hs.2]
  have hadd := norm_add_le y ((s:ℂ) • (P.V (J.W y)-y))
  rw [norm_smul] at hadd
  have hmul := mul_le_mul hsn hsup (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  change ‖correctedHomotopy P J s y‖≤_ at hadd
  nlinarith [norm_nonneg y]

end IsingBulk.Anisotropic.NegativeCycles
