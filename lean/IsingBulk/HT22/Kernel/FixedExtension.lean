import IsingBulk.HT22.Tail.PairFactorization
import IsingBulk.HT22.Transport.FieldNeighborhood.ShiftedDomain

/-! The ordinary odd matrix entry is a nonzero exponential gauge times
the genuinely removable pair extension, translated to fixed v. -/
namespace IsingBulk.HT22.Kernel
noncomputable section
open IsingBulk.Preferred22 Geometry IsingBulk.HT22.Tail Filter Set Metric
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def ordinaryScalar (t v w : ℂ) : ℂ :=
  Algebra.ordinaryEntry (Complex.exp (Complex.I*regularInverse t v))
    (Complex.exp (Complex.I*regularInverse t w))
    (Complex.exp (-Complex.I*regularPhase t v))
    (Complex.exp (-Complex.I*regularPhase t w))

def inverseGauge (v w : ℂ) : ℂ :=
  Complex.exp (-Complex.I*v/2)*Complex.exp (-Complex.I*w/2)

theorem inverseGauge_ne_zero (v w : ℂ) : inverseGauge v w≠0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem ordinaryScalar_eq_pair (t v w : ℂ) :
    ordinaryScalar t v w=
      (Complex.sin ((regularInverse t v-regularInverse t w)/2)/
        Complex.sinh (Complex.I*(regularPhase t v+regularPhase t w)/2))/inverseGauge v w := by
  let W : Fin 2 → ℂ := ![regularInverse t v,regularInverse t w]
  let P : Fin 2 → ℂ := ![regularPhase t v,regularPhase t w]
  have hh := canonicalPhaseGauge_halfAngle W P 0 1
  have hg0 : canonicalPhaseGauge W P 0=Complex.exp (-Complex.I*v/2) := by
    simp [canonicalPhaseGauge,W,P,regularPhase]
  have hg1 : canonicalPhaseGauge W P 1=Complex.exp (-Complex.I*w/2) := by
    simp [canonicalPhaseGauge,W,P,regularPhase]
  rw [hg0,hg1] at hh
  simp only [halfAngleKernel,W,P,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  apply (eq_div_iff (inverseGauge_ne_zero v w)).mpr
  unfold ordinaryScalar Algebra.ordinaryEntry dispersionB inverseGauge
  rw [←hh]
  ring

def ordinaryExtension (t v w : ℂ) : ℂ :=
  preferredKernelExtension t (v-preferredMovingBranch t) (w-preferredMovingBranch t) /
    inverseGauge v w

theorem ordinaryScalar_eq_moving_pair (t v w : ℂ) :
    ordinaryScalar t v w=preferredRegularPair t (v-preferredMovingBranch t)
      (w-preferredMovingBranch t)/inverseGauge v w := by
  rw [ordinaryScalar_eq_pair]
  simp only [preferredRegularPair,regularInverse_moving_adapter,preferredRegularPhase,regularPhase]
  congr 3; ring

theorem ordinaryScalar_germ (c : ℝ) (t v w : ℂ)
    (h : PreferredRightRegularPoint c t (v-preferredMovingBranch t) (w-preferredMovingBranch t))
    (hv : (regularPhase t v).im<0) (hw : (regularPhase t w).im<0) :
    (fun z : ℂ × ℂ × ℂ => ordinaryScalar z.1 z.2.1 z.2.2)=ᶠ[𝓝 (t,v,w)]
      (fun z => ordinaryExtension z.1 z.2.1 z.2.2) := by
  have hp (v : ℂ) : preferredRegularPhase t (v-preferredMovingBranch t)=regularPhase t v := by
    simp only [preferredRegularPhase,regularInverse_moving_adapter,regularPhase]
    ring
  have he := preferred_regular_pair_germ c t _ _ h (by rwa [hp]) (by rwa [hp])
  have hb : ContinuousAt (fun z : ℂ × ℂ × ℂ => preferredMovingBranch z.1) (t,v,w) :=
    ContinuousAt.comp (f := fun z : ℂ × ℂ × ℂ => z.1)
      (g := preferredMovingBranch) h.1.continuousAt continuousAt_fst
  have hmap : ContinuousAt (fun z : ℂ × ℂ × ℂ =>
      (z.1,z.2.1-preferredMovingBranch z.1,z.2.2-preferredMovingBranch z.1)) (t,v,w) :=
    continuousAt_fst.prodMk (((continuousAt_fst.comp continuousAt_snd).sub hb).prodMk
      ((continuousAt_snd.comp continuousAt_snd).sub hb))
  have he' := he.comp_tendsto hmap
  filter_upwards [he'] with z hz
  dsimp only [Function.comp_def] at hz
  rw [ordinaryScalar_eq_moving_pair,hz]
  rfl

theorem ordinaryExtension_analyticAt (c : ℝ) (t v w : ℂ)
    (h : PreferredRightRegularPoint c t (v-preferredMovingBranch t) (w-preferredMovingBranch t)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2) (t,v,w) := by
  have hB : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredMovingBranch z.1) (t,v,w) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => z.1)
      (g := preferredMovingBranch) h.1 analyticAt_fst
  have hmap : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      (z.1,z.2.1-preferredMovingBranch z.1,z.2.2-preferredMovingBranch z.1)) (t,v,w) :=
    analyticAt_fst.prod (((analyticAt_fst.comp analyticAt_snd).sub hB).prod
      ((analyticAt_snd.comp analyticAt_snd).sub hB))
  have hK0 := preferredKernelExtension_analyticAt t (v-preferredMovingBranch t)
    (w-preferredMovingBranch t) h.2.1 h.2.2.1 h.1 h.2.2.2.2.2.2.2.2.2
  have hK : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      preferredKernelExtension z.1 (z.2.1-preferredMovingBranch z.1)
        (z.2.2-preferredMovingBranch z.1)) (t,v,w) :=
    hK0.fun_comp_of_eq
      (f := fun z : ℂ × ℂ × ℂ =>
        (z.1,z.2.1-preferredMovingBranch z.1,z.2.2-preferredMovingBranch z.1)) hmap rfl
  have hvi : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => -Complex.I*z.2.1/2) (t,v,w) :=
    (analyticAt_const.mul (analyticAt_fst.comp analyticAt_snd)).div_const
  have hwi : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => -Complex.I*z.2.2/2) (t,v,w) :=
    (analyticAt_const.mul (analyticAt_snd.comp analyticAt_snd)).div_const
  have hG : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => inverseGauge z.2.1 z.2.2) (t,v,w) :=
    hvi.cexp.mul hwi.cexp
  change AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
    preferredKernelExtension z.1 (z.2.1-preferredMovingBranch z.1)
      (z.2.2-preferredMovingBranch z.1) / inverseGauge z.2.1 z.2.2) (t,v,w)
  exact hK.fun_div hG (inverseGauge_ne_zero v w)


end
end IsingBulk.HT22.Kernel
