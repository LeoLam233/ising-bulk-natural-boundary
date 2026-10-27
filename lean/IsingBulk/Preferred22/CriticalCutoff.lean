import IsingBulk.Preferred22.FirstRemainder
import IsingBulk.Preferred22.WeightedRightAnalytic

/-! A concrete smooth original angular multiplier for the critical shape
cutoff. Its first n coordinates are exactly the free shape coordinates;
no change of measure or factorial normalization is hidden in this cutoff. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def preferredCriticalWeight {n : ℕ} (α ρ : ℝ) (θ : Fin (n+1) → ℝ) : ℝ :=
  Real.smoothTransition (2-4*((∑ i : Fin n,(θ i.castSucc+α)^2)+
    (∑ i : Fin n,(θ i.castSucc+α))^2)/ρ^2)

def preferredCriticalMultiplier {n : ℕ} (α ρ : ℝ) (θ : Fin (n+1) → ℝ) : ℂ :=
  (preferredCriticalWeight α ρ θ:ℂ)

theorem preferredCriticalMultiplier_eq_shape {n : ℕ} (α ρ : ℝ) (θ : Fin (n+1) → ℝ) :
    preferredCriticalMultiplier α ρ θ=preferredShapeCutoff ρ
      (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 (fun i => θ i.castSucc+α))) := by
  simp only [preferredCriticalMultiplier,preferredCriticalWeight,preferredShapeCutoff,
    IsingBulk.First.norm_sq_shapeCoordinateEquiv]

theorem preferredCriticalWeight_smooth {n : ℕ} (α ρ : ℝ) :
    ContDiff ℝ ∞ (@preferredCriticalWeight n α ρ) := by
  unfold preferredCriticalWeight
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem preferredCriticalMultiplier_smooth {n : ℕ} (α ρ : ℝ) :
    ContDiff ℝ ∞ (@preferredCriticalMultiplier n α ρ) :=
  Complex.ofRealCLM.contDiff.comp (preferredCriticalWeight_smooth α ρ)

theorem preferredCriticalWeight_mem {n : ℕ} (α ρ : ℝ) (θ : Fin (n+1) → ℝ) :
    preferredCriticalWeight α ρ θ∈Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem preferredCriticalMultiplier_norm {n : ℕ} (α ρ : ℝ) (θ : Fin (n+1) → ℝ) :
    ‖preferredCriticalMultiplier α ρ θ‖≤1 ∧ ‖1-preferredCriticalMultiplier α ρ θ‖≤1 := by
  have hw := preferredCriticalWeight_mem α ρ θ
  constructor
  · simp only [preferredCriticalMultiplier,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
    exact hw.2
  · rw [preferredCriticalMultiplier,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hw.2)]
    linarith [hw.1]

/-- The actual critical multiplier is one on an entire open angular
neighborhood, not just on the equality locus. -/
theorem preferredCriticalMultiplier_one_neighborhood {n : ℕ} (α ρ : ℝ) :
    ∃ κ : ℝ,0<κ ∧ ∀ θ : Fin (n+1) → ℝ,
      (∀ i,|θ i+α|<κ) → preferredCriticalMultiplier α ρ θ=1 := by
  let F : (Fin (n+1) → ℝ) → ℝ := fun θ =>
    2-4*((∑ i : Fin n,(θ i.castSucc+α)^2)+(∑ i : Fin n,(θ i.castSucc+α))^2)/ρ^2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hc : F (fun _ => -α)=2 := by simp [F]
  have he : ∀ᶠ θ in 𝓝 (fun _ : Fin (n+1) => -α),1<F θ :=
    (continuousAt_const : ContinuousAt (fun _ : Fin (n+1) → ℝ => (1:ℝ)) _).eventually_lt
      hF.continuousAt (by rw [hc]; norm_num)
  obtain ⟨κ,hκ,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨κ,hκ,?_⟩
  intro θ hθ
  have hd : dist θ (fun _ : Fin (n+1) => -α)<κ := by
    rw [dist_eq_norm,pi_norm_lt_iff hκ]
    intro i
    simpa only [Pi.sub_apply,sub_neg_eq_add,Real.norm_eq_abs] using hθ i
  have hh := hball hd
  simp only [preferredCriticalMultiplier,preferredCriticalWeight]
  rw [show 2-4*((∑ i : Fin n,(θ i.castSucc+α)^2)+(∑ i : Fin n,(θ i.castSucc+α))^2)/ρ^2=F θ from rfl,
    Real.smoothTransition.one_of_one_le hh.le,Complex.ofReal_one]

/-- Every genuine shape coordinate, including the dependent last one,
is bounded by the intrinsic Euclidean shape norm. -/
theorem preferred_shape_coordinate_norm_bound {n : ℕ} (t : Fin n → ℝ) (i : Fin (n+1)) :
    |constrainedAngles t i|≤‖IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)‖ := by
  let x := IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)
  have hh := PiLp.norm_apply_le x.1 i
  simpa only [x,IsingBulk.First.shapeCoordinateEquiv_apply,PiLp.toLp_apply,
    IsingBulk.First.shapeExtend,constrainedAngles,Real.norm_eq_abs,Submodule.norm_coe] using hh

theorem preferred_shape_cutoff_chart_support {n : ℕ} (α : ℝ) {ρ : ℝ} (hρ : 0<ρ)
    (t : Fin n → ℝ)
    (ht : preferredShapeCutoff ρ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))≠0) :
    ∀ i,|firstChartAngles α t i+α|<ρ := by
  intro i
  have hh := (preferred_shape_coordinate_norm_bound t i).trans_lt (preferredShapeCutoff_support hρ _ ht)
  simpa only [firstChartAngles,sub_add_cancel] using hh

theorem preferredCriticalMultiplier_free_support {n : ℕ} (α : ℝ) {ρ : ℝ} (hρ : 0<ρ)
    (θ : Fin (n+1) → ℝ) (hθ : preferredCriticalMultiplier α ρ θ≠0) :
    ∀ i : Fin n,|θ i.castSucc+α|<ρ := by
  rw [preferredCriticalMultiplier_eq_shape] at hθ
  intro i
  have hh := preferred_shape_cutoff_chart_support α hρ _ hθ i.castSucc
  simpa only [firstChartAngles,constrainedAngles,Fin.snoc_castSucc,sub_add_cancel] using hh

/-- The critical chart is recovered exactly by the actual modular lift
when its first coordinates lie in the common original and lifted period. -/
theorem preferred_lower_mod_recover {δ x : ℝ}
    (hx : x∈Ioc (-Real.pi) Real.pi)
    (hy : toIocMod (by positivity : 0<2*Real.pi) (-Real.pi-δ) x∈Ioc (-Real.pi) Real.pi) :
    toIocMod (by positivity : 0<2*Real.pi) (-Real.pi-δ) x=x := by
  have hp : 0<2*Real.pi := by positivity
  have hxx : toIocMod hp (-Real.pi) x=x := (toIocMod_eq_self hp).mpr ⟨hx.1,by linarith [hx.2]⟩
  have hyy : toIocMod hp (-Real.pi) (toIocMod hp (-Real.pi-δ) x)=
      toIocMod hp (-Real.pi-δ) x := (toIocMod_eq_self hp).mpr ⟨hy.1,by linarith [hy.2]⟩
  have hh := toIocMod_toIocMod hp (-Real.pi) (-Real.pi-δ) x
  rw [hxx,hyy] at hh
  exact hh

theorem preferred_critical_angle_plateau {α δ ρ θ : ℝ} (_hδ : 0<δ)
    (hlo : ρ≤Real.pi-δ-α) (hhi : ρ≤α-δ) (hθ : |θ+α|<ρ) :
    θ∈Ioo (-Real.pi+δ) (-δ) := by
  obtain ⟨hθlo,hθhi⟩ := abs_lt.mp hθ
  constructor <;> linarith

/-- The compact critical multiplier is insensitive to the lift of the free
angles on the original Haar box. This is an exact equality, including the
original boundary convention. -/
theorem preferredCriticalMultiplier_lift_eq {n : ℕ} (α δ : ℝ) (hδ : 0<δ)
    {ρ : ℝ} (hρ : 0<ρ) (hlo : ρ≤Real.pi-δ-α) (hhi : ρ≤α-δ)
    (θ : Fin n → ℝ) (hθ : θ∈angularBox n) :
    preferredCriticalMultiplier α ρ (preferredLiftedAngles δ (constrainedAngles θ))=
      preferredCriticalMultiplier α ρ (constrainedAngles θ) := by
  let u := preferredLiftedAngles δ (constrainedAngles θ)
  have hEqFromLeft (hu : preferredCriticalMultiplier α ρ u≠0) :
      ∀ i : Fin n,u i.castSucc=θ i := by
    intro i
    have hcrit := preferredCriticalMultiplier_free_support α hρ u hu i
    have hplat := preferred_critical_angle_plateau hδ hlo hhi hcrit
    have hm : toIocMod (by positivity : 0<2*Real.pi) (-Real.pi-δ) (θ i)=u i.castSucc := by
      simp only [u,preferredLiftedAngles,constrainedAngles,Fin.snoc_castSucc]
    rw [←hm] at hplat
    rw [←hm]
    exact preferred_lower_mod_recover (hθ i (Set.mem_univ i)) ⟨by linarith [hplat.1],by linarith [hplat.2,Real.pi_pos]⟩
  have hEqFromRight (hu : preferredCriticalMultiplier α ρ (constrainedAngles θ)≠0) :
      ∀ i : Fin n,u i.castSucc=θ i := by
    intro i
    have hcrit := preferredCriticalMultiplier_free_support α hρ (constrainedAngles θ) hu i
    simp only [constrainedAngles,Fin.snoc_castSucc] at hcrit
    have hplat := preferred_critical_angle_plateau hδ hlo hhi hcrit
    have he : toIocMod (by positivity : 0<2*Real.pi) (-Real.pi-δ) (θ i)=θ i := by
      apply (toIocMod_eq_self (by positivity : 0<2*Real.pi)).mpr
      constructor <;> linarith [hplat.1,hplat.2,Real.pi_pos]
    simpa only [u,preferredLiftedAngles,constrainedAngles,Fin.snoc_castSucc] using he
  have he (h : ∀ i : Fin n,u i.castSucc=θ i) :
      preferredCriticalMultiplier α ρ u=preferredCriticalMultiplier α ρ (constrainedAngles θ) := by
    simp only [preferredCriticalMultiplier,preferredCriticalWeight,h,constrainedAngles,Fin.snoc_castSucc]
  by_cases hl : preferredCriticalMultiplier α ρ u=0
  · by_cases hr : preferredCriticalMultiplier α ρ (constrainedAngles θ)=0
    · exact hl.trans hr.symm
    · exact he (hEqFromRight hr)
  · exact he (hEqFromLeft hl)

end
end IsingBulk.Preferred22
