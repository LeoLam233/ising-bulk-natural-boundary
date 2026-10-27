import IsingBulk.Preferred22.CriticalCutoff

/-! Exact critical-chart localization of the complete lifted right integral.
The modular dependent angle, translation of the free Haar coordinates and
all original normalization factors are identified explicitly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The resonance fixes the integer winding of the eliminated angle.
Consequently the actual lift of a supported first chart is that chart. -/
theorem preferred_critical_lift_firstChart {n : ℕ} (α δ : ℝ) (hδ : 0<δ)
    (k : ℤ) (hres : ((n+1:ℕ):ℝ)*α=(k:ℝ)*(2*Real.pi))
    (θ : Fin n → ℝ)
    (hchart : ∀ i,firstChartAngles α (fun j => θ j+α) i∈Ioo (-Real.pi+δ) (-δ)) :
    preferredLiftedAngles δ (constrainedAngles θ)=firstChartAngles α (fun j => θ j+α) := by
  have hp : 0<2*Real.pi := by positivity
  funext i
  change toIocMod hp (-Real.pi-δ) (constrainedAngles θ i)=_
  apply (toIocMod_eq_iff hp).mpr
  refine ⟨⟨by linarith [(hchart i).1],by linarith [(hchart i).2,Real.pi_pos]⟩,?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · refine ⟨k,?_⟩
    have hs : (∑ j : Fin n,(θ j+α))=(∑ j : Fin n,θ j)+(n:ℝ)*α := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp only [firstChartAngles,constrainedAngles,Fin.snoc_last,hs,zsmul_eq_mul]
    push_cast at hres
    linarith
  · refine ⟨0,?_⟩
    simp only [firstChartAngles,constrainedAngles,Fin.snoc_castSucc,add_sub_cancel_right,zero_zsmul,add_zero]

/-- On every sufficiently small actual shape cutoff, the complete lifted
right integral equals the physical localized integral as a function of s.
The equality is valid for every deformation strength and parameter, so it
also identifies every complex derivative without an asymptotic argument. -/
theorem preferred_critical_localization (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB : ℝ) (rcut : ℝ → ℝ)
    (hr : PreferredRightCutoffData d B δB rcut) :
    ∃ R : ℝ,0<R ∧ ∀ n : ℕ,∀ k : ℤ,
      ((n+1:ℕ):ℝ)*d.alpha=(k:ℝ)*(2*Real.pi) →
      ∀ ρ : ℝ,0<ρ → ρ≤R → ∀ τ : ℝ,
      preferredWeightedRightIntegral n d B (preferredCriticalMultiplier d.alpha ρ) τ rcut 0=
        localizedPhysicalIntegral d.alpha (preferredShapeCutoff (n := n) ρ) := by
  obtain ⟨R₀,hR₀,hloc⟩ := preferred_localized_integral_eq_right_seed d B δB rcut hr
  have hleft : 0<Real.pi-B.delta-d.alpha := by
    linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]
  have hright : 0<d.alpha-B.delta := by linarith [B.delta_alpha,d.alpha_pos]
  let R := min R₀ (min (Real.pi-B.delta-d.alpha) (d.alpha-B.delta))
  have hR : 0<R := lt_min hR₀ (lt_min hleft hright)
  refine ⟨R,hR,?_⟩
  intro n k hres ρ hρ hρR τ
  have hρ₀ : ρ≤R₀ := hρR.trans (min_le_left _ _)
  have hρl : ρ≤Real.pi-B.delta-d.alpha :=
    hρR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρr : ρ≤d.alpha-B.delta :=
    hρR.trans ((min_le_right _ _).trans (min_le_right _ _))
  funext s
  let χ := preferredShapeCutoff (n := n) ρ
  let F : (Fin n → ℝ) → ℂ := fun t =>
    χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))*
      preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut s (firstChartAngles d.alpha t)
  have hχ (t : Fin n → ℝ) (ht : χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))≠0) :
      ∀ i,|firstChartAngles d.alpha t i+d.alpha|<ρ :=
    preferred_shape_cutoff_chart_support d.alpha hρ t ht
  have hsource (t : Fin n → ℝ) (ht : χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))≠0) :
      ∀ i,|firstChartAngles d.alpha t i+d.alpha|<R₀ := fun i => (hχ t ht i).trans_le hρ₀
  have hlocal := hloc n χ hsource τ s
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have he (θ : Fin n → ℝ) (hθ : θ∈angularBox n) :
      preferredWeightedPhysicalDensity (preferredCriticalMultiplier d.alpha ρ) τ preferredPopulationCutoff
        B.p B.m rcut 0 s (preferredLiftedAngles B.delta (constrainedAngles θ))=
        F (θ+(fun _ => d.alpha)) := by
    let t : Fin n → ℝ := fun i => θ i+d.alpha
    let u := preferredLiftedAngles B.delta (constrainedAngles θ)
    have hcut : preferredCriticalMultiplier d.alpha ρ u=
        χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t)) := by
      rw [preferredCriticalMultiplier_lift_eq d.alpha B.delta B.delta_pos hρ hρl hρr θ hθ,
        preferredCriticalMultiplier_eq_shape]
      simp only [constrainedAngles,Fin.snoc_castSucc,χ,t]
    change preferredCriticalMultiplier d.alpha ρ u*
      preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut s u=
      χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))*
        preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m rcut s (firstChartAngles d.alpha t)
    rw [hcut]
    by_cases hz : χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))=0
    · simp only [hz,zero_mul]
    · have hchart (i : Fin (n+1)) : firstChartAngles d.alpha t i∈Ioo (-Real.pi+B.delta) (-B.delta) :=
        preferred_critical_angle_plateau B.delta_pos hρl hρr (hχ t hz i)
      rw [show u=firstChartAngles d.alpha t from
        preferred_critical_lift_firstChart d.alpha B.delta B.delta_pos k hres θ hchart]
  have hzero (θ : Fin n → ℝ) (hθ : θ∉angularBox n) : F (θ+(fun _ => d.alpha))=0 := by
    let t : Fin n → ℝ := fun i => θ i+d.alpha
    by_cases hz : χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))=0
    · change χ (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))*_=0
      rw [hz,zero_mul]
    · exfalso
      apply hθ
      intro i _
      have hc := hχ t hz i.castSucc
      simp only [firstChartAngles,constrainedAngles,Fin.snoc_castSucc,sub_add_cancel,t] at hc
      have hp := preferred_critical_angle_plateau B.delta_pos hρl hρr hc
      exact ⟨by linarith [hp.1,B.delta_pos],by linarith [hp.2,Real.pi_pos,B.delta_pos]⟩
  calc
    preferredWeightedRightIntegral n d B (preferredCriticalMultiplier d.alpha ρ) τ rcut 0 s=
        ∫ θ in angularBox n,F (θ+(fun _ => d.alpha)) := by
      unfold preferredWeightedRightIntegral
      exact setIntegral_congr_fun hbox he
    _ = ∫ θ : Fin n → ℝ,F (θ+(fun _ => d.alpha)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ = ∫ t : Fin n → ℝ,F t := integral_add_right_eq_self F (fun _ => d.alpha)
    _ = localizedPhysicalIntegral d.alpha (preferredShapeCutoff ρ) s := hlocal.symm

/-- The prime first order has exactly the integer winding required by the
preceding actual chart identity. -/
theorem preferred_prime_critical_winding (d : PreferredBranchData) {p n : ℕ}
    (hp : 0<p) (hN : n+1=2*p) {a : ℤ}
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ((n+1:ℕ):ℝ)*d.alpha=((2*a:ℤ):ℝ)*(2*Real.pi) := by
  rw [hN,hα]
  unfold IsingBulk.PrimeFamily.angle
  have hp' : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- The smooth original complement needed by the finite first-chart
remainder. Its norm is at most one and it vanishes on an entire critical
neighborhood; the local integral is the exact normalized physical one. -/
theorem preferred_critical_cutoff_package (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB : ℝ) (rcut : ℝ → ℝ)
    (hr : PreferredRightCutoffData d B δB rcut) (n : ℕ) (k : ℤ)
    (hres : ((n+1:ℕ):ℝ)*d.alpha=(k:ℝ)*(2*Real.pi))
    (Rmax : ℝ) (hRmax : 0<Rmax) :
    ∃ ρ κ : ℝ,0<ρ ∧ ρ≤Rmax ∧ 0<κ ∧
      ContDiff ℝ ∞ (preferredCriticalMultiplier (n := n) d.alpha ρ) ∧
      ContDiff ℝ ∞ (fun θ : Fin (n+1) → ℝ => 1-preferredCriticalMultiplier d.alpha ρ θ) ∧
      (∀ θ : Fin (n+1) → ℝ,‖1-preferredCriticalMultiplier d.alpha ρ θ‖≤1) ∧
      (∀ θ : Fin (n+1) → ℝ,(∀ i,|θ i+d.alpha|<κ) → 1-preferredCriticalMultiplier d.alpha ρ θ=0) ∧
      ∀ τ : ℝ,preferredWeightedRightIntegral n d B (preferredCriticalMultiplier d.alpha ρ) τ rcut 0=
        localizedPhysicalIntegral d.alpha (preferredShapeCutoff (n := n) ρ) := by
  obtain ⟨R,hR,hloc⟩ := preferred_critical_localization d B δB rcut hr
  let ρ := min R Rmax
  have hρ : 0<ρ := lt_min hR hRmax
  obtain ⟨κ,hκ,hnear⟩ := preferredCriticalMultiplier_one_neighborhood (n := n) d.alpha ρ
  refine ⟨ρ,κ,hρ,min_le_right _ _,hκ,preferredCriticalMultiplier_smooth _ _,
    contDiff_const.sub (preferredCriticalMultiplier_smooth _ _),fun θ => (preferredCriticalMultiplier_norm _ _ θ).2,?_,?_⟩
  · intro θ hθ
    rw [hnear θ hθ,sub_self]
  · intro τ
    exact hloc n k hres ρ hρ (min_le_left _ _) τ

end
end IsingBulk.Preferred22
