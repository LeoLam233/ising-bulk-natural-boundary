import IsingBulk.Preferred22.RightCoarea
import IsingBulk.Preferred22.ShellObligations
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-! The genuine full geometric extreme fibers of the affine right shell,
with their literal physical pair integral. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

theorem extremeShellFiber_isClosed {ι : Type*} (A r lo hi : ℝ) (z : ι → ℝ) :
    IsClosed (extremeShellFiber A r lo hi z) := by
  have hz : IsClosed {m : ℝ | ∀ i, m ≤ z i ∧ z i ≤ A-m} := by
    have he : {m : ℝ | ∀ i, m ≤ z i ∧ z i ≤ A-m} =
        ⋂ i : ι, {m : ℝ | m ≤ z i ∧ z i ≤ A-m} := by ext m; simp
    rw [he]
    exact isClosed_iInter (fun i =>
      (isClosed_le continuous_id continuous_const).inter
        (isClosed_le continuous_const (continuous_const.sub continuous_id)))
  exact (isClosed_le continuous_const continuous_id).inter
    ((isClosed_le (continuous_const.sub continuous_id) continuous_const).inter
      ((isClosed_le continuous_id (continuous_const.sub continuous_id)).inter
        ((isClosed_le continuous_const (continuous_const.sub (continuous_const.mul continuous_id))).inter
          ((isClosed_le (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const).inter hz))))

theorem extremeShellFiber_isCompact {ι : Type*} (A r lo hi : ℝ) (z : ι → ℝ) :
    IsCompact (extremeShellFiber A r lo hi z) := by
  apply isCompact_Icc.of_isClosed_subset (extremeShellFiber_isClosed A r lo hi z)
  intro m hm
  exact ⟨hm.1,hm.2.2.1.trans hm.2.1⟩

theorem extremeShellFiber_eq_Icc {ι : Type*} (A r lo hi : ℝ) (z : ι → ℝ)
    (hne : (extremeShellFiber A r lo hi z).Nonempty) :
    ∃ x y : ℝ, x ≤ y ∧ extremeShellFiber A r lo hi z = Icc x y := by
  have hc := extremeShellFiber_isCompact A r lo hi z
  refine ⟨sInf (extremeShellFiber A r lo hi z),sSup (extremeShellFiber A r lo hi z),
    csInf_le_csSup hne hc.bddBelow hc.bddAbove,?_⟩
  exact eq_Icc_of_connected_compact ⟨hne,(extremeShellFiber_ordConnected A r lo hi z).isPreconnected⟩ hc

def preferredFiberConfiguration {n : ℕ} (c : ℝ) (z : Fin n → ℝ) (m : ℝ) : Fin (n+2) → ℝ :=
  Fin.snoc (Fin.cons m z) (c-m-∑ i,z i)

theorem preferredFiberConfiguration_sum {n : ℕ} (c : ℝ) (z : Fin n → ℝ) (m : ℝ) :
    (∑ i,preferredFiberConfiguration c z m i)=c := by
  unfold preferredFiberConfiguration
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

theorem preferredFiberConfiguration_first {n : ℕ} (c : ℝ) (z : Fin n → ℝ) (m : ℝ) :
    preferredFiberConfiguration c z m 0=m := by
  simp [preferredFiberConfiguration]

theorem preferredFiberConfiguration_last {n : ℕ} (c : ℝ) (z : Fin n → ℝ) (m : ℝ) :
    preferredFiberConfiguration c z m (Fin.last (n+1))=(c-∑ i,z i)-m := by
  simp only [preferredFiberConfiguration,Fin.snoc_last]
  ring

theorem preferredFiberConfiguration_other {n : ℕ} (c : ℝ) (z : Fin n → ℝ) (m : ℝ) (i : Fin n) :
    preferredFiberConfiguration c z m i.succ.castSucc=z i := by
  simp only [preferredFiberConfiguration,Fin.snoc_castSucc,Fin.cons_succ]

theorem preferredFiberConfiguration_eq_extremePath {n : ℕ} (c : ℝ) (z : Fin n → ℝ) (m : ℝ) :
    preferredFiberConfiguration c z m =
      extremeAnglePath (preferredFiberConfiguration c z 0) 0 (Fin.last (n+1)) m := by
  funext v
  refine Fin.lastCases ?_ (fun a => ?_) v
  · simp [preferredFiberConfiguration,extremeAnglePath]
    ring
  · refine Fin.cases ?_ (fun i => ?_) a
    · simp [preferredFiberConfiguration,extremeAnglePath]
    · have h0 : i.succ.castSucc ≠ (0:Fin (n+2)) := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_zero] at hh
        omega
      have hl := Fin.castSucc_ne_last i.succ
      simp only [extremeAnglePath,ite_eq_right h0,ite_eq_right hl,add_zero,sub_zero,
        preferredFiberConfiguration_other]

theorem preferredFiberConfiguration_geometry {n : ℕ} {c m r lo hi : ℝ} {z : Fin n → ℝ}
    (hm : m ∈ extremeShellFiber (c-∑ i,z i) r lo hi z) :
    (∀ v,preferredFiberConfiguration c z m v∈Icc lo hi) ∧
    (∀ v,preferredFiberConfiguration c z m 0 ≤ preferredFiberConfiguration c z m v ∧
      preferredFiberConfiguration c z m v ≤ preferredFiberConfiguration c z m (Fin.last (n+1))) ∧
    r ≤ preferredFiberConfiguration c z m (Fin.last (n+1))-preferredFiberConfiguration c z m 0 ∧
    preferredFiberConfiguration c z m (Fin.last (n+1))-preferredFiberConfiguration c z m 0 ≤ 2*r := by
  obtain ⟨hlo,hhi,horder,hrlo,hrhi,hz⟩ := hm
  simp only [preferredFiberConfiguration_first,preferredFiberConfiguration_last]
  refine ⟨?_,?_,by linarith,by linarith⟩
  · intro v
    refine Fin.lastCases ?_ (fun a => ?_) v
    · rw [preferredFiberConfiguration_last]
      constructor <;> linarith
    · refine Fin.cases ?_ (fun i => ?_) a
      · rw [show (0:Fin (n+1)).castSucc=(0:Fin (n+2)) by rfl,preferredFiberConfiguration_first]
        constructor <;> linarith
      · rw [preferredFiberConfiguration_other]
        have hv := hz i
        constructor <;> linarith [hv.1,hv.2]
  · intro v
    refine Fin.lastCases ?_ (fun a => ?_) v
    · rw [preferredFiberConfiguration_last]
      exact ⟨horder,le_rfl⟩
    · refine Fin.cases ?_ (fun i => ?_) a
      · rw [show (0:Fin (n+1)).castSucc=(0:Fin (n+2)) by rfl,preferredFiberConfiguration_first]
        exact ⟨le_rfl,horder⟩
      · rw [preferredFiberConfiguration_other]
        exact hz i

theorem preferredFiberConfiguration_mean_window {n : ℕ} (d : PreferredBranchData)
    {c m r lo hi : ℝ} {z : Fin n → ℝ}
    (hm : m ∈ extremeShellFiber (c-∑ i,z i) r lo hi z) :
    let t := d.b+c/((n+2:ℕ):ℝ)
    ∀ v, t-2*r ≤ preferredFiberConfiguration c z m v+d.b ∧
      preferredFiberConfiguration c z m v+d.b ≤ t+2*r := by
  let t := d.b+c/((n+2:ℕ):ℝ)
  have hmean : (∑ v,(preferredFiberConfiguration c z m v+d.b))=((n+2:ℕ):ℝ)*t := by
    rw [Finset.sum_add_distrib,preferredFiberConfiguration_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,t]
    have hN : ((n+2:ℕ):ℝ)≠0 := by positivity
    field_simp
    ring
  obtain ⟨_,hext,_,hdiam⟩ := preferredFiberConfiguration_geometry hm
  apply constrained_shell_coordinate_window (i := 0) (j := Fin.last (n+1)) (by omega) hmean
  · intro v
    have hv := hext v
    constructor <;> linarith [hv.1,hv.2]
  · linarith

set_option maxHeartbeats 1200000 in
/-- The complete actual physical pair integral on the full geometric
extreme fiber. Empty fibers, all constrained means and all positive diameters
are included. No finite-component assumption is made about a cutoff. -/
theorem preferred_geometric_fiber_pair_integral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ → 0 < r →
      ∀ z : Fin n → ℝ,
      (∫ m in extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
          ‖1-preferredActualZ d B ε τ (preferredFiberConfiguration c z m)‖) ≤
        C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ := preferred_right_extreme_integral d B
  refine ⟨2*C,ε₀,τ₀,δB,by positivity,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro n ε τ c r hε hεr hτ hτr hr z
  let F := extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
  let t := d.b+c/((n+2:ℕ):ℝ)
  let T := |t|+r+ε
  have hT : 0 < T := by dsimp [T]; positivity
  by_cases hne : F.Nonempty
  · obtain ⟨x,y,hxy,hF⟩ := extremeShellFiber_eq_Icc (c-∑ i,z i) r (-d.b-δB) B.delta z hne
    have hR := hbound (n+2) (by omega) ε τ hε hεr hτ hτr
      (preferredFiberConfiguration c z 0) 0 (Fin.last (n+1)) x y r (2*T) hxy hr
      (by dsimp [T]; linarith [abs_nonneg t]) (by
        intro m hm
        have hmem : m ∈ F := by
          change m ∈ extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
          rw [hF]
          exact hm
        have hg := preferredFiberConfiguration_geometry hmem
        have hwin := preferredFiberConfiguration_mean_window d hmem (Fin.last (n+1))
        have hscale : preferredFiberConfiguration c z m (Fin.last (n+1))+d.b+ε ≤ 2*T := by
          dsimp [T,t]
          linarith [hwin.2,le_abs_self (d.b+c/((n+2:ℕ):ℝ)),abs_nonneg (d.b+c/((n+2:ℕ):ℝ))]
        simpa only [← preferredFiberConfiguration_eq_extremePath] using
          And.intro hg.1 (And.intro hg.2.1 (And.intro hg.2.2.1 hscale)))
    have hsqrt : Real.sqrt (2*T) ≤ 2*Real.sqrt T := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have h2 : Real.sqrt (2:ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
      exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg T)
    rw [hF,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hxy]
    calc
      _ ≤ C*((n+2:ℕ):ℝ)*Real.sqrt (2*T)/r*(1+|Real.log ε|) := by
        simpa only [← preferredFiberConfiguration_eq_extremePath] using hR
      _ ≤ C*((n+2:ℕ):ℝ)*(2*Real.sqrt T)/r*(1+|Real.log ε|) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hr.le) (by positivity)
      _ = _ := by dsimp [T,t]; ring
  · have hF : F=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change (∫ m in F, _) ≤ _
    rw [hF,setIntegral_empty]
    positivity

/-- Continuity of the literal physical pair resolvent on every real
constrained path. Strict product attenuation follows from the physical sheet
of any one factor and nonnegative attenuation of all remaining factors. -/
theorem preferred_extreme_resolvent_continuous {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i j : Fin N) :
    Continuous (fun t : ℝ =>
      preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j /
        ‖1-preferredActualZ d B ε τ (extremeAnglePath θ i j t)‖) := by
  have hnum : Continuous (fun t : ℝ => preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j) :=
    ((preferred_extreme_slope_continuous hN d B hε hτ θ i j i).add continuous_const |>.mul
      ((preferred_extreme_slope_continuous hN d B hε hτ θ i j j).add continuous_const)).norm
  have hG : Continuous (fun t : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)) :=
    (preferred_extreme_phase_smooth d B hε hτ θ i j).continuous
  have hZ : Continuous (fun t : ℝ => preferredActualZ d B ε τ (extremeAnglePath θ i j t)) := by
    simp_rw [preferredActualZ_eq_exp d B hε hτ]
    fun_prop
  have hden (t : ℝ) : ‖1-preferredActualZ d B ε τ (extremeAnglePath θ i j t)‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    rw [preferredActualZ_eq_exp d B hε hτ]
    apply preferred_phase_denominator_ne_zero
    have hs : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
      (by linarith [d.alpha_lt,Real.pi_pos])
    have hW := (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ (extremeAnglePath θ i j t) i)
    have hneg := (IsingBulk.Branch.lowerArccos_sheet_of_upper hW).2.2.2
    have hsum := preferred_single_phase_attenuation_le_total d B hε hτ (extremeAnglePath θ i j t) i
    change (preferredAngularPhase d ε (deformedAngles τ B.p B.m (extremeAnglePath θ i j t) i)).im < 0 at hneg
    linarith
  exact hnum.div ((continuous_const.sub hZ).norm) hden

theorem preferred_geometric_fiber_pair_integrable {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (c r lo hi : ℝ) (z : Fin n → ℝ) :
    IntegrableOn (fun m : ℝ =>
      preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
        ‖1-preferredActualZ d B ε τ (preferredFiberConfiguration c z m)‖)
      (extremeShellFiber (c-∑ i,z i) r lo hi z) := by
  have hc := preferred_extreme_resolvent_continuous (by omega : 0 < n+2) d B hε hτ
    (preferredFiberConfiguration c z 0) 0 (Fin.last (n+1))
  have hc' : Continuous (fun m : ℝ =>
      preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
        ‖1-preferredActualZ d B ε τ (preferredFiberConfiguration c z m)‖) := by
    simpa only [← preferredFiberConfiguration_eq_extremePath] using hc
  exact hc'.continuousOn.integrableOn_compact (extremeShellFiber_isCompact _ _ _ _ _)

/-- Nonnegative-integral form for genuine Tonelli assembly of the complete
actual transported density. The finite physical pair integral is proved here,
not supplied as a tail-envelope hypothesis. -/
theorem preferred_geometric_fiber_pair_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ → 0 < r →
      ∀ z : Fin n → ℝ,
      (∫⁻ m in extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        ENNReal.ofReal (preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
          ‖1-preferredActualZ d B ε τ (preferredFiberConfiguration c z m)‖)) ≤
        ENNReal.ofReal (C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|)) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ := preferred_geometric_fiber_pair_integral d B
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro n ε τ c r hε hεr hτ hτr hr z
  rw [← ofReal_integral_eq_lintegral_ofReal
    (preferred_geometric_fiber_pair_integrable d B hε hτ c r (-d.b-δB) B.delta z)
    (Filter.Eventually.of_forall (fun m : ℝ => by unfold preferredExtremePair; positivity))]
  exact ENNReal.ofReal_le_ofReal (hbound n ε τ c r hε hεr hτ hτr hr z)

end
end IsingBulk.Preferred22
