import IsingBulk.Preferred22.HyperplanePermutation
import IsingBulk.Preferred22.RightShellMeasure
import IsingBulk.Preferred22.JacobianContinuity
import IsingBulk.Preferred22.TransportedFiberBound

/-! Genuine complete constrained shell integration of the literal physical
Jacobian/resolvent. The result retains every mean and every positive shell
diameter. The transported-density application has only the explicit remaining
pointwise q20 majorant; no integrated shell or tail bound is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal

def preferredFullRightShell {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB r : ℝ) (i j : Fin N) : Set (Fin N → ℝ) :=
  {w | (∀ v,w v∈Icc (-d.b-δB) B.delta) ∧
    (∀ v,w i≤w v ∧ w v≤w j) ∧ r≤w j-w i ∧ w j-w i≤2*r}

theorem preferredFullRightShell_isClosed {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r : ℝ) (i j : Fin N) :
    IsClosed (preferredFullRightShell d B δB r i j) := by
  have h₁ : IsClosed {w : Fin N → ℝ | ∀ v,w v∈Icc (-d.b-δB) B.delta} := by
    have he : {w : Fin N → ℝ | ∀ v,w v∈Icc (-d.b-δB) B.delta}=
        ⋂ v : Fin N,{w : Fin N → ℝ | w v∈Icc (-d.b-δB) B.delta} := by ext w; simp
    rw [he]
    exact isClosed_iInter (fun v => isClosed_Icc.preimage (continuous_apply v))
  have h₂ : IsClosed {w : Fin N → ℝ | ∀ v,w i≤w v ∧ w v≤w j} := by
    have he : {w : Fin N → ℝ | ∀ v,w i≤w v ∧ w v≤w j}=
        ⋂ v : Fin N,{w : Fin N → ℝ | w i≤w v ∧ w v≤w j} := by ext w; simp
    rw [he]
    exact isClosed_iInter (fun v => (isClosed_le (continuous_apply i) (continuous_apply v)).inter
      (isClosed_le (continuous_apply v) (continuous_apply j)))
  exact h₁.inter (h₂.inter ((isClosed_le continuous_const
    ((continuous_apply j).sub (continuous_apply i))).inter
    (isClosed_le ((continuous_apply j).sub (continuous_apply i)) continuous_const)))

theorem preferredFullRightShell_fiber_iff {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r c m : ℝ) (z : Fin n → ℝ) :
    preferredFiberConfiguration c z m∈preferredFullRightShell d B δB r 0 (Fin.last (n+1)) ↔
      m∈extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z := by
  constructor
  · rintro ⟨hbox,hext,hlo,hhi⟩
    have hm := (hbox 0).1
    have hM := (hbox (Fin.last (n+1))).2
    have hord := (hext (Fin.last (n+1))).1
    simp only [preferredFiberConfiguration_first,preferredFiberConfiguration_last] at hm hM hord hlo hhi
    refine ⟨hm,hM,hord,by linarith,by linarith,?_⟩
    intro i
    have hh := hext i.succ.castSucc
    simpa only [preferredFiberConfiguration_first,preferredFiberConfiguration_last,
      preferredFiberConfiguration_other] using hh
  · exact preferredFiberConfiguration_geometry

theorem preferredFullRightShell_perm {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r : ℝ) (i j : Fin N)
    (e : Equiv.Perm (Fin N)) (w : Fin N → ℝ) :
    (w ∘ e)∈preferredFullRightShell d B δB r (e.symm i) (e.symm j) ↔
      w∈preferredFullRightShell d B δB r i j := by
  simp only [preferredFullRightShell,mem_ofPred_eq,Function.comp_apply,Equiv.apply_symm_apply]
  constructor
  · rintro ⟨hb,he,hl,hr⟩
    exact ⟨fun v => by simpa only [Equiv.apply_symm_apply] using hb (e.symm v),
      fun v => by simpa only [Equiv.apply_symm_apply] using he (e.symm v),hl,hr⟩
  · rintro ⟨hb,he,hl,hr⟩
    exact ⟨fun v => hb (e v),fun v => he (e v),hl,hr⟩

theorem preferred_full_shell_indicator_permutation {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r ε τ c : ℝ) (i j : Fin (n+1))
    (e : Equiv.Perm (Fin (n+1))) :
    (∫⁻ x : Fin n → ℝ,
      (preferredFullRightShell d B δB r (e.symm i) (e.symm j)).indicator
        (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) (constrainedAtTotal c x)) =
      ∫⁻ x : Fin n → ℝ,
        (preferredFullRightShell d B δB r i j).indicator
          (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) (constrainedAtTotal c x) := by
  rw [← constrained_hyperplane_lintegral_perm e c]
  apply lintegral_congr
  intro x
  let w := constrainedAtTotal c x
  change (preferredFullRightShell d B δB r (e.symm i) (e.symm j)).indicator
    (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) (w ∘ e) =
      (preferredFullRightShell d B δB r i j).indicator
        (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) w
  by_cases hw : w∈preferredFullRightShell d B δB r i j
  · have he := (preferredFullRightShell_perm d B δB r i j e w).2 hw
    rw [Set.indicator_of_mem he,Set.indicator_of_mem hw,preferredJacobianResolvent_equiv]
  · have he := mt (preferredFullRightShell_perm d B δB r i j e w).1 hw
    rw [Set.indicator_of_notMem he,Set.indicator_of_notMem hw]

set_option maxHeartbeats 1400000 in
/-- Complete actual constrained Jacobian/resolvent shell integral, with the
canonical minimum and maximum. The full fiber and all remaining coordinates
are integrated with their true Lebesgue measures. -/
theorem preferred_canonical_shell_jacobian_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r δB : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ →
      (∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r 0 (Fin.last (n+1))).indicator
          (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hfiber⟩ := preferred_q20_fiber_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n ε τ c r δB hε hεr hτ hτr hr hδB hδ
  let S := preferredFullRightShell d B δB r 0 (Fin.last (n+1))
  let G := S.indicator (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w))
  let t := d.b+c/((n+2:ℕ):ℝ)
  let T := |t|+r+ε
  let L := C*((n+2:ℕ):ℝ)*Real.sqrt T/r*(1+|Real.log ε|)
  let W := preferredShiftedOneBodyBox n d.b t r
  have hG : Measurable G :=
    ((preferredJacobianResolvent_continuous (by omega : 0<n+2) d B hε hτ).measurable.ennreal_ofReal).indicator
      (preferredFullRightShell_isClosed d B δB r 0 (Fin.last (n+1))).measurableSet
  have hc : Continuous (constrainedAtTotal (n := n+1) c) := by unfold constrainedAtTotal; fun_prop
  change (∫⁻ x : Fin (n+1) → ℝ,G (constrainedAtTotal c x)) ≤ _
  rw [constrained_hyperplane_lintegral_cons c G (hG.comp hc.measurable).aemeasurable]
  have hinner (z : Fin n → ℝ) :
      (∫⁻ m : ℝ,G (preferredFiberConfiguration c z m)) ≤
        W.indicator (fun z => ENNReal.ofReal (A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*L)) z := by
    let F := extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
    have he : (fun m => G (preferredFiberConfiguration c z m)) =
        F.indicator (fun m => ENNReal.ofReal (preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z m))) := by
      funext m
      by_cases hm : m∈F
      · have hs := (preferredFullRightShell_fiber_iff d B δB r c m z).2 hm
        exact (Set.indicator_of_mem hs _).trans (Set.indicator_of_mem hm (fun t => ENNReal.ofReal (preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z t)))).symm
      · have hs := mt (preferredFullRightShell_fiber_iff d B δB r c m z).1 hm
        exact (Set.indicator_of_notMem hs _).trans (Set.indicator_of_notMem hm (fun t => ENNReal.ofReal (preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z t)))).symm
    rw [he,lintegral_indicator (extremeShellFiber_isClosed _ _ _ _ _).measurableSet]
    have hh := hfiber n ε τ c r δB 1 hε hεr hτ hτr hr hδB hδ (by norm_num)
      (preferredJacobianResolvent d B ε τ) (Equiv.refl _) z (by intro m _; simp)
    simpa only [Function.comp_def,Equiv.refl_apply,one_mul] using hh
  have hL : 0 ≤ A^n*L := by dsimp [L,T]; positivity
  calc
    _ ≤ ∫⁻ z : Fin n → ℝ,
        W.indicator (fun z => ENNReal.ofReal (A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*L)) z :=
      lintegral_mono hinner
    _ = ∫⁻ z in W,ENNReal.ofReal (A^n*L)*ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (z i+d.b)) := by
      rw [lintegral_indicator (preferredShiftedOneBodyBox_measurable _ _ _ _)]
      apply lintegral_congr
      intro z
      rw [← ENNReal.ofReal_mul hL]
      congr 1
      ring
    _ = ENNReal.ofReal (A^n*L)*∫⁻ z in W,ENNReal.ofReal (∏ i,preferredOneBodyMajorant ε (z i+d.b)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A^n*L)*ENNReal.ofReal ((32*r/Real.sqrt T)^n) := by
      have hh := preferredShiftedOneBodyBox_lintegral n hε hr d.b t
      simpa only [mul_comm] using mul_le_mul_left hh (ENNReal.ofReal (A^n*L))
    _ = _ := by rw [← ENNReal.ofReal_mul hL]


/-- A literal permutation puts any distinct pair at the canonical extreme
positions. No symmetry of a transported density is used. -/
theorem preferred_extreme_permutation {n : ℕ} (i j : Fin (n+2)) (hij : i≠j) :
    ∃ e : Equiv.Perm (Fin (n+2)),e i=0 ∧ e j=Fin.last (n+1) := by
  let a := Equiv.swap i 0
  let b := Equiv.swap (a j) (Fin.last (n+1))
  refine ⟨a.trans b,?_,?_⟩
  · have hji : a j≠0 := by
      intro h
      have hi : a i=0 := Equiv.swap_apply_left _ _
      exact hij (a.injective (hi.trans h.symm))
    have hlast : (0:Fin (n+2))≠Fin.last (n+1) := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_zero,Fin.val_last] at hh
      omega
    change b (a i)=0
    rw [show a i=0 from Equiv.swap_apply_left _ _]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) hlast
  · change b (a j)=Fin.last (n+1)
    exact Equiv.swap_apply_left _ _

/-- The complete actual shell Jacobian/resolvent bound for every pair of
extreme indices. Every change of eliminated coordinate preserves Lebesgue
measure exactly. -/
theorem preferred_shell_jacobian_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r δB : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → ∀ i j : Fin (n+2),
      (∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r i j).indicator
          (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hcanon⟩ := preferred_canonical_shell_jacobian_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n ε τ c r δB hε hεr hτ hτr hr hδB hδ i j
  by_cases hij : i=j
  · subst j
    have hs : preferredFullRightShell d B δB r i i=∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro w hw
      have hh := hw.2.2.1
      simp only [sub_self] at hh
      exact (not_le_of_gt hr) hh
    rw [hs]
    simp only [Set.indicator_empty,lintegral_zero]
    exact bot_le
  · obtain ⟨e,hi,hj⟩ := preferred_extreme_permutation i j hij
    have hi' : e.symm 0=i := e.injective (by simp only [Equiv.apply_symm_apply,hi])
    have hj' : e.symm (Fin.last (n+1))=j := e.injective (by simp only [Equiv.apply_symm_apply,hj])
    have he := preferred_full_shell_indicator_permutation d B δB r ε τ c 0 (Fin.last (n+1)) e
    rw [hi',hj'] at he
    rw [he]
    exact hcanon n ε τ c r δB hε hεr hτ hτr hr hδB hδ

/-- Integrated q20 on the actual affine shell from its literal pointwise
majorant. This theorem proves the complete measure conversion and integration;
it does not assume a shell estimate or a tail estimate. -/
theorem preferred_shell_q20_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r δB K : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → 0 ≤ K → ∀ i j : Fin (n+2),
      ∀ f : (Fin (n+2) → ℝ) → ℝ,
      (∀ x : Fin (n+1) → ℝ, constrainedAtTotal c x∈preferredFullRightShell d B δB r i j →
        f (constrainedAtTotal c x) ≤ K*preferredJacobianResolvent d B ε τ (constrainedAtTotal c x)) →
      (∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r i j).indicator
          (fun w => ENNReal.ofReal (f w)) (constrainedAtTotal c x)) ≤
      ENNReal.ofReal (K*(A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n)) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hjac⟩ := preferred_shell_jacobian_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK i j f hpoint
  let S := preferredFullRightShell d B δB r i j
  let J := fun x : Fin (n+1) → ℝ =>
    S.indicator (fun w => ENNReal.ofReal (preferredJacobianResolvent d B ε τ w)) (constrainedAtTotal c x)
  calc
    _ ≤ ∫⁻ x : Fin (n+1) → ℝ,ENNReal.ofReal K*J x := by
      apply lintegral_mono
      intro x
      by_cases hx : constrainedAtTotal c x∈S
      · dsimp [J]
        rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (hpoint x hx)
      · dsimp [J]
        rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx,mul_zero]
    _ = ENNReal.ofReal K*∫⁻ x : Fin (n+1) → ℝ,J x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal
        (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|))*
          (32*r/Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε))^n) := by
      have hh := hjac n ε τ c r δB hε hεr hτ hτr hr hδB hδ i j
      simpa only [mul_comm] using mul_le_mul_left hh (ENNReal.ofReal K)
    _ = _ := by rw [← ENNReal.ofReal_mul hK]


/-- The actual lifted transported density on the original angular shell.
Only its explicit pointwise q20 domination is a hypothesis; the complete
constrained-shell integration and periodic lift conversion are proved. -/
theorem preferred_transported_shell_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n k : ℕ, ∀ ε τ r δB K : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → 0 ≤ K → ∀ η rcut : ℝ → ℝ,
      ∀ l : ℤ, ∀ i j : Fin (n+2),
      (∀ x ∈ preferredRightShell d B δB r l i j,
        ‖preferredTransportedDensity .right τ η B.p B.m rcut k
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖ ≤
        K*preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x))) →
      (∫⁻ x in preferredRightShell d B δB r l i j,
        ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut k
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖) ≤
      ENNReal.ofReal (K*(A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (preferredShellScale d (n+2) l r ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (preferredShellScale d (n+2) l r ε))^n)) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hq⟩ := preferred_shell_q20_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n k ε τ r δB K hε hεr hτ hτr hr hδB hδ hK η rcut l i j hpoint
  have hδδ : δB<B.delta := hδ.trans_lt hδ₀δ
  let c := 2*Real.pi*(l:ℝ)
  let f := fun w : Fin (n+2) → ℝ => ‖preferredTransportedDensity .right τ η B.p B.m rcut k
    (IsingBulk.Branch.radialParameter d.alpha ε) w‖
  have hb : ∀ x : Fin (n+1) → ℝ, constrainedAtTotal c x∈preferredFullRightShell d B δB r i j →
      f (constrainedAtTotal c x) ≤ K*preferredJacobianResolvent d B ε τ (constrainedAtTotal c x) := by
    intro x hx
    have hl : x∈preferredLinearRightShell d B δB r l i j := hx
    have hs : x∈preferredRightShell d B δB r l i j := by
      rw [preferredRightShell_eq_linear d B hδδ]
      exact hl
    have he := (preferred_lift_eq_affine_from_right d B hδδ l x hl.1).2
    simpa only [he] using hpoint x hs
  have hh := hq n ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK i j f hb
  calc
    _ = ∫⁻ x in preferredLinearRightShell d B δB r l i j,
        ENNReal.ofReal (f (constrainedAtTotal c x)) := by
      rw [preferredRightShell_eq_linear d B hδδ]
      apply setLIntegral_congr_fun (preferredLinearRightShell_isClosed d B δB r l i j).measurableSet
      intro x hx
      dsimp only
      rw [(preferred_lift_eq_affine_from_right d B hδδ l x hx.1).2]
    _ = ∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r i j).indicator (fun w => ENNReal.ofReal (f w))
          (constrainedAtTotal c x) := by
      rw [← lintegral_indicator (preferredLinearRightShell_isClosed d B δB r l i j).measurableSet]
      apply lintegral_congr
      intro x
      by_cases hx : x∈preferredLinearRightShell d B δB r l i j
      · have hx' : constrainedAtTotal c x∈preferredFullRightShell d B δB r i j := hx
        rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx']
      · have hx' : constrainedAtTotal c x∉preferredFullRightShell d B δB r i j := hx
        rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx']
    _ ≤ _ := by simpa only [preferredShellScale,preferredShellMean] using hh

end
end IsingBulk.Preferred22
