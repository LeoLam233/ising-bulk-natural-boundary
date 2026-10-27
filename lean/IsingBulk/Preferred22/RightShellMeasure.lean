import IsingBulk.Preferred22.ConstrainedMeasure

/-! The actual right support avoids every independent angular seam. Thus
there is one affine constrained-mean chart per integer mean, with no extra
component multiplicity and no unproved change of measure. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem preferred_right_interval_original (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) :
    Icc (-d.b-δB) B.delta ⊆ Ioc (-Real.pi) Real.pi := by
  intro u hu
  constructor <;> linarith [hu.1,hu.2,B.branch_plateau,B.delta_alpha,d.alpha_lt,Real.pi_pos]

theorem preferred_right_interval_oneSided (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) :
    Icc (-d.b-δB) B.delta ⊆ Ioc (-Real.pi-B.delta) (-Real.pi-B.delta+2*Real.pi) := by
  intro u hu
  have hh := preferred_right_interval_original d B hδB hu
  constructor <;> linarith [hh.1,hu.2,B.delta_pos,B.delta_alpha,d.alpha_lt,Real.pi_pos]

theorem preferred_lift_free_eq_of_right {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (θ : Fin n → ℝ) (hθ : θ∈angularBox n)
    (hw : ∀ v,preferredLiftedAngles B.delta (constrainedAngles θ) v∈Icc (-d.b-δB) B.delta)
    (i : Fin n) : preferredLiftedAngles B.delta (constrainedAngles θ) i.castSucc=θ i := by
  let hp : 0<2*Real.pi := Real.two_pi_pos
  have hθi : θ i∈Ioc (-Real.pi) (-Real.pi+2*Real.pi) := by
    have hh := hθ i (Set.mem_univ i)
    simpa only [show -Real.pi+2*Real.pi=Real.pi by ring] using hh
  have hwi : preferredLiftedAngles B.delta (constrainedAngles θ) i.castSucc∈
      Ioc (-Real.pi) (-Real.pi+2*Real.pi) := by
    have hh := preferred_right_interval_original d B hδB (hw i.castSucc)
    simpa only [show -Real.pi+2*Real.pi=Real.pi by ring] using hh
  calc
    _ = toIocMod hp (-Real.pi) (preferredLiftedAngles B.delta (constrainedAngles θ) i.castSucc) :=
      ((toIocMod_eq_self hp).mpr hwi).symm
    _ = toIocMod hp (-Real.pi) (θ i) := by
      simp only [preferredLiftedAngles,constrainedAngles,Fin.snoc_castSucc,toIocMod_toIocMod]
    _ = θ i := (toIocMod_eq_self hp).mpr hθi

theorem preferred_lift_eq_affine_on_right {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB c : ℝ} (hδB : δB<B.delta) (θ : Fin n → ℝ) (hθ : θ∈angularBox n)
    (hw : ∀ v,preferredLiftedAngles B.delta (constrainedAngles θ) v∈Icc (-d.b-δB) B.delta)
    (hsum : (∑ v,preferredLiftedAngles B.delta (constrainedAngles θ) v)=c) :
    preferredLiftedAngles B.delta (constrainedAngles θ)=constrainedAtTotal c θ := by
  have hf := preferred_lift_free_eq_of_right d B hδB θ hθ hw
  rw [Fin.sum_univ_castSucc] at hsum
  simp_rw [hf] at hsum
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAtTotal,Fin.snoc_last]
    linarith
  · simpa only [constrainedAtTotal,Fin.snoc_castSucc] using hf j

theorem preferred_lift_eq_affine_from_right {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (l : ℤ) (θ : Fin n → ℝ)
    (hw : ∀ v,constrainedAtTotal (2*Real.pi*(l:ℝ)) θ v∈Icc (-d.b-δB) B.delta) :
    θ∈angularBox n ∧ preferredLiftedAngles B.delta (constrainedAngles θ)=
      constrainedAtTotal (2*Real.pi*(l:ℝ)) θ := by
  let hp : 0<2*Real.pi := Real.two_pi_pos
  have hrep (v : Fin (n+1)) :
      toIocMod hp (-Real.pi-B.delta) (constrainedAtTotal (2*Real.pi*(l:ℝ)) θ v)=
        constrainedAtTotal (2*Real.pi*(l:ℝ)) θ v :=
    (toIocMod_eq_self hp).mpr (preferred_right_interval_oneSided d B hδB (hw v))
  constructor
  · intro i _
    simpa only [constrainedAtTotal,Fin.snoc_castSucc] using
      preferred_right_interval_original d B hδB (hw i.castSucc)
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hh := hrep (Fin.last n)
      simp only [constrainedAtTotal,Fin.snoc_last] at hh
      have he : 2*Real.pi*(l:ℝ)-(∑ j,θ j)=-(∑ j,θ j)+l • (2*Real.pi) := by
        rw [zsmul_eq_mul]
        ring
      rw [he,toIocMod_add_zsmul] at hh
      simpa only [preferredLiftedAngles,constrainedAngles,constrainedAtTotal,Fin.snoc_last,he] using hh
    · simpa only [preferredLiftedAngles,constrainedAngles,constrainedAtTotal,Fin.snoc_castSucc]
        using hrep j.castSucc

def preferredLinearRightShell {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB r : ℝ) (l : ℤ) (i j : Fin (n+1)) : Set (Fin n → ℝ) :=
  {θ | let w := constrainedAtTotal (2*Real.pi*(l:ℝ)) θ
    (∀ v,w v∈Icc (-d.b-δB) B.delta) ∧
    (∀ v,w i≤w v ∧ w v≤w j) ∧ r≤w j-w i ∧ w j-w i≤2*r}

/-- Exact equality, not an estimate or an assumed periodic cell split. -/
theorem preferredRightShell_eq_linear {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (r : ℝ) (l : ℤ) (i j : Fin (n+1)) :
    preferredRightShell d B δB r l i j=preferredLinearRightShell d B δB r l i j := by
  ext θ
  constructor
  · rintro ⟨hθ,hw,hsum,hext,hlo,hhi⟩
    have he := preferred_lift_eq_affine_on_right d B hδB θ hθ hw hsum
    change (∀ v,_∈_) ∧ (∀ v,_≤_ ∧ _≤_) ∧ _≤_ ∧ _≤_
    simpa only [he] using And.intro hw (And.intro hext (And.intro hlo hhi))
  · rintro ⟨hw,hext,hlo,hhi⟩
    obtain ⟨hθ,he⟩ := preferred_lift_eq_affine_from_right d B hδB l θ hw
    refine ⟨hθ,?_,?_,?_,?_,?_⟩
    · simpa only [he] using hw
    · simpa only [he] using constrainedAtTotal_sum (2*Real.pi*(l:ℝ)) θ
    · simpa only [he] using hext
    · simpa only [he] using hlo
    · simpa only [he] using hhi

theorem preferredLinearRightShell_isClosed {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB r : ℝ) (l : ℤ) (i j : Fin (n+1)) :
    IsClosed (preferredLinearRightShell d B δB r l i j) := by
  let w : (Fin n → ℝ) → Fin (n+1) → ℝ := constrainedAtTotal (2*Real.pi*(l:ℝ))
  have hc : Continuous w := by unfold w constrainedAtTotal; fun_prop
  have hi (a : Fin (n+1)) : Continuous (fun θ : Fin n → ℝ => w θ a) :=
    (continuous_apply a).comp hc
  have h₁ : IsClosed {θ : Fin n → ℝ | ∀ v,w θ v∈Icc (-d.b-δB) B.delta} := by
    have he : {θ : Fin n → ℝ | ∀ v,w θ v∈Icc (-d.b-δB) B.delta}=
        ⋂ v : Fin (n+1),{θ : Fin n → ℝ | w θ v∈Icc (-d.b-δB) B.delta} := by ext θ; simp
    rw [he]
    exact isClosed_iInter (fun v => isClosed_Icc.preimage (hi v))
  have h₂ : IsClosed {θ : Fin n → ℝ | ∀ v,w θ i≤w θ v ∧ w θ v≤w θ j} := by
    have he : {θ : Fin n → ℝ | ∀ v,w θ i≤w θ v ∧ w θ v≤w θ j}=
        ⋂ v : Fin (n+1),{θ : Fin n → ℝ | w θ i≤w θ v ∧ w θ v≤w θ j} := by ext θ; simp
    rw [he]
    exact isClosed_iInter (fun v => (isClosed_le (hi i) (hi v)).inter (isClosed_le (hi v) (hi j)))
  exact h₁.inter (h₂.inter ((isClosed_le continuous_const ((hi j).sub (hi i))).inter
    (isClosed_le ((hi j).sub (hi i)) continuous_const)))

theorem preferredRightShellMass_eq_linear {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (τ : ℝ) (η rcut : ℝ → ℝ) (k : ℕ)
    (ε r : ℝ) (l : ℤ) (i j : Fin (n+1)) :
    preferredRightShellMass d B δB τ η rcut k ε r l i j =
      ∫ θ in preferredLinearRightShell d B δB r l i j,
        ‖preferredTransportedDensity .right τ η B.p B.m rcut k
          (IsingBulk.Branch.radialParameter d.alpha ε) (constrainedAtTotal (2*Real.pi*(l:ℝ)) θ)‖ := by
  unfold preferredRightShellMass
  rw [preferredRightShell_eq_linear d B hδB]
  apply setIntegral_congr_fun (preferredLinearRightShell_isClosed d B δB r l i j).measurableSet
  intro θ hθ
  dsimp only
  rw [(preferred_lift_eq_affine_from_right d B hδB l θ hθ.1).2]

end
end IsingBulk.Preferred22
