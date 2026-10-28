import IsingBulk.HT22.Geometry.SignedShellScale
import IsingBulk.Preferred22.ShellCover

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ENNReal

theorem signed_lift_free_eq_of_right {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (a : ℝ) (θ : Fin n → ℝ) (hθ : θ∈angularBox n)
    (hw : ∀ v,preferredLiftedAngles B.delta (constrainedAtTotal a θ) v∈Icc (-d.b-δB) B.delta)
    (i : Fin n) : preferredLiftedAngles B.delta (constrainedAtTotal a θ) i.castSucc=θ i := by
  let hp : 0<2*Real.pi := Real.two_pi_pos
  have hθi : θ i∈Ioc (-Real.pi) (-Real.pi+2*Real.pi) := by
    have hh := hθ i (Set.mem_univ i)
    simpa only [show -Real.pi+2*Real.pi=Real.pi by ring] using hh
  have hwi : preferredLiftedAngles B.delta (constrainedAtTotal a θ) i.castSucc∈
      Ioc (-Real.pi) (-Real.pi+2*Real.pi) := by
    have hh := preferred_right_interval_original d B hδB (hw i.castSucc)
    simpa only [show -Real.pi+2*Real.pi=Real.pi by ring] using hh
  calc
    _ = toIocMod hp (-Real.pi) (preferredLiftedAngles B.delta (constrainedAtTotal a θ) i.castSucc) :=
      ((toIocMod_eq_self hp).mpr hwi).symm
    _ = toIocMod hp (-Real.pi) (θ i) := by
      simp only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_castSucc,toIocMod_toIocMod]
    _ = θ i := (toIocMod_eq_self hp).mpr hθi

theorem signed_lift_eq_affine_on_right {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB c : ℝ} (hδB : δB<B.delta) (a : ℝ) (θ : Fin n → ℝ) (hθ : θ∈angularBox n)
    (hw : ∀ v,preferredLiftedAngles B.delta (constrainedAtTotal a θ) v∈Icc (-d.b-δB) B.delta)
    (hsum : (∑ v,preferredLiftedAngles B.delta (constrainedAtTotal a θ) v)=c) :
    preferredLiftedAngles B.delta (constrainedAtTotal a θ)=constrainedAtTotal c θ := by
  have hf := signed_lift_free_eq_of_right d B hδB a θ hθ hw
  rw [Fin.sum_univ_castSucc] at hsum
  simp_rw [hf] at hsum
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAtTotal,Fin.snoc_last] at hsum ⊢
    linarith
  · simpa only [constrainedAtTotal,Fin.snoc_castSucc] using hf j

theorem signed_lift_eq_affine_from_right {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (l : ℤ) (a : ℝ) (θ : Fin n → ℝ)
    (hw : ∀ v,constrainedAtTotal ((a+2*Real.pi*(l:ℝ))) θ v∈Icc (-d.b-δB) B.delta) :
    θ∈angularBox n ∧ preferredLiftedAngles B.delta (constrainedAtTotal a θ)=
      constrainedAtTotal ((a+2*Real.pi*(l:ℝ))) θ := by
  let hp : 0<2*Real.pi := Real.two_pi_pos
  have hrep (v : Fin (n+1)) :
      toIocMod hp (-Real.pi-B.delta) (constrainedAtTotal ((a+2*Real.pi*(l:ℝ))) θ v)=
        constrainedAtTotal ((a+2*Real.pi*(l:ℝ))) θ v :=
    (toIocMod_eq_self hp).mpr (preferred_right_interval_oneSided d B hδB (hw v))
  constructor
  · intro i _
    simpa only [constrainedAtTotal,Fin.snoc_castSucc] using
      preferred_right_interval_original d B hδB (hw i.castSucc)
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hh := hrep (Fin.last n)
      simp only [constrainedAtTotal,Fin.snoc_last] at hh
      have he : (a+2*Real.pi*(l:ℝ))-(∑ j,θ j)=(a-(∑ j,θ j))+l • (2*Real.pi) := by
        rw [zsmul_eq_mul]
        ring
      rw [he,toIocMod_add_zsmul] at hh
      simpa only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_last,he] using hh
    · simpa only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_castSucc]
        using hrep j.castSucc


/-- Literal signed torus shell with its actual integer mean. -/
def signedRightShell {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r : ℝ) (l : ℤ) (i j : Fin (n+1)) : Set (Fin n → ℝ) :=
  {θ | θ∈angularBox n ∧
    preferredLiftedAngles B.delta (constrainedAtTotal a θ) ∈ preferredFullRightShell d B δB r i j ∧
    (∑ v,preferredLiftedAngles B.delta (constrainedAtTotal a θ) v)=a+2*Real.pi*(l:ℝ)}

theorem signedRightShell_eq_affine {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (r : ℝ) (l : ℤ) (i j : Fin (n+1)) :
    signedRightShell a d B δB r l i j =
      (constrainedAtTotal (a+2*Real.pi*(l:ℝ))) ⁻¹' preferredFullRightShell d B δB r i j := by
  ext θ
  constructor
  · rintro ⟨hθ,hw,hs⟩
    have he := signed_lift_eq_affine_on_right d B hδB a θ hθ hw.1 hs
    simpa only [Set.mem_preimage,he] using hw
  · intro hw
    change constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ ∈ preferredFullRightShell d B δB r i j at hw
    obtain ⟨hθ,he⟩ := signed_lift_eq_affine_from_right d B hδB l a θ hw.1
    refine ⟨hθ,?_,?_⟩
    · simpa only [he] using hw
    · simpa only [he] using constrainedAtTotal_sum (a+2*Real.pi*(l:ℝ)) θ

theorem signedRightShell_isClosed {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (r : ℝ) (l : ℤ) (i j : Fin (n+1)) : IsClosed (signedRightShell a d B δB r l i j) := by
  rw [signedRightShell_eq_affine a d B hδB]
  apply (preferredFullRightShell_isClosed d B δB r i j).preimage
  unfold constrainedAtTotal
  fun_prop

/-- The affine signed constraint shifts the sum, not the lattice spacing. -/
theorem signedLiftedAngles_integer_mean {n : ℕ} (δ a : ℝ) (θ : Fin n → ℝ) :
    ∃ l : ℤ,(∑ i,preferredLiftedAngles δ (constrainedAtTotal a θ) i)=a+2*Real.pi*(l:ℝ) := by
  let k : Fin (n+1) → ℤ := fun i =>
    toIocDiv (by positivity : 0<2*Real.pi) (-Real.pi-δ) (constrainedAtTotal a θ i)
  refine ⟨-∑ i,k i,?_⟩
  simp only [preferredLiftedAngles,toIocMod,Finset.sum_sub_distrib,zsmul_eq_mul]
  rw [constrainedAtTotal_sum]
  simp only [Int.cast_neg,Int.cast_sum]
  dsimp [k]
  rw [← Finset.sum_mul]
  ring

end
end IsingBulk.HT22.Geometry
