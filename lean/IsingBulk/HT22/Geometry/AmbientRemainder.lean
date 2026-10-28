import IsingBulk.HT22.Geometry.SignedShellCover
import IsingBulk.Preferred22.LiftedTransportCalculus

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology BigOperators ContDiff

theorem actualCellWeight_right_support (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {N : ℕ} {δB : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (θ : Fin N → ℝ)
    (hθ : ∀i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hw : preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut θ≠0) :
    ∀i,θ i∈Icc (-d.b-δB) B.delta := by
  classical
  intro i
  constructor
  · by_contra hn
    have hlo : θ i< -d.b-δB := lt_of_not_ge hn
    have hi : θ i∈Icc (-Real.pi-B.delta) B.delta :=
      ⟨(hθ i).1.le,by linarith [d.b_pos,B.delta_pos,hcut.1]⟩
    have hz := (hcut.2.2.2.2.2 (θ i) hi).1 (by linarith)
    have hp : (∏v,rcut (θ v))=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact hw (by simp only [preferredCellWeight,preferredRightWeight,hp,mul_zero])
  · by_contra hn
    have hp : B.p (θ i)=1 := B.plateau (θ i) ⟨(lt_of_not_ge hn).le,(hθ i).2⟩
    have hP : 1/2≤occupancy B.p θ := by
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun v _ => B.lower_bound (θ v)) (Finset.mem_univ i)
      rw [hp] at hh
      exact (by norm_num : (1/2:ℝ)≤1).trans hh
    exact hw (by simp only [preferredCellWeight,preferredLowerWeight,lowerWeight,
      preferredPopulationCutoff_one hP,sub_self,zero_mul,zero_div])

def ambientRemainder {n : ℕ} (rem : (Fin n → ℝ) → ℝ) (w : Fin (n+1) → ℝ) : ℝ :=
  rem (fun i => w i.castSucc)

theorem ambientRemainder_contDiff {n : ℕ} (rem : (Fin n → ℝ) → ℝ)
    (hrem : ContDiff ℝ ∞ rem) : ContDiff ℝ ∞ (ambientRemainder rem) := by
  exact hrem.comp (by fun_prop)

theorem ambientRemainder_lift_eq {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδB : δB<B.delta) (a : ℝ) (θ : Fin n → ℝ)
    (hθ : θ∈signedRightRegion a d B δB) (rem : (Fin n → ℝ) → ℝ) :
    ambientRemainder rem (preferredLiftedAngles B.delta (constrainedAtTotal a θ))=rem θ := by
  unfold ambientRemainder
  congr 1
  funext i
  exact signed_lift_free_eq_of_right d B hδB a θ hθ.1 hθ.2 i

/-- A genuine open zero germ of the partition lifts to ambient angular
space, so every derivative of the inserted seed cutoff vanishes there. -/
theorem ambientRemainder_zero_germ {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB a r : ℝ} (hδB : δB<B.delta) (rem : (Fin n → ℝ) → ℝ)
    (hrem : ∀ θ∈signedRightRegion a d B δB,
      preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal a θ))<r →
      rem =ᶠ[𝓝 θ] (fun _ => 0))
    (w : Fin (n+1) → ℝ) (hw : ∀ i,w i∈Icc (-d.b-δB) B.delta)
    (l : ℤ) (hs : (∑ i,w i)=a+2*Real.pi*(l:ℝ))
    (hD : preferredAngularDiameter w<r) :
    ambientRemainder rem =ᶠ[𝓝 w] (fun _ => 0) := by
  let θ : Fin n → ℝ := fun i => w i.castSucc
  have he : constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ=w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.sum_univ_castSucc] at hs
      simp only [constrainedAtTotal,Fin.snoc_last,θ]
      linarith
    · simp only [constrainedAtTotal,Fin.snoc_castSucc,θ]
  obtain ⟨hθ,hlift⟩ := signed_lift_eq_affine_from_right d B hδB l a θ (by simpa only [he] using hw)
  rw [he] at hlift
  have hg := hrem θ ⟨hθ,by simpa only [hlift] using hw⟩ (by simpa only [hlift] using hD)
  exact (show ContinuousAt (fun z : Fin (n+1) → ℝ => fun i : Fin n => z i.castSucc) w by
    exact (continuous_pi (fun i => continuous_apply i.castSucc)).continuousAt).tendsto.eventually hg

/-- Exact weighted compatibility on the entire original angular box,
including modular seams; no periodicity of the remainder is assumed. -/
theorem ambientRemainder_weighted_lift_eq {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (a : ℝ) (θ : Fin n → ℝ)
    (hθ : θ∈angularBox n) (rem : (Fin n → ℝ) → ℝ) :
    let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
    ambientRemainder rem w * preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w =
      rem θ * preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w := by
  dsimp only
  by_cases hz : preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ))=0
  · simp only [hz,mul_zero]
  · rw [ambientRemainder_lift_eq d B hcut.2.1 a θ ⟨hθ,?_⟩ rem]
    exact actualCellWeight_right_support d B rcut hcut _
      (preferredLiftedAngles_mem_oneSided B.delta _) hz

end
end IsingBulk.HT22.Geometry
