import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticHadamard
import IsingBulk.Anisotropic.NegativeNormalForm.Symmetry
import IsingBulk.Anisotropic.NegativeNormalForm.Vandermonde

/-! Actual analytic coincidence factors of an equivariant analytic map. -/
noncomputable section
open Filter
open scoped Topology
namespace IsingBulk.Anisotropic.NegativeNormalForm

def collisionInsert {n : ℕ} (i j : Fin n) : (Config n × ℂ) →L[ℂ] Config n :=
  ContinuousLinearMap.pi fun k => if k = i then
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ (Config n) ℂ) +
      ContinuousLinearMap.snd ℂ (Config n) ℂ
    else (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ (Config n) ℂ)

@[simp] theorem collisionInsert_apply {n : ℕ} (i j : Fin n) (z : Config n × ℂ) (k : Fin n) :
    collisionInsert i j z k = if k = i then z.1 j + z.2 else z.1 k := by
  by_cases h : k = i <;> simp [collisionInsert,h]

@[simp] theorem collisionInsert_reconstruct {n : ℕ} (i j : Fin n) (v : Config n) :
    collisionInsert i j (v,v i-v j) = v := by
  ext k
  by_cases h : k = i <;> simp [h]

 theorem collisionInsert_coincidence {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : Config n) :
    collisionInsert i j (v,0) i = collisionInsert i j (v,0) j := by
  simp [Ne.symm hij]

def collisionFunction {n : ℕ} (Phi : Config n → Config n) (i j : Fin n)
    (z : Config n × ℂ) : ℂ := Phi (collisionInsert i j z) i - Phi (collisionInsert i j z) j

def coincidenceFactor {n : ℕ} (Phi : Config n → Config n) (i j : Fin n) (v : Config n) : ℂ :=
  coordinateHadamard (collisionFunction Phi i j) (v,v i-v j)

 theorem collisionFunction_analyticAt {n : ℕ} (Phi : Config n → Config n)
    (hPhi : AnalyticAt ℂ Phi 0) (i j : Fin n) :
    AnalyticAt ℂ (collisionFunction Phi i j) 0 := by
  have h := hPhi.comp_of_eq ((collisionInsert i j).analyticAt 0) (map_zero _)
  exact (analyticAt_pi_iff.mp h i).sub (analyticAt_pi_iff.mp h j)

 theorem coincidenceFactor_analyticAt {n : ℕ} (Phi : Config n → Config n)
    (hPhi : AnalyticAt ℂ Phi 0) (i j : Fin n) :
    AnalyticAt ℂ (coincidenceFactor Phi i j) 0 := by
  have harg : AnalyticAt ℂ (fun v : Config n => (v,v i-v j)) 0 :=
    analyticAt_id.prod ((analyticAt_pi_iff.mp analyticAt_id i).sub
      (analyticAt_pi_iff.mp analyticAt_id j))
  exact (coordinateHadamard_analyticAt (collisionFunction_analyticAt Phi hPhi i j)).comp_of_eq
    harg (by simp)

 theorem coincidenceFactor_identity {n : ℕ} (Phi : Config n → Config n)
    (hPhi : AnalyticAt ℂ Phi 0)
    (heq : ∀ (e : Equiv.Perm (Fin n)) v, Phi (permute e v) = permute e (Phi v))
    (i j : Fin n) (hij : i ≠ j) :
    ∀ᶠ v in 𝓝 (0 : Config n), Phi v i - Phi v j = (v i-v j)*coincidenceFactor Phi i j v := by
  have hc : ContinuousAt (fun v : Config n => (v,v i-v j)) 0 := by fun_prop
  have ht : Tendsto (fun v : Config n => (v,v i-v j)) (𝓝 0) (𝓝 0) := by
    convert! hc.tendsto using 1
    simp
    rfl
  filter_upwards [ht.eventually (coordinateHadamard_identity
    (collisionFunction_analyticAt Phi hPhi i j))] with v hv
  have hz : collisionFunction Phi i j (v,0) = 0 := by
    exact sub_eq_zero.mpr (equivariant_coincidence Phi heq _ i j
      (collisionInsert_coincidence i j hij v))
  rw [hz,sub_zero] at hv
  simpa only [collisionFunction,collisionInsert_reconstruct,coincidenceFactor] using hv

 theorem coincidenceFactor_zero {n : ℕ} (Phi : Config n → Config n)
    (hd : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config n)) 0)
    (i j : Fin n) (hij : i ≠ j) : coincidenceFactor Phi i j 0 = 1 := by
  let L : Config n →L[ℂ] ℂ := (ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ) -
    (ContinuousLinearMap.proj j : Config n →L[ℂ] ℂ)
  have hd' : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config n)) (collisionInsert i j 0) := by
    simpa using hd
  have hcomp := hd'.comp (f := fun z => collisionInsert i j z) 0
    ((collisionInsert i j).hasFDerivAt (x := 0))
  have hfun : HasFDerivAt (collisionFunction Phi i j)
      (L.comp ((ContinuousLinearMap.id ℂ (Config n)).comp (collisionInsert i j))) 0 := by
    convert! (L.hasFDerivAt (x := Phi (collisionInsert i j 0))).comp
      (f := fun z => Phi (collisionInsert i j z)) 0 hcomp using 1
  change coordinateHadamard (collisionFunction Phi i j) (0,0-0) = 1
  rw [sub_self,show ((0 : Config n),(0 : ℂ)) = 0 from rfl,coordinateHadamard_zero,hfun.fderiv]
  simp [L,Ne.symm hij]

end IsingBulk.Anisotropic.NegativeNormalForm
