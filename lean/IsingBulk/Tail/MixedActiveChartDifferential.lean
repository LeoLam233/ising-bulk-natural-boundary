import IsingBulk.Tail.MixedActiveSourceGerm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def mixedDisplacementParameterColumn {N : ℕ} (J : Finset (Fin N)) (τ : Fin N → ℂ) : MixedActiveSpace N :=
  (1,((fun i => if i∈J then τ i else 0),0))

def mixedDisplacementAngularColumn {N : ℕ} (J : Finset (Fin N)) (q k : Fin N)
    (b : Fin N → ℂ) : MixedActiveSpace N :=
  (0,((fun i => if i∈J then if i=k then b i else 0 else 0),if q=k then 1 else 0))

theorem mixedContourPhase_plateau_hasDerivAt {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ a,DifferentiableAt ℝ f.p (θ a)) (hm : ∀ a,DifferentiableAt ℝ f.m (θ a))
    (hpk : deriv f.p (θ k)=0) (hmk : deriv f.m (θ k)=0)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasDerivAt (fun u => mixedContourPhase f r τ lam s (Function.update θ k u) i)
      (if i=k then mixedSourceSlope s (deformedPoint f r τ lam θ i) else 0) (θ k) := by
  have hh := mixedContourPhase_coordinate f hr τ lam s θ k i hp hm hW
  rw [show angularJacobian f τ lam θ i k=if i=k then Complex.I else 0 from
    retractionJacobian_named_column lam τ _ _ _ _ k hpk hmk i] at hh
  convert hh using 1
  by_cases hik : i=k
  · simp only [hik,ite_true,mixedSourceSlope,mixedContourPhase]
    ring
  · simp [hik]

theorem mixedSourceDisplacement_parameter {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (t : ℂ) (x : Fin N → ℝ) (ht : t≠0)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)).im) :
    HasDerivAt (fun z => mixedSourceDisplacement J q f r τ lam s background z x)
      (mixedDisplacementParameterColumn J (fun i => mixedSourceTau t
        (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i))) t := by
  have hφ : HasDerivAt (fun z => fun i => if i∈J then
      mixedContourPhase f r τ lam z (mixedFreeze (insert q J) background x) i-
        mixedContourPhase f r τ lam s background i else 0)
      (fun i => if i∈J then mixedSourceTau t
        (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i) else 0) t := by
    apply hasDerivAt_pi.mpr
    intro i
    by_cases hi : i∈J
    · simpa only [hi,ite_true,mixedContourPhase] using (mixedSourcePhase_parameter ht (hW i hi)).sub_const
        (mixedContourPhase f r τ lam s background i)
    · simp only [hi,ite_false]
      exact hasDerivAt_const t 0
  exact ((hasDerivAt_id t).sub_const s).prodMk (hφ.prodMk (hasDerivAt_const t _))

theorem mixedSourceDisplacement_angular {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (t : ℂ) (x : Fin N → ℝ) (k : Fin N)
    (hp : ∀ a,DifferentiableAt ℝ f.p (mixedFreeze (insert q J) background x a))
    (hm : ∀ a,DifferentiableAt ℝ f.m (mixedFreeze (insert q J) background x a))
    (hplateau : ∀ a∈insert q J,deriv f.p (mixedFreeze (insert q J) background x a)=0 ∧
      deriv f.m (mixedFreeze (insert q J) background x a)=0)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)).im) :
    HasDerivAt (fun u => mixedSourceDisplacement J q f r τ lam s background t (Function.update x k u))
      (mixedDisplacementAngularColumn J q k (fun i => mixedSourceSlope t
        (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i))) (x k) := by
  let θ := mixedFreeze (insert q J) background x
  have hφ : HasDerivAt (fun u => fun i => if i∈J then
      mixedContourPhase f r τ lam t (mixedFreeze (insert q J) background (Function.update x k u)) i-
        mixedContourPhase f r τ lam s background i else 0)
      (fun i => if i∈J then if i=k then mixedSourceSlope t (deformedPoint f r τ lam θ i) else 0 else 0) (x k) := by
    apply hasDerivAt_pi.mpr
    intro i
    by_cases hi : i∈J
    · simp only [hi,ite_true]
      by_cases hk : k∈insert q J
      · have hh := (mixedContourPhase_plateau_hasDerivAt f hr τ lam t θ k i hp hm
          (hplateau k hk).1 (hplateau k hk).2 (hW i hi)).sub_const (mixedContourPhase f r τ lam s background i)
        have hθk : θ k=x k := by simp [θ,mixedFreeze,hk]
        simpa only [mixedFreeze_update_active _ _ _ k hk,hθk] using hh
      · have hik : i≠k := by intro he; subst k; exact hk (Finset.mem_insert_of_mem hi)
        simp only [mixedFreeze_update_inactive _ _ _ k hk,hik,ite_false]
        exact hasDerivAt_const _ _
    · simp only [hi,ite_false]
      exact hasDerivAt_const _ _
  have hq : HasDerivAt (fun u =>
      (mixedFreeze (insert q J) background (Function.update x k u) q:ℂ)-(background q:ℂ))
      (if q=k then 1 else 0) (x k) := by
    simp only [mixedFreeze,Finset.mem_insert_self,ite_true]
    by_cases hqk : q=k
    · subst k
      simp only [Function.update_self,ite_true]
      exact Complex.ofRealCLM.hasDerivAt.sub_const _
    · simp only [Function.update_of_ne hqk,hqk,ite_false]
      exact hasDerivAt_const _ _
  exact (hasDerivAt_const (x k) (t-s)).prodMk (hφ.prodMk hq)

end
end IsingBulk.Tail
