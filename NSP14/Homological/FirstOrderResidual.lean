module
public import NSP14.Homological.FirstOrderAction
public import Mathlib.Data.Fin.Tuple.Basic
@[expose] public section
open scoped Classical
namespace NSP14.Homological
variable (k : Type) [Field k] (r f : ℕ)

noncomputable def complementCoordinates : (Fin (r+f) → k) →ₗ[k] (Fin f → k) where
  toFun a i := a (Fin.natAdd r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def firstOrderDropPrefix : FirstOrderRing k r f →ₐ[k] TrivSqZeroExt k (Fin f → k) :=
  TrivSqZeroExt.map (complementCoordinates k r f)

theorem complementCoordinates_single_prefix (v : Fin r) :
    complementCoordinates k r f (Pi.single (Fin.castAdd f v) (1:k))=0 := by
  funext i
  have hn : Fin.natAdd r i ≠ Fin.castAdd f v := by
    intro h
    have he := congrArg (fun a : Fin (r+f) => a.val) h
    have hv := v.isLt
    change r+i.val=v.val at he
    omega
  change (Pi.single (Fin.castAdd f v) (1:k) : Fin (r+f) → k) (Fin.natAdd r i)=0
  simp [hn]

theorem complementCoordinates_single_complement (v : Fin f) :
    complementCoordinates k r f (Pi.single (Fin.natAdd r v) (1:k))=Pi.single v 1 := by
  funext i
  change (Pi.single (Fin.natAdd r v) (1:k) : Fin (r+f) → k) (Fin.natAdd r i)=(Pi.single v (1:k) : Fin f → k) i
  simp [Pi.single_apply]

theorem firstOrderDropPrefix_lambda (v : Fin r) :
    firstOrderDropPrefix k r f (TrivSqZeroExt.inr (Pi.single (Fin.castAdd f v) (1:k)))=0 := by
  rw [firstOrderDropPrefix,TrivSqZeroExt.map_inr,complementCoordinates_single_prefix]
  exact TrivSqZeroExt.inr_zero k

theorem firstOrderDropPrefix_complement (v : Fin f) :
    firstOrderDropPrefix k r f (TrivSqZeroExt.inr (Pi.single (Fin.natAdd r v) (1:k)))=
      TrivSqZeroExt.inr (Pi.single v (1:k)) := by
  rw [firstOrderDropPrefix,TrivSqZeroExt.map_inr,complementCoordinates_single_complement]

theorem firstOrderDropPrefix_surjective : Function.Surjective (firstOrderDropPrefix k r f) := by
  intro a
  refine ⟨(a.fst,Fin.append 0 a.snd),?_⟩
  apply TrivSqZeroExt.ext
  · exact TrivSqZeroExt.fst_map _ _
  · change (TrivSqZeroExt.map (complementCoordinates k r f) (a.fst,Fin.append 0 a.snd)).snd=a.snd
    erw [TrivSqZeroExt.snd_map]
    change complementCoordinates k r f (Fin.append 0 a.snd)=a.snd
    funext i
    exact Fin.append_right _ _ i
end NSP14.Homological
