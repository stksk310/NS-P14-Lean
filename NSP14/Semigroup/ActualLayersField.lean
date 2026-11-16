module
public import NSP14.Semigroup.ActualLayers
public import NSP14.Semigroup.TowerIntervals
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k L : Type*) [Field k] [Field L]

/-- The actual H comes from coordinate counts. This transports that same
resource row; it does not select another cut or another good bound. -/
theorem actualLayers_field_independent : S.actualLayers k=S.actualLayers L := by
  unfold actualLayers
  congr 1
  · exact_mod_cast S.towerResource_field_independent k L 1
  · funext j
    exact_mod_cast S.towerResource_field_independent k L (j+2)
end NSP14.NumericalSemigroup
