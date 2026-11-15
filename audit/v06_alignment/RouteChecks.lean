module
import NSP14.Endpoint.RowPackage
import NSP14.Endpoint.SocleBounds
import NSP14.Endpoint.FiniteSocleBounds
import NSP14.Width.Closure
import NSP14.Width.IntegerPayment
import NSP14.Width.HigherFromSecond
import NSP14.Width.DenseComparison
import Lean

/- Named-root reachability complements scripts/check_v06_routes.py.
This fixture is deliberately independent of the umbrella's retained imports. -/
#check NSP14.Endpoint.Data.competitorMin_height
#check NSP14.Endpoint.Data.competitor_zero_column
#check NSP14.Width.antipodal_integer_payment
#check NSP14.Width.nonAntipodal_integer_payment
#check NSP14.Width.higher_capacity_from_second
#check NSP14.Endpoint.Data.actual_higher_from_second
#check NSP14.Endpoint.Data.actual_antipodal_first
#check NSP14.Endpoint.Data.actual_five_nonAntipodal_first
#check NSP14.Endpoint.Data.actual_five_higher
#check NSP14.Endpoint.Data.actual_sparse_higher
#check NSP14.Endpoint.Data.dense_core_lex_bound_two_branch
#check NSP14.Width.dense_coeff_ge_three
#check NSP14.Width.dense_payment_ge_three
#check NSP14.Endpoint.Data.actual_dense_firstterm
#check NSP14.NumericalSemigroup.narrow_width_comparison
