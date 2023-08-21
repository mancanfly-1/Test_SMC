import z3
from libirpy import util
import datatype.datatypes as dt

# only a invariant, counter >= 0 && counter < dt.MAX_UNIT
def impl_invariants_py(ctx):
	conj = []
	conj.append(z3.And(
		util.global_value(ctx, '@counter') >= 0, 
		util.global_value(ctx, '@counter') <= dt.MAX_UINT))
	return conj

