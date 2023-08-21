import sys
import argparse
import copy
import unittest
import inspect

import libirpy
import libirpy.util as util
import libirpy.solver as solver
import libirpy.ex as ex
import libirpy.itypes as itypes
from libirpy.datatypes import BitcastPointer

import TIPC

#import syscall_spec
import datatype.datatypes as dt
import z3
import specs as spec
import invariants as inv
Solver = solver.Solver
INTERACTIVE = False
class BaseTest(unittest.TestCase):
    def _prove(self, cond, pre=None, return_model=False, minimize=True):
        if minimize:
            self.solver.push()
        self.solver.add(z3.Not(cond))

        res = self.solver.check()
        if res != z3.unsat:
            if not minimize and not return_model:
                self.assertEquals(res, z3.unsat)

            model = self.solver.model()
            if return_model:
                return model

            print "Could not prove, trying to find a minimal ce"
            assert res != z3.unknown
            if z3.is_and(cond):
                self.solver.pop()
                # Condition is a conjunction of some child clauses.
                # See if we can find something smaller that is sat.

                if pre is not None:
                    ccond = sorted(
                        zip(cond.children(), pre.children()), key=lambda x: len(str(x[0])))
                else:
                    ccond = sorted(cond.children(), key=lambda x: len(str(x)))

                for i in ccond:
                    self.solver.push()
                    if isinstance(i, tuple):
                        self._prove(i[0], pre=i[1])
                    else:
                        self._prove(i)
                    self.solver.pop()

            print "Can not minimize condition further"
            if pre is not None:
                print "Precondition"
                print pre
                print "does not imply"
            print cond
            self.assertEquals(model, [])

def newctx():
    ctx = libirpy.newctx()
    # If we don't need the values of any constants we don't have to
    # initialize them, slightly faster execution time.
    ctx.eval.declare_global_constant = ctx.eval.declare_global_variable
    libirpy.initctx(ctx, TIPC)
    ctx.ptr_to_int[ctx.globals['@port_table']._ref._name] = util.FreshBitVec( '(uintptr)@port_table', 64)
    return ctx

class DetailTest(BaseTest):
    def setUp(self):
		# init LLVM IR context. 
        self.ctx = newctx()
		#define counter machine state of ourself
        self.state = dt.IPCState()
		# instance z3 solver.
        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)
		# current ctx state and machine state is equal?		
        self._pre_state = spec.state_equiv(self.ctx, self.state)

		# we should add our invariants to context.
		#self.ctx.add_assumption(inv.impl_invariants_py(self.ctx))
		
		# take the condition pre state equal to solver.
        self.solver.add(self._pre_state)
    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver
    # '''def test_test1(self):
    # 	print "testOne"'''
    def _general_test(self, call_name, *args):
        print "starting test_{}....".format(call_name)
        res = self.ctx.call('@' + call_name, *args)

        # print(self._pre_state)
        cond, newstate = getattr(spec, call_name)(self.state, *args)
        print(res)
        model = self._prove(z3.And(spec.state_equiv(self.ctx, newstate),
                                   cond == (res == util.i32(0))),
                            pre=z3.And(self._pre_state, z3.BoolVal(True)),
                            return_model=INTERACTIVE)

    def test_chan_init(self):
        chan_id = util.FreshBitVec('chan_id',dt.uint64_t)
        flags = util.FreshBitVec('flags',dt.uint64_t)
        uuid =util.FreshBitVec('uuid',dt.uint64_t)
        args = (chan_id, flags, uuid)
        self._general_test('chan_init', *args)

if __name__ == "__main__":
	#t = child()
	#print t['a'][1]
	unittest.main()


