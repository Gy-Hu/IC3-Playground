# state transition system
from pysmt.shortcuts import Symbol

class TransitionSystem(object):
    """Trivial representation of a Transition System."""
    def __init__(self, variables, prime_variables, init, trans):
        self.variables = variables
        self.prime_variables = prime_variables


        self.init = init
        self.trans = trans # T ->  # a formula or list (will need a final conversion)

        # var -> assign_list
        self.state_var = set()
        self.input_var = set()
        self.output_var = set()
        self.wires = set()

    @classmethod
    def get_prime(cls, v):
        """Returns the 'next' of the given variable"""
        return Symbol("%s_prime" % v.symbol_name(), v.symbol_type())

    def add_func_trans(self, trans):
        self.trans = trans

    def set_init(self, initexpr):
        self.init = initexpr 

    def add_output_var(self, v):
        self.output_var.add(v)
    def add_input_var(self, v):
        self.input_var.add(v)
    def add_state_var(self, v):
        self.state_var.add(v)
    def add_wire(self,v):
        self.wires.add(v)

    def finish_adding(self):
        self.variables = self.output_var.union(self.input_var.union(self.state_var))
        self.prime_variables = [TransitionSystem.get_prime(v) for v in self.variables]

