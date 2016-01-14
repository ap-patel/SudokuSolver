#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one remaining variable)
        we look for unary constraints of the csp (constraints whose scope contains
        only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constraints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
         
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
    pruned_values = [] #water if pruned val has to be globel var
    if csp == None:
        print("csp is None")
        return
    if newVar== None:
        one_unasgn = []
        if len(csp.get_all_cons()) == 0:
            return True,pruned_values
        for cons in csp.get_all_cons():
            if cons.get_n_unasgn() == 1:
                one_unasgn.append(cons)
        for i in one_unasgn:
            unknown_var = i.get_unasgn_vars()[0]
            status = FCCHeck_unary(i, unknown_var, pruned_values)
            pruned_values = list(set(pruned_values)) #getting rid of duplicates
            if status == False:
                return False,pruned_values #not sure if return false should be ehre to at the end
        return True,pruned_values
    else: #case where newVar != None
       # pruned_values = []
        unasgn_with_v = []
        if len(csp.get_cons_with_var(newVar)) == 0:
            return True,pruned_values
        for i in csp.get_cons_with_var(newVar):
            unasgn_with_v.append(i)
        unasgn_V_with_1unkwn = []
        for i in unasgn_with_v:
            if i.get_n_unasgn() == 1:
                unasgn_V_with_1unkwn.append(i)
        for i in unasgn_V_with_1unkwn:
            status = FCCHeck_unary(i, i.get_unasgn_vars()[0],pruned_values)
            pruned_values = list(set(pruned_values))
            if status == False:
                return False,pruned_values
        return True,pruned_values
            

def FCCHeck_unary(cons, var, pruned_values):
    unary = False
    if cons.get_scope() == 1:
        unary = True
    for d in var.cur_domain():
        if unary:
            #case where you dont need all prev values
            if not cons.check([d]):
                var.prune_value(d)
                pruned_values.append((var, d))
        elif unary == False:
            cons_scope = cons.get_scope()
            temp_list = []
            for i in cons_scope:
                if i.is_assigned():
                    temp_list.append(i.get_assigned_value())
                else:
                    temp_list.append(d)
            if not cons.check(temp_list):
                var.prune_value(d)
                pruned_values.append((var, d))
            #case where we need to keep track of all prev values in order
    if var.cur_domain_size() == 0:
        return False
    return True
        
    

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    pruned_list = []
    if newVar == None:
      #  pruned_list = []
        GACQueue = Queue()
        if len(csp.get_all_cons()) == 0:
            print("\n\n BRUV cSP constrains are empty how?")
        else:
            for cons in csp.get_all_cons():
                GACQueue.enqueue(cons)
        GAC_return = GAC_helper(csp, GACQueue, pruned_list)
        if GAC_return == True:
           # pruned_list = list(set(pruned_list))
            return True,pruned_list
        else:
           # pruned_list = list(set(pruned_list))
            return False,pruned_list
    else:
       # pruned_list = []
        GACQueue = Queue()
        if len(csp.get_cons_with_var(newVar)) == 0:
            print("\n\n\n BREV csp with newVat is empty")
        else:   
            for cons in csp.get_cons_with_var(newVar):
                GACQueue.enqueue(cons)
        GAC_return = GAC_helper(csp, GACQueue, pruned_list)
        if GAC_return == True:
            pruned_list = list(set(pruned_list))
            return True,pruned_list
        else:
            pruned_list = list(set(pruned_list))
            return False,pruned_list
       
            

def GAC_helper(csp, GACQueue, pruned_list):
    while not GACQueue.is_empty():
        C = GACQueue.dequeue()
        for var in C.get_scope():
            for d in var.cur_domain():
                sup = C.has_support(var, d)
                #find an assignment A for all other variables in scope(C)such that 
                #C(A U var = c) = True
                if sup == False:
                    var.prune_value(d)
                    pruned_list.append((var, d))
                    if var.cur_domain_size() == 0:
                        GACQueue.empty()
                        return False #DWO happened here
                    else:
                        constraints_with_var = csp.get_cons_with_var(var)
                        if len(constraints_with_var) == 0:
                            print("\n\n\n\n\There are no cons with var inside GAC helper ")
                            return False  #there aint no constraints with var
                        for i in constraints_with_var:
                            if not GACQueue.contains(i):
                                GACQueue.enqueue(i)
    return True
                        
                    
    


class Queue:
    def __init__ (self):
        self.items = []
        
    def dequeue(self):
        x = None
        if(self.q_len() > 0):
            x = self.items[0]
            self.items = self.items[1:]
        return x
    
    def is_empty(self):
        return len(self.items) == 0
    
    def enqueue(self,item):
        self.items.append(item)
        
    def q_len(self):
        return len(self.items)
    
    def empty(self):
        self.items = []
        
    def contains(self, item):
        if (item in self.items):
            return True
        return False        