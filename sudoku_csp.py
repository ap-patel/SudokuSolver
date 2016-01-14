#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return sudoku CSP models.
'''

from cspbase import *
import itertools


DIM_OF_BOARD = 9
def sudoku_csp_model_1(initial_sudoku_board):
    '''Return a CSP object representing a sudoku CSP problem along 
       with an array of variables for the problem. That is return

       sudoku_csp, variable_array

       where sudoku_csp is a csp representing sudoku using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the sudokup board (indexed from (0,0) to (8,8))

       
       
       The input board is specified as a list of 9 lists. Each of the
       9 lists represents a row of the board. If a 0 is in the list it
       represents an empty cell. Otherwise if a number between 1--9 is
       in the list then this represents a pre-set board
       position. E.g., the board
    
       -------------------  
       | | |2| |9| | |6| |
       | |4| | | |1| | |8|
       | |7| |4|2| | | |3|
       |5| | | | | |3| | |
       | | |1| |6| |5| | |
       | | |3| | | | | |6|
       |1| | | |5|7| |4| |
       |6| | |9| | | |2| |
       | |2| | |8| |1| | |
       -------------------
       would be represented by the list of lists
       
       [[0,0,2,0,9,0,0,6,0],
       [0,4,0,0,0,1,0,0,8],
       [0,7,0,4,2,0,0,0,3],
       [5,0,0,0,0,0,3,0,0],
       [0,0,1,0,6,0,5,0,0],
       [0,0,3,0,0,0,0,0,6],
       [1,0,0,0,5,7,0,4,0],
       [6,0,0,9,0,0,0,2,0],
       [0,2,0,0,8,0,1,0,0]]
       
       
       This routine returns Model_1 which consists of a variable for
       each cell of the board, with domain equal to {1-9} if the board
       has a 0 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.
       
       Model_1 also contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.), then invoke enforce_gac on those
       constraints. All of the constraints of Model_1 MUST BE binary
       constraints (i.e., constraints whose scope includes two and
       only two variables).
    '''
    
    #creating a list of Object Variables
    Variables = []
    for i in range(9):
        Variables.append([None]*9)
    #now Variables is a nested list of None 
    for row_num in range(9):
        for column_num in range(9):
            current_value = initial_sudoku_board[row_num][column_num]
            if current_value == 0: #meaning its unassigned
                new_var = Variable("Cell" + "["+str(row_num) + ","+ str(column_num) + "]", range(1,10))
                Variables[row_num][column_num] = new_var
            else: #meaning cell's value is fixed
                fixed_val_var = Variable("Cell" + "["+str(row_num) + ","+ str(column_num) + "]", [current_value])
                Variables[row_num][column_num] = fixed_val_var
    #Variables done
    
    #CSP start
    all_var = []
    for i in Variables:
        for j in i:
            all_var.append(j)
    sudoku_csp = CSP("9X9 Sudoku",all_var)
    #now need to add constraints
    Constraints = []
    
    #lets do subsquare constraints first
    for i in range(9):
        ith_subsquare = get_ith_subsquare(Variables, i)
        for presuccessor in range(9):
            for successor in range(presuccessor + 1, 9):
                presuccessor_variable = ith_subsquare[presuccessor]
                successor_variable = ith_subsquare[successor]
                constraint = Constraint("Cons " + presuccessor_variable.name+","+ successor_variable.name, [presuccessor_variable, successor_variable])
                sat_tuples = []
                for value1 in presuccessor_variable.cur_domain():
                    for value2 in successor_variable.cur_domain():
                        if value1 != value2:
                            sat_tuples.append((value1, value2))
                constraint.add_satisfying_tuples(sat_tuples)
                Constraints.append(constraint)
    #lets do row constraints next
       
    for i in range(9):
        ith_row = Variables[i]
        for presuccessor in range(9):
            for successor in range(presuccessor+1, 9):
                presuccessor_variable = ith_row[presuccessor]
                successor_variable = ith_row[successor] 
                constraint = Constraint("Cons " + presuccessor_variable.name+","+ successor_variable.name, [presuccessor_variable, successor_variable])
                sat_tuples = []
                for value1 in presuccessor_variable.cur_domain():
                    for value2 in successor_variable.cur_domain():
                        if value1 != value2:
                            sat_tuples.append((value1, value2))                
                constraint.add_satisfying_tuples(sat_tuples)
                Constraints.append(constraint)                 
                
    
    #colum constraints next
   
    for i in range(9):
        ith_column = []
        for rows in range(9):
            ith_column.append(Variables[rows][i])
        for presuccessor in range(9):
            for successor in range(presuccessor+1, 9):        
                presuccessor_variable = ith_column[presuccessor]
                successor_variable = ith_column[successor]                 
                constraint = Constraint("Cons " + presuccessor_variable.name+","+ successor_variable.name, [presuccessor_variable, successor_variable])
                sat_tuples = []
                for value1 in presuccessor_variable.cur_domain():
                    for value2 in successor_variable.cur_domain():
                        if value1 != value2:
                            sat_tuples.append((value1, value2))                
                constraint.add_satisfying_tuples(sat_tuples)
                Constraints.append(constraint)
    if len(Constraints) == 0:
        sudoku_csp.add_constraint([None])
    else:
        for i in Constraints:
            sudoku_csp.add_constraint(i)  #might have to loop over constraints and add them juan by juan
    return sudoku_csp,Variables
    
#IMPLEMENT


def get_ith_subsquare(variables, i):
    subsquare_values_to_return = [None]*9
    col_num = (i%3)*3
    row_num = (i//3)*3
    for i in range(9):
        row_i = i//3
        col_i = i%3
        subsquare_values_to_return[i] = variables[row_num + row_i][col_num + col_i]
    return subsquare_values_to_return

def compute_new_dom(dom, x):
    temp = []
    for l in dom:
        if not l in x:
            temp.append(l)
    return temp

##############################
def sudoku_csp_model_2(initial_sudoku_board):
    '''Return a CSP object representing a sudoku CSP problem along 
       with an array of variables for the problem. That is return

       sudoku_csp, variable_array

       where sudoku_csp is a csp representing sudoku using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the sudokup board (indexed from (0,0) to (8,8))

    The input board takes the same input format (a list of 9 lists
    specifying the board as sudoku_csp_model_1.
    
    The variables of model_2 are the same as for model_1: a variable
    for each cell of the board, with domain equal to {1-9} if the
    board has a 0 at that position, and domain equal {i} if the board
    has a fixed number i at that cell.

    However, model_2 has different constraints. In particular, instead
    of binary non-equals constaints model_2 has 27 all-different
    constraints: all-different constraints for the variables in each
    of the 9 rows, 9 columns, and 9 sub-squares. Each of these
    constraints is over 9-variables (some of these variables will have
    a single value in their domain). model_2 should create these
    all-different constraints between the relevant variables, then
    invoke enforce_gac on those constraints.
    '''
    #creating a list of Object Variables
    Variables = []
    for i in range(9):
        Variables.append([None]*9)
    #now Variables is a nested list of None 
    for row_num in range(9):
        for column_num in range(9):
            current_value = initial_sudoku_board[row_num][column_num]
            if current_value == 0: #meaning its unassigned
                new_var = Variable("Cell" + "["+str(row_num) + ","+ str(column_num) + "]", range(1,10))
                Variables[row_num][column_num] = new_var
            else: #meaning cell's value is fixed
                fixed_val_var = Variable("Cell" + "["+str(row_num) + ","+ str(column_num) + "]", [current_value])
                Variables[row_num][column_num] = fixed_val_var
        #Variables done    
   # Constraints = []
    all_var = []
    for i in Variables:
        for j in i:
            all_var.append(j)    
    
    sudoku_csp = CSP("9X9 Sudoku", all_var)
    #for i in all_var:
        #print("\n\n\n" + i.name)
    
    #lets do subsquare constraints first
    for i in range(9):
        ith_subsquare = get_ith_subsquare(Variables, i)
        constraint = Constraint("Cons subsquare_" + str(i), ith_subsquare)
        cur_ith_domain = [] #list of lists [[domain var1], [domain var2],...,[domain varn]]
        
        for var_obj in ith_subsquare:
            cur_ith_domain.append(var_obj.cur_domain())
            
        all_possible_tuples = []
        
        for cell_0 in cur_ith_domain[0]:
            cell_1_new_domain = compute_new_dom(cur_ith_domain[1], [cell_0]) #because new cell_1 domain cannot contain same value as cell_0 otherwise it wont satisfy the constraint
            for cell_1 in cell_1_new_domain:
                cell_2_new_domain = compute_new_dom(cur_ith_domain[2], [cell_0, cell_1])
                for cell_2 in cell_2_new_domain:
                    cell_3_new_domain = compute_new_dom(cur_ith_domain[3], [cell_0, cell_1, cell_2])
                    for cell_3 in cell_3_new_domain:
                        cell_4_new_domain = compute_new_dom(cur_ith_domain[4], [cell_0, cell_1, cell_2, cell_3])
                        for cell_4 in cell_4_new_domain:
                            cell_5_new_domain = compute_new_dom(cur_ith_domain[5], [cell_0, cell_1, cell_2, cell_3, cell_4])
                            for cell_5 in cell_5_new_domain:
                                cell_6_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5])
                                for cell_6 in cell_6_new_domain:
                                    cell_7_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5, cell_6])
                                    for cell_7 in cell_7_new_domain:
                                        cell_8_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5, cell_6, cell_7])
                                        for cell_8 in cell_8_new_domain:
                                            all_possible_tuples.append((cell_0,cell_1,cell_2,cell_3,cell_4,cell_5,cell_6,cell_7,cell_8))        
    
    
        
       
                
        constraint.add_satisfying_tuples(all_possible_tuples)
        sudoku_csp.add_constraint(constraint)
       # Constraints.append(constraint)
        
    #lets do row constraints 
    #doing row constraints
    for i in range(9):
        ith_row = Variables[i]
        constraint = Constraint("Cons row_" + str(i), ith_row)
        cur_ith_domain = []
        
        for var_obj in ith_row:
            cur_ith_domain.append(var_obj.cur_domain())
            
        all_possible_tuples = []
        
        for cell_0 in cur_ith_domain[0]:
            cell_1_new_domain = compute_new_dom(cur_ith_domain[1], [cell_0]) #because new cell_1 domain cannot contain same value as cell_0 otherwise it wont satisfy the constraint
            for cell_1 in cell_1_new_domain:
                cell_2_new_domain = compute_new_dom(cur_ith_domain[2], [cell_0, cell_1])
                for cell_2 in cell_2_new_domain:
                    cell_3_new_domain = compute_new_dom(cur_ith_domain[3], [cell_0, cell_1, cell_2])
                    for cell_3 in cell_3_new_domain:
                        cell_4_new_domain = compute_new_dom(cur_ith_domain[4], [cell_0, cell_1, cell_2, cell_3])
                        for cell_4 in cell_4_new_domain:
                            cell_5_new_domain = compute_new_dom(cur_ith_domain[5], [cell_0, cell_1, cell_2, cell_3, cell_4])
                            for cell_5 in cell_5_new_domain:
                                cell_6_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5])
                                for cell_6 in cell_6_new_domain:
                                    cell_7_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5, cell_6])
                                    for cell_7 in cell_7_new_domain:
                                        cell_8_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5, cell_6, cell_7])
                                        for cell_8 in cell_8_new_domain:
                                            all_possible_tuples.append((cell_0,cell_1,cell_2,cell_3,cell_4,cell_5,cell_6,cell_7,cell_8))
        
        constraint.add_satisfying_tuples(all_possible_tuples)
        sudoku_csp.add_constraint(constraint)
      #  Constraints.append(constraint)
    
    
    #column constraints
    for i in range(9):
        ith_column = []
        for rows in range(9):
            ith_column.append(Variables[rows][i])
        constraint = Constraint("Cons col_" + str(i), ith_column)
        cur_ith_domain = []
        
        for var_obj in ith_column:
            cur_ith_domain.append(var_obj.cur_domain())
            
        all_possible_tuples = []        
        
        for cell_0 in cur_ith_domain[0]:
            cell_1_new_domain = compute_new_dom(cur_ith_domain[1], [cell_0]) #because new cell_1 domain cannot contain same value as cell_0 otherwise it wont satisfy the constraint
            for cell_1 in cell_1_new_domain:
                cell_2_new_domain = compute_new_dom(cur_ith_domain[2], [cell_0, cell_1])
                for cell_2 in cell_2_new_domain:
                    cell_3_new_domain = compute_new_dom(cur_ith_domain[3], [cell_0, cell_1, cell_2])
                    for cell_3 in cell_3_new_domain:
                        cell_4_new_domain = compute_new_dom(cur_ith_domain[4], [cell_0, cell_1, cell_2, cell_3])
                        for cell_4 in cell_4_new_domain:
                            cell_5_new_domain = compute_new_dom(cur_ith_domain[5], [cell_0, cell_1, cell_2, cell_3, cell_4])
                            for cell_5 in cell_5_new_domain:
                                cell_6_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5])
                                for cell_6 in cell_6_new_domain:
                                    cell_7_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5, cell_6])
                                    for cell_7 in cell_7_new_domain:
                                        cell_8_new_domain = compute_new_dom(cur_ith_domain[6], [cell_0, cell_1, cell_2, cell_3, cell_4, cell_5, cell_6, cell_7])
                                        for cell_8 in cell_8_new_domain:
                                            all_possible_tuples.append((cell_0,cell_1,cell_2,cell_3,cell_4,cell_5,cell_6,cell_7,cell_8))     
        constraint.add_satisfying_tuples(all_possible_tuples)
        sudoku_csp.add_constraint(constraint)
       # Constraints.append(constraint)
    
   
    #for cons in Constraints:
        #sudoku_csp.add_constraint(cons)
    
    return sudoku_csp,Variables
       
        
    

#IMPLEMENT



    