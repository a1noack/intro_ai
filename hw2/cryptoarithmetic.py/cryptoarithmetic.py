def get_constraints(minu, subt, diff):
    '''Create list of constraints based on user input.
    '''
    minu, subt, diff = map(list, [minu, subt, diff]) # convert strings into lists
    constraints = []
    for i in range(1,len(minu)):
#         constraints.append("C{} in [0,1]".format(i))
        if i > 1:
            constraints.append("c{} + {} + {} == {} + 10 * c{}".format(i-1, diff[-i], subt[-i], minu[-i], i))
        else:
            constraints.append("{} + {} == {} + 10 * c{}".format(diff[-i], subt[-i], minu[-i], i))
    constraints.append("c4 == {}".format(minu[0]))
    return constraints

def get_variables(minu, subt, diff):
    '''Create a dictionary in which the keys are the variables and the values represent the
    domains for each variable.
    '''
    variables = []
    for ch in minu+subt+diff:
        if ch not in variables:
            variables.append(ch)
    var_doms = dict((el,list(range(10))) for el in variables)
    for i in range(1,len(minu)):
        var_doms["c{}".format(i)] = [0,1]
    return var_doms

def no_leading_zero(minu, subt, diff, var_doms):
    '''Remove the domain value of zero from leading characters.
    '''
    l = set([minu[0], subt[0], diff[0]])
    for el in l:
        var_doms[el].remove(0)
    return var_doms

def final_carry(minu, var_doms):
    '''Create the constraint that the final carry value must equal 1.
    '''
    var_doms[minu[0]] = [1]
    var_doms['c4'] = [1]
    return var_doms

def initialize(minu, subt, diff):
    ''' Create constraints and remove all of the unnecessary domain values from the
    each variable's list of possible domain values.
    '''
    constraints = get_constraints(minu, subt, diff)
    var_doms = get_variables(minu, subt, diff)
    var_doms = no_leading_zero(minu, subt, diff, var_doms)
    var_doms = final_carry(minu, var_doms)
    return var_doms, constraints

def backtrack(asgns, var_doms, constraints):
    '''The actual backtrack search algorithm.
    '''
    global ctr, SOLUTION_NUM
    if DEFAULT_ASGN not in list(asgns.values()):
        print("Solution #{}".format(SOLUTION_NUM))
        print("Cumulative assignments: {}\nVariable assignments: {}\n".format(ctr, asgns))
        SOLUTION_NUM +=1
        return False
    # find first variable in asgns that hasn't yet been assigned a value without using heuristic
    # cur_var = [k for k, v in asgns.items() if v == DEFAULT_ASGN][0]
    vars_sorted = mrv(var_doms, asgns)
    cur_var = vars_sorted[0]

    options_sorted = list(map(int, lcv(cur_var, asgns, var_doms)))
    # test
    for cur_val in options_sorted:
        if not used(cur_var, cur_val, asgns) and is_consistent(cur_var, cur_val, asgns, constraints):
            asgns[cur_var] = cur_val
            ctr += 1
            # var_doms[cur_var] = []
            result = backtrack(asgns, var_doms, constraints)
            if result != False:
                return result
        asgns[cur_var] = DEFAULT_ASGN
    return False

def is_consistent(test_var, test_val, asgns, constraints):
    ''' For each of the variable names, replace every occurence of the variable in the list of
    constraints with the value that that variable was assigned to in the asgns dictionary.
    '''
    local_constraints = constraints.copy()
    for var in list(asgns.keys()):
        for i in range(len(local_constraints)):
            if var != test_var:
                # replace variable with value
                local_constraints[i] = local_constraints[i].replace(var, str(asgns[var]))
            else:
                local_constraints[i] = local_constraints[i].replace(var, str(test_val))
    # check to see if constraints fail to evaluate to True
    # print(local_constraints)
    for constraint in local_constraints:
        try:
            # test each constraint
            satisfied = eval(constraint)
            # print('constraint {} IS satisfied'.format(constraint))
        except NameError:
            satisfied = True
        # if any constraint fails, ie evaluates to False, return False
        if not satisfied:
            # print('constraint {} NOT satisfied'.format(constraint))
            return False
    return True

def used(cur_var, test_val, asgns):
    '''Returns True if all of the variable assignments are unique.
    '''
    if 'c' in cur_var:
        return False
    values = [v for k, v in asgns.items() if 'c' not in k and v != DEFAULT_ASGN]
    used = test_val in values
    return used

def lcv(cur_var, asgns, var_doms):
    '''Runs through each of the possible assignments for cur_var and returns a list of the
    variable's domain values ordered by the number of options the assignment would leave open for
    the variables that have yet to be assigned a value.
    '''
    global constraints, ctr
    valid_options = dict((str(el), 0) for el in var_doms[cur_var])
    for val in var_doms[cur_var]:
        if not used(cur_var, val, asgns) and is_consistent(cur_var, val, asgns, constraints):
            asgns[cur_var] = val
            rvs = rem_vals(var_doms, asgns)
            # if any of the unassigned variables have zero possible assignment options, don't try this value
            if 0 not in rvs.values():
                valid_options[str(val)] += sum(rvs.values())
            asgns[cur_var] = DEFAULT_ASGN
    return list(reversed(sorted(valid_options, key=valid_options.get)))

def count_occs(constraints, asgns):
    '''Count the number of times each variable occurs in the constraints.
    '''
    occs = dict((var, 0) for var in asgns.keys())
    for var in occs.keys():
        for c in constraints:
            occs[var] += c.count(var)
    return occs

def rem_vals(var_doms, asgns):
    # find variables that haven't yet been assigned a value
    rem_values = {}
    for k,v in asgns.items():
        if v == DEFAULT_ASGN:
            rem_values[k] = 0

    # test out each variable and track how many of its domain options are valid
    for var in rem_values.keys():
        for val in var_doms[var]:
            if not used(var, val, asgns) and is_consistent(var, val, asgns, constraints):
                rem_values[var] += 1

    # return the dictionary that has as keys the unassigned variables and values the number of valid assignments remaining
    return rem_values

def mrv(var_doms, asgns):
    '''This function encapsulates the Most Constrained Variable and Most Constraining Variable heuristics
    '''
    global constraints, occs
    # rem_values = dict((k,0) for k in var_doms.keys())
    rem_values = rem_vals(var_doms, asgns)

    v = list(rem_values.keys())

    #sort variables by how many times they occur in the constraints
    v.sort(key=lambda x: occs[x], reverse=True)

    #sort variables by how many valid assignments the unassigned variables have remaining
    v.sort(key=lambda x: rem_values[x])

    # return the key (the variable) from rem_values that has the least number of rem. values
    # return sorted(rem_values, key=rem_values.get)
    return v

if __name__ == '__main__':
    minu = input("Enter the minuend (5 letters): ").upper()
    subt = input("Enter the subtrahend (4 letters): ").upper()
    diff = input("Enter the difference (4 letters): ").upper()

    print("\n\n%s\n-%s\n------\n %s" % (minu, subt, diff))
    print("\n\nIMPLIES THAT...")
    print("\n\n %s\n+%s\n------\n%s\n\n" % (subt, diff, minu))

    DEFAULT_ASGN = 'na'
    SOLUTION_NUM = 1
    ctr = 0


    var_doms, constraints = initialize(minu, subt, diff)

    asgns = dict((el, DEFAULT_ASGN) for el in list(var_doms.keys()))

    asgns['c4'] = 1
    asgns[minu[0]] = 1

    var_doms['c4'] = []
    var_doms[minu[0]] = []

    occs = count_occs(constraints, asgns)

    print(occs)
    solution = backtrack(asgns, var_doms, constraints)
    if SOLUTION_NUM == 1:
        print('NO SOLUTIONS FOR THESE VARIABLES.')