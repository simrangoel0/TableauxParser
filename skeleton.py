MAX_CONSTANTS = 10

# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    # Check if the formula is a proposition (index 6)
    if fmla in ['p', 'q', 'r', 's']:
        return 6  # 'a proposition'

    # Check if the formula is an atom (index 1)
    if fmla.startswith(('P(', 'Q(', 'R(', 'S(')) and fmla.endswith(')') and ',' in fmla:
        args = fmla[2:-1].split(',')
        if len(args) == 2 and all(arg in ['x', 'y', 'z', 'w'] for arg in args):
            return 1  # 'an atom'

    # Check for negation
    if fmla.startswith('~'):
        subformula = fmla[1:]
        result = parse(subformula)
        if result in {6, 7, 8}:  
            return 7  # 'a negation of a propositional formula'
        elif result in {1, 2, 3, 4, 5}:  
            return 2  # 'a negation of a first order logic formula'
        else:
            return 0  # 'not a formula'

    # Check for quantifiers
    if len(fmla) > 1 and fmla[0] in {'E', 'A'} and fmla[1] in ['x', 'y', 'z', 'w']:
        subformula = fmla[2:]
        result = parse(subformula)
        if fmla[0] == 'E' and result in {1, 2, 3, 4, 5}: 
            return 4  # 'an existentially quantified formula'
        elif fmla[0] == 'A' and result in {1, 2, 3, 4, 5}: 
            return 3  # 'a universally quantified formula'
        else:
            return 0  # 'not a formula'

    # Check for binary connectives
    if fmla.startswith('(') and fmla.endswith(')'):
        inner = fmla[1:-1]
        depth = 0
        for i, char in enumerate(inner):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            # Look for connectives at the top level (depth == 0)
            elif depth == 0 and inner[i:i+2] in ['/\\', '\\/', '=>']:
                left = inner[:i].strip()
                connective = inner[i:i+2]
                right = inner[i+2:].strip()
                left_result = parse(left)
                right_result = parse(right)
                if left_result in {6, 7, 8} and right_result in {6, 7, 8}:
                    return 8  # 'a binary connective propositional formula'
                elif left_result in {1, 2, 3, 4, 5} and right_result in {1, 2, 3, 4, 5}:
                    return 5  # 'a binary connective first order formula'
                
    # If none of the conditions match...
    return 0  # 'not a formula'

    

# Return the LHS of a binary connective formula
def lhs(fmla):
    if fmla.startswith('(') and fmla.endswith(')'):
        depth = 0
        for i, char in enumerate(fmla):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            elif depth == 1:
                # Check for multi-character connectives
                if fmla[i:i+2] in ['/\\', '\\/'] or fmla[i:i+2] == '=>':
                    return fmla[1:i].strip()
    return ''

# Return the connective symbol of a binary connective formula
def con(fmla):
    if fmla.startswith('(') and fmla.endswith(')'):
        depth = 0
        for i, char in enumerate(fmla):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            elif depth == 1:
                # Check for multi-character connectives
                if fmla[i:i+2] in ['/\\', '\\/']:
                    return fmla[i:i+2]
                elif fmla[i:i+2] == '=>':
                    return '=>'
    return ''

# Return the RHS of a binary connective formula
def rhs(fmla):
    if fmla.startswith('(') and fmla.endswith(')'):
        depth = 0
        for i, char in enumerate(fmla):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            elif depth == 1:
                # Check for multi-character connectives
                if fmla[i:i+2] in ['/\\', '\\/'] or fmla[i:i+2] == '=>':
                    return fmla[i+2:-1].strip()
    return ''


# You may choose to represent a theory as a set or a list
def theory(fmla): #initialise a theory with a single formula in it
    return [fmla]

def sat(tableau):
    def is_literal(fmla):
        return parse(fmla) in [6, 7]

    def is_contradictory(branch):
        literals = set()
        for fmla in branch:
            if isinstance(fmla, str):  # Ensure we process only strings
                if fmla[0]=='~':
                    if fmla[1:] in literals:  # ~p and p
                        return True
                else:
                    if f"~{fmla}" in literals:  # p and ~p
                        return True
                literals.add(fmla)
        return False

    def expand_alpha(branch, formula):
        if con(formula) == "/\\":
            lhs_fmla = lhs(formula)
            rhs_fmla = rhs(formula)
            return branch + [lhs_fmla, rhs_fmla]
        elif formula.startswith("~") and formula[1:].startswith("("):
            subformula = formula[2:-1]
            if con(subformula) == "\\/":  # ~(A \/ B) => (~A /\ ~B)
                lhs_fmla = f"~{lhs(subformula)}"
                rhs_fmla = f"~{rhs(subformula)}"
                return branch + [lhs_fmla, rhs_fmla]
            elif con(subformula) == "=>":  # ~(A => B) => (A /\ ~B)
                lhs_fmla = lhs(subformula)
                rhs_fmla = f"~{rhs(subformula)}"
                return branch + [lhs_fmla, rhs_fmla]
        elif formula.startswith("~") and formula[1:].startswith("~"):  # ~~A => A
            return branch + [formula[2:]]
        return branch

    def expand_beta(branch, formula):
        if con(formula) == "\\/":
            lhs_fmla = lhs(formula)
            rhs_fmla = rhs(formula)
            return [branch + [lhs_fmla], branch + [rhs_fmla]]
        elif con(formula) == "=>":
            lhs_fmla = f"~{lhs(formula)}"
            rhs_fmla = rhs(formula)
            return [branch + [lhs_fmla], branch + [rhs_fmla]]
        return []

    # Initialize a list to manage branches
    branches = [tableau]  # Start with the initial tableau as a single branch

    while branches:
        # Get the current branch
        current_branch = branches.pop(0)

        # Check for contradictions
        if is_contradictory(current_branch):
            continue  # This branch is closed, skip to the next one

        # Check if the branch is fully expanded (only literals)
        if all(is_literal(fmla) for fmla in current_branch if isinstance(fmla, str)):
            return 1  # Satisfiable 

        # Expand the next non-literal formula in the branch
        for formula in current_branch:
            if isinstance(formula, str) and not is_literal(formula):  # Process strings only
                # Handle alpha expansions
                if con(formula) == "/\\" or (formula.startswith("~") and con(formula[1:]) in ["\\/", "=>"]):
                    expanded_branch = expand_alpha(current_branch, formula)
                    branches.append([f for f in expanded_branch if f != formula])
                # Handle beta expansions
                elif con(formula) in ["\\/", "=>"]:
                    new_branches = expand_beta(current_branch, formula)
                    for new_branch in new_branches:
                        branches.append([f for f in new_branch if f != formula])
                break  # Process one formula at a time

    return 0  # Unsatisfiable

#------------------------------------------------------------------------------------------------------------------------------:
#                   DO NOT MODIFY THE CODE BELOW. MODIFICATION OF THE CODE BELOW WILL RESULT IN A MARK OF 0!                   :
#------------------------------------------------------------------------------------------------------------------------------:

f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
