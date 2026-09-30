"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """
    kb = PropKB()

    #1. Every cell has at least one value from {1, . . . , n}.
    for r in range(1, n + 1):         
        for c in range(1, n + 1):      
            options = [atom('Is', r, c, v) for v in range(1, n + 1)]
            kb.tell(associate('|', options))
    
    #2. Every cell has at most one value from {1, . . . , n}. (no cell holds two digits at once).
    for r in range(1,n + 1):
        for c in range(1, n + 1):
            for v1 in range(1, n + 1):
                for v2 in range(v1 + 1, n + 1):
                    kb.tell(~atom('Is', r, c, v1) | ~atom('Is', r, c, v2))

    #3. No two cells in the same row hold the same value.
    for r in range (1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(c1 + 1, n + 1):
                    kb.tell(~atom('Is', r, c1, v) | ~atom('Is', r, c2, v))

    #4. No two cells in the same column hold the same value.
    for c in range (1, n + 1):
                for v in range(1, n + 1):
                    for r1 in range(1, n + 1):
                        for r2 in range(r1 + 1, n + 1):
                            kb.tell(~atom('Is', r1, c, v) | ~atom('Is', r2, c, v))   

    # 5. No two cells in the same box share a value.
    for br in range(0, n, box_h):           
        for bc in range(0, n, box_w):
            cells = [(br + i, bc + j) for i in range(1, box_h + 1)
                                      for j in range(1, box_w + 1)]
            for v in range(1, n + 1):
                for a in range(len(cells)):
                    for b in range(a + 1, len(cells)):
                        (r1, c1), (r2, c2) = cells[a], cells[b]
                        kb.tell(~atom('Is', r1, c1, v) | ~atom('Is', r2, c2, v))

    # 6. Givens hold their stated values.
    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    return kb


class IndexedDefiniteKB(PropDefiniteKB):
    """PropDefiniteKB with a premise index, so pl_fc_entails doesn't rescan
    the whole KB every time it pops a symbol."""
    def __init__(self, sentence=None):
        self._index = defaultdict(list)
        super().__init__(sentence)

    def tell(self, sentence):
        super().tell(sentence)
        if sentence.op == '==>':
            for p in conjuncts(sentence.args[0]):
                self._index[p].append(sentence)

    def clauses_with_premise(self, p):
        return self._index.get(p, [])


def units_of(n, box_h, box_w, r, c):
    """The three groups (row, column, box) that cell (r, c) belongs to."""
    row = [(r, j) for j in range(1, n + 1)]
    col = [(i, c) for i in range(1, n + 1)]
    br = (r - 1) // box_h * box_h
    bc = (c - 1) // box_w * box_w
    box = [(br + i, bc + j) for i in range(1, box_h + 1) for j in range(1, box_w + 1)]
    return [row, col, box]


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """

    kb = IndexedDefiniteKB()             
    values = range(1, n + 1)              
    cells = [(r, c) for r in range(1, n + 1) for c in range(1, n + 1)]   

    # ── Condition 6: givens are facts ──
    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))                     

    for (r, c) in cells:
        units = units_of(n, box_h, box_w, r, c)           
        peers = {cell for unit in units for cell in unit} - {(r, c)}   
        for v in values:
            is_rcv = atom('Is', r, c, v)

            # ── Conditions 3, 4, 5: row / column / box uniqueness ──
            #    "If (r,c) is v, then no neighbour is v"
            for (pr, pc) in peers:
                kb.tell(Expr('==>', is_rcv, atom('Not', pr, pc, v)))      # Is1_1_5 ⇒ Not1_2_5

            # ── Condition 2: at most one value ──
            #    "If (r,c) is v, then (r,c) isn't any other value"
            for w in values:
                if w != v:
                    kb.tell(Expr('==>', is_rcv, atom('Not', r, c, w)))    # Is1_1_5 ⇒ Not1_1_1

            # ── Condition 1: at least one value (last candidate in the cell) ──
            #    "If every other value is ruled out, then it's v"
            others = [atom('Not', r, c, w) for w in values if w != v]
            kb.tell(Expr('==>', associate('&', others), is_rcv))
            #    Not1_1_1 ∧ Not1_1_2 ∧ … ∧ Not1_1_9 (all but 5)  ⇒  Is1_1_5

            # ── Condition 1 (+3/4/5): hidden single ──
            #    "If v is ruled out of every OTHER cell in this row/col/box, it must be here"
            for unit in units:
                others = [atom('Not', ur, uc, v) for (ur, uc) in unit if (ur, uc) != (r, c)]
                kb.tell(Expr('==>', associate('&', others), is_rcv))
                #    Not1_2_5 ∧ Not1_3_5 ∧ … ∧ Not1_9_5  ⇒  Is1_1_5

    return kb

def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    grid = {}
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                if pl_fc_entails(kb, atom('Is', r, c, v)):
                    grid[(r, c)] = v
                    break
    return grid
    
    
    


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
     # --- Setup: facts, and "which rules conclude X?" ---
    facts = {cl for cl in kb.clauses if is_prop_symbol(cl.op)}
    rules_for = defaultdict(list)
    for cl in kb.clauses:
        if cl.op == '==>':
            rules_for[cl.args[1]].append(conjuncts(cl.args[0]))

    proven = set(facts)          # everything known to be true so far

    def search(goal):
        """One depth-first backward-chaining pass. Returns True/False."""
        if goal in proven:
            return True
        failed = set()           # goals that already failed in this pass
        on_path = {goal}         # goals currently being worked on (cycle check)
        stack = [[goal, 0, 0]]   # each frame: [goal, which rule, which premise]
        result = None            # answer coming back from the frame just finished

        while stack:
            frame = stack[-1]
            g, ri, pi = frame
            rules = rules_for[g]

            # A sub-goal just finished: use its answer
            if result is not None:
                if result:
                    frame[2] += 1            # premise proved -> next premise
                else:
                    frame[1] += 1            # premise failed -> try next rule
                    frame[2] = 0
                result = None
                continue

            # No rules left for g -> g fails
            if ri >= len(rules):
                on_path.discard(g)
                failed.add(g)
                stack.pop()
                result = False
                continue

            premises = rules[ri]

            # Every premise of this rule proved -> g is proved
            if pi >= len(premises):
                on_path.discard(g)
                proven.add(g)
                stack.pop()
                result = True
                continue

            # Look at the next premise p
            p = premises[pi]
            if p in proven:
                frame[2] += 1                # already true -> next premise
            elif p in on_path or p in failed:
                frame[1] += 1                # loop or known failure -> next rule
                frame[2] = 0
            else:
                on_path.add(p)
                stack.append([p, 0, 0])      # try to prove p (go deeper)

        return result

    # Repeat passes until the query is proved or nothing new was learned
    while True:
        before = len(proven)
        if search(query):
            return True
        if len(proven) == before:
            return False


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    grid = {}
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                if pl_bc_entails(kb, atom('Is', r, c, v)):
                    grid[(r, c)] = v
                    break
    return grid
