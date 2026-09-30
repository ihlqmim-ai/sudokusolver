import json
import time
import streamlit as st
from utils import *
from logic_ import *
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails,
)

st.title('Sudoku Solver')

with open('puzzles.json') as f:
    pool = json.load(f)

# --- 1. Puzzle selection & visual board display ---
# TODO: a dropdown/selectbox to pick a puzzle by index from pool['puzzles'].
# TODO: render the grid (e.g. a table or grid of st.columns), showing given
# cells and empty cells differently (e.g. bold givens, blank otherwise).



# --- 2. Full-grid auto-solver, with algorithm selection ---
# TODO: a radio/selectbox letting the user choose forward chaining
# (solve_full_grid_fc) or backward chaining (solve_full_grid_bc).
# TODO: a button that times and calls the chosen solver on
# (n, box_h, box_w, givens), then displays the solved grid and the elapsed
# time.

# --- 3. Targeted cell entailment query ---
# TODO: number inputs for row (r), column (c), value (v).
# TODO: a button that builds the definite KB, calls
# pl_bc_entails(kb, atom('Is', r, c, v)), and displays True/False.

# --- 4. Reasoning trace ("tutor mode") ---
# TODO: instrument your forward- or backward-chaining approach to record each
# reasoning step (which rule fired, on what premises, producing what
# conclusion) as it answers the query above.
# TODO: render that trace as human-readable output -- e.g. a sequence of
# st.expander(...) blocks, one per step, each with a plain-English sentence
# -- not a raw list/dict dump.
#
# Keep the core solver functions in sudoku_solver.py; do not duplicate them here.

def parse_puzzle(p):
    """Turn the JSON "r_c" keys into (r, c) tuples."""
    givens = {tuple(int(x) for x in k.split('_')): v for k, v in p['givens'].items()}
    solution = {tuple(int(x) for x in k.split('_')): v for k, v in p['solution'].items()}
    return {'givens': givens, 'solution': solution, 'given_count': p['given_count']}
 
 
@st.cache_resource
def get_definite_kb(puzzle_index):
    """Build the definite KB once per puzzle and reuse it."""
    return build_definite_kb(n, box_h, box_w, puzzles[puzzle_index]['givens'])
 
 
def board_html(grid, givens, highlight=None, query=None):
    """Draw the grid as an HTML table.
    Givens: bold black on grey. Deduced values: blue. Highlighted cell: yellow."""
    html = ['<table style="border-collapse:collapse;margin:4px 0 12px 0;">']
    for r in range(1, n + 1):
        html.append('<tr>')
        for c in range(1, n + 1):
            top = '3px' if (r - 1) % box_h == 0 else '1px'
            left = '3px' if (c - 1) % box_w == 0 else '1px'
            bottom = '3px' if r == n else '1px'
            right = '3px' if c == n else '1px'
            value = grid.get((r, c), '')
            if (r, c) in givens:
                bg, color, weight = '#e6e6e6', '#111111', '700'
            else:
                bg, color, weight = '#ffffff', '#1f5fbf', '500'
            if highlight == (r, c):
                bg = '#ffe066'
            if query == (r, c):
                bg = '#ffd6d6'
            html.append(
                f'<td style="width:38px;height:38px;text-align:center;'
                f'font-size:20px;font-family:monospace;font-weight:{weight};'
                f'color:{color};background:{bg};border-style:solid;border-color:#333;'
                f'border-width:{top} {right} {bottom} {left};">{value}</td>')
        html.append('</tr>')
    html.append('</table>')
    return ''.join(html)
 
 
def show_board(grid, givens, **kwargs):
    st.markdown(board_html(grid, givens, **kwargs), unsafe_allow_html=True)
 
 
# ---------------------------------------------------------------------------
# Reasoning trace: an instrumented copy of forward chaining that records WHY
# each symbol was inferred (which rule fired). Used only for explanations.
# ---------------------------------------------------------------------------
 
def parse(sym):
    """'Is3_2_4' -> ('Is', 3, 2, 4)"""
    name = str(sym)
    kind = 'Is' if name.startswith('Is') else 'Not'
    r, c, v = name[len(kind):].split('_')
    return kind, int(r), int(c), int(v)
 
 
@st.cache_resource
def traced_forward_chaining(puzzle_index):
    """Run forward chaining to a fixpoint and record, for every inferred
    symbol, the rule that first produced it, plus the order in which new
    cell values (Is symbols) were deduced."""
    kb = get_definite_kb(puzzle_index)
    count = {cl: len(conjuncts(cl.args[0])) for cl in kb.clauses if cl.op == '==>'}
    cause = {}                      # symbol -> rule that produced it (None = given)
    inferred = set()
    agenda = []
    for cl in kb.clauses:
        if is_prop_symbol(cl.op):
            cause[cl] = None
            agenda.append(cl)
    deduced_order = []              # Is symbols in the order they were deduced
    front = 0                       # agenda is used as a first-in-first-out queue
    while front < len(agenda):
        p = agenda[front]
        front += 1
        if p in inferred:
            continue
        inferred.add(p)
        if cause[p] is not None and parse(p)[0] == 'Is':
            deduced_order.append(p)
        for cl in kb.clauses_with_premise(p):
            count[cl] -= 1
            if count[cl] == 0:
                q = cl.args[1]
                if q not in cause:
                    cause[q] = cl
                agenda.append(q)
    return deduced_order, cause, inferred
 
 
def explain_not(sym, cause):
    """Plain-English reason for a Not symbol."""
    _, r, c, v = parse(sym)
    source = cause[sym].args[0]                 # the single Is premise
    _, r2, c2, v2 = parse(source)
    if (r2, c2) == (r, c):
        return f'{v} is ruled out because cell ({r},{c}) already holds {v2}'
    if r2 == r:
        return f'{v} is ruled out because row {r} already has {v} at ({r2},{c2})'
    if c2 == c:
        return f'{v} is ruled out because column {c} already has {v} at ({r2},{c2})'
    return f'{v} is ruled out because its box already has {v} at ({r2},{c2})'
 
 
def explain_is(sym, cause):
    """Headline + list of supporting reasons for a deduced Is symbol."""
    _, r, c, v = parse(sym)
    rule = cause[sym]
    if rule is None:
        return f'({r},{c}) = {v} is a given.', []
    premises = [parse(p) for p in conjuncts(rule.args[0])]
    if all((pr, pc) == (r, c) for _, pr, pc, _ in premises):
        headline = (f'({r},{c}) = {v}: last remaining candidate. '
                    f'Every other value was ruled out for this cell.')
        reasons = [explain_not(atom('Not', r, c, w), cause) for *_, w in premises]
    else:
        cells = [(pr, pc) for _, pr, pc, _ in premises]
        if all(pr == r for pr, _ in cells):
            unit = f'row {r}'
        elif all(pc == c for _, pc in cells):
            unit = f'column {c}'
        else:
            unit = 'its box'
        headline = (f'({r},{c}) = {v}: hidden single. {v} cannot go anywhere '
                    f'else in {unit}, so it must go here.')
        reasons = [f'({pr},{pc}): ' + explain_not(atom('Not', pr, pc, v), cause)
                   for pr, pc in cells]
    return headline, reasons
 
 
def reasoning_chain(target, cause, order):
    """All deduced cell values (Is symbols) that the target depends on,
    in the order forward chaining deduced them."""
    needed, stack, seen = set(), [target], {target}
    while stack:
        s = stack.pop()
        rule = cause.get(s)
        if rule is None:            # a given (or never derived)
            continue
        if parse(s)[0] == 'Is':
            needed.add(s)
        for p in conjuncts(rule.args[0]):
            if p not in seen:
                seen.add(p)
                stack.append(p)
    position = {sym: i for i, sym in enumerate(order)}
    return sorted(needed, key=lambda s: position[s])
 
 
# ---------------------------------------------------------------------------
# Page
# ---------------------------------------------------------------------------
 
with open('puzzles.json') as f:
    pool = json.load(f)
n, box_h, box_w = pool['n'], pool['box_h'], pool['box_w']
puzzles = [parse_puzzle(p) for p in pool['puzzles']]
 
st.title('Sudoku Solver')
st.caption('Knowledge base of definite clauses, solved with forward and backward chaining.')
 
# --- 1. Puzzle selection & visual board display ---
st.header('1. Choose a puzzle')
labels = [f'Puzzle {i + 1} ({p["given_count"]} givens)' for i, p in enumerate(puzzles)]
idx = st.selectbox('Puzzle', range(len(puzzles)), format_func=lambda i: labels[i])
puzzle = puzzles[idx]
givens = puzzle['givens']
st.markdown('Grey bold cells are **givens**; blank cells are to be solved.')
show_board(givens, givens)
 
# --- 2. Full-grid auto-solver, with algorithm selection ---
st.header('2. Solve the full grid')
method = st.radio('Inference algorithm',
                  ['Forward chaining (solve_full_grid_fc)',
                   'Backward chaining (solve_full_grid_bc)'],
                  horizontal=True)
if 'results' not in st.session_state:
    st.session_state.results = {}
 
if st.button('Solve'):
    solver = solve_full_grid_fc if method.startswith('Forward') else solve_full_grid_bc
    with st.spinner('Solving... (this can take 10-30 seconds)'):
        t0 = time.perf_counter()
        solved = solver(n, box_h, box_w, givens)
        elapsed = time.perf_counter() - t0
    st.session_state.results[(idx, method)] = (solved, elapsed)
 
if (idx, method) in st.session_state.results:
    solved, elapsed = st.session_state.results[(idx, method)]
    col1, col2 = st.columns([2, 1])
    with col1:
        show_board(solved, givens)
    with col2:
        st.metric('Solve time', f'{elapsed:.2f} s')
        if solved == puzzle['solution']:
            st.success('Matches the known solution.')
        else:
            st.warning(f'Solved {len(solved)} of {n * n} cells.')
    # Show both timings side by side once both have been run
    other = [m for (i, m) in st.session_state.results if i == idx and m != method]
    if other:
        st.caption(f'Other method on this puzzle ({other[0].split(" (")[0]}): '
                   f'{st.session_state.results[(idx, other[0])][1]:.2f} s')
 
# --- 3. Targeted cell entailment query ---
st.header('3. Ask about one cell')
q1, q2, q3 = st.columns(3)
r = q1.number_input('Row (r)', min_value=1, max_value=n, value=1)
c = q2.number_input('Column (c)', min_value=1, max_value=n, value=1)
v = q3.number_input('Value (v)', min_value=1, max_value=n, value=1)
 
if st.button('Check entailment with backward chaining'):
    kb = get_definite_kb(idx)
    t0 = time.perf_counter()
    verdict = pl_bc_entails(kb, atom('Is', r, c, v))
    st.session_state.query = (idx, r, c, v, verdict, time.perf_counter() - t0)
 
if st.session_state.get('query') and st.session_state.query[0] == idx:
    _, qr, qc, qv, verdict, qtime = st.session_state.query
    if verdict:
        st.success(f'KB ⊨ Is{qr}_{qc}_{qv}: **True**. Cell ({qr},{qc}) is {qv}. '
                   f'({qtime:.3f} s)')
    else:
        st.error(f'KB ⊭ Is{qr}_{qc}_{qv}: **False**. Cell ({qr},{qc}) cannot be '
                 f'shown to be {qv}. ({qtime:.3f} s)')
 
 
# --- 4. Reasoning trace ("tutor mode") ---
st.header('4. Reasoning trace for the query')
st.markdown('Forward chaining is instrumented to record which rule fired, on which '
            'premises, for every fact it infers. Below is the chain of steps that '
            'leads to the answer for the cell you asked about.')
order, cause, inferred = traced_forward_chaining(idx)
 
if not (st.session_state.get('query') and st.session_state.query[0] == idx):
    st.info('Ask about a cell in section 3 to see its reasoning trace here.')
else:
    _, qr, qc, qv, verdict, _ = st.session_state.query
    is_sym, not_sym = atom('Is', qr, qc, qv), atom('Not', qr, qc, qv)
    if (qr, qc) in givens:
        target = is_sym if givens[(qr, qc)] == qv else not_sym
    else:
        target = is_sym if is_sym in inferred else not_sym
    if target not in inferred:
        st.info('Neither the value nor its elimination can be derived from the rules.')
    else:
        steps = reasoning_chain(target, cause, order)
        st.markdown(f'**{len(steps)} deduction step(s)** lead to this answer '
                    f'(givens are used directly).')
        for i, sym in enumerate(steps, start=1):
            headline, reasons = explain_is(sym, cause)
            _, sr, sc, sv = parse(sym)
            with st.expander(f'Step {i}: ({sr},{sc}) = {sv}',
                             expanded=(sym == target)):
                st.markdown(headline)
                grid = dict(givens)
                for done in steps[:i]:
                    _, rr, cc, vv = parse(done)
                    grid[(rr, cc)] = vv
                show_board(grid, givens, highlight=(sr, sc))
                for reason in reasons:
                    st.markdown(f'- {reason}')
        if target == not_sym:
            st.error(f'Conclusion: ({qr},{qc}) cannot be {qv}. '
                     + explain_not(not_sym, cause) + '.')
        else:
            st.success(f'Conclusion: ({qr},{qc}) = {qv}.')
 
# --- Extra: replay the whole solve ---
st.header('Replay the whole solve')
if not order:
    st.info('No cells could be deduced.')
else:
    step = st.slider('Step', 1, len(order), 1)
    current = order[step - 1]
    _, sr, sc, sv = parse(current)
    grid = dict(givens)
    for sym in order[:step]:
        _, rr, cc, vv = parse(sym)
        grid[(rr, cc)] = vv
    left, right = st.columns([1, 1])
    with left:
        st.markdown(f'**Step {step} of {len(order)}**: new value at ({sr},{sc}), '
                    f'shown in yellow')
        show_board(grid, givens, highlight=(sr, sc))
    with right:
        headline, reasons = explain_is(current, cause)
        st.info(headline)
        with st.expander('Show the eliminations behind this step', expanded=True):
            for reason in reasons:
                st.markdown(f'- {reason}')